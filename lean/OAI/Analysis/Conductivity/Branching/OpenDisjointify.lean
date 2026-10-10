import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set MeasureTheory Metric
open scoped ENNReal Topology

def openDisjointify {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (i : Fin n) : Set E :=
  U i \ ⋃ j ∈ Finset.Iio i, closure (U j)

lemma openDisjointify_subset {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (i : Fin n) : openDisjointify U i ⊆ U i := sdiff_subset

lemma openDisjointify_isOpen {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) (i : Fin n) :
    IsOpen (openDisjointify U i) := by
  apply (hU i).sdiff
  exact isClosed_biUnion_finset (fun _ _ => isClosed_closure)

lemma openDisjointify_pairwise {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) : Pairwise (fun i j => Disjoint (openDisjointify U i) (openDisjointify U j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hxj.2 (mem_iUnion₂.mpr ⟨i, Finset.mem_Iio.mpr hij, subset_closure hxi.1⟩)
  · exact hxi.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_Iio.mpr hji, subset_closure hxj.1⟩)

lemma openDisjointify_cover {E : Type*} [TopologicalSpace E] {n : ℕ}
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) :
    (⋃ i, U i) \ (⋃ i, openDisjointify U i) ⊆ ⋃ i, frontier (U i) := by
  classical
  intro x hx
  by_contra hn
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx.1
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ U i)
  have hsn : s.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let i := s.min' hsn
  have hi : x ∈ U i := (Finset.mem_filter.mp (Finset.min'_mem s hsn)).2
  apply hx.2
  apply mem_iUnion.mpr
  refine ⟨i, hi, ?_⟩
  intro hc
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hc
  have hfront : x ∉ frontier (U j) := fun h => hn (mem_iUnion.mpr ⟨j, h⟩)
  have hin : x ∈ U j := by
    by_contra hnot
    apply hfront
    rw [frontier, (hU j).interior_eq]
    exact ⟨hxj, hnot⟩
  have hmin : i ≤ j := Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩)
  exact not_lt_of_ge hmin (Finset.mem_Iio.mp hj)

lemma openDisjointify_ae_cover {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) {n : ℕ} (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i))
    (hf : ∀ i, μ (frontier (U i)) = 0) :
    μ ((⋃ i, U i) \ ⋃ i, openDisjointify U i) = 0 := by
  exact measure_mono_null (openDisjointify_cover U hU) (measure_iUnion_null hf)

theorem finite_disjoint_localization
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {A : Set E} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i)) (hc : A ⊆ ⋃ i, U i)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (n : ℕ) (Q : Fin n → Set E) (tag : Fin n → I),
      (∀ i, IsOpen (Q i) ∧ IsCompact (closure (Q i)) ∧ closure (Q i) ⊆ U (tag i)) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧ μ (A \ ⋃ i, Q i) < ε := by
  classical
  obtain ⟨K, hKA, hK, hKμ⟩ := hA.exists_isCompact_sdiff_lt hμA hε
  have hb : ∀ x : K, ∃ i : I, ∃ r : ℝ, 0 < r ∧ closedBall x.val r ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hc (hKA x.property))
    obtain ⟨r, hr, hri⟩ := Metric.isOpen_iff.mp (hU i) x.val hi
    refine ⟨i, r/2, by positivity, ?_⟩
    intro y hy
    exact hri (show dist y x.val < r from (mem_closedBall.mp hy).trans_lt (by linarith))
  choose tag r hr hri using hb
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x.val (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, mem_ball_self (hr ⟨x,hx⟩)⟩)
  let T := {x : K // x ∈ t}
  let n := Fintype.card T
  let e : Fin n ≃ T := (Fintype.equivFin T).symm
  let B : Fin n → Set E := fun i => Metric.ball (e i).val.val (r (e i).val)
  have hKB : K ⊆ ⋃ i, B i := by
    intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    let z : T := ⟨y, hyt⟩
    exact mem_iUnion.mpr ⟨e.symm z, by simpa only [B, Equiv.apply_symm_apply] using hxy⟩
  have hBo : ∀ i, IsOpen (B i) := fun _ => isOpen_ball
  have hBf : ∀ i, μ (frontier (B i)) = 0 := by
    intro i
    exact measure_mono_null frontier_ball_subset_sphere (Measure.addHaar_sphere μ _ _)
  refine ⟨n, openDisjointify B, fun i => tag (e i).val, ?_, openDisjointify_pairwise B, ?_⟩
  · intro i
    have hcl : closure (openDisjointify B i) ⊆ closedBall (e i).val.val (r (e i).val) :=
      (closure_mono (openDisjointify_subset B i)).trans closure_ball_subset_closedBall
    exact ⟨openDisjointify_isOpen B hBo i,
      (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl, hcl.trans (hri (e i).val)⟩
  · have hsub : A \ (⋃ i, openDisjointify B i) ⊆
        (A \ K) ∪ ((⋃ i, B i) \ ⋃ i, openDisjointify B i) := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inr ⟨hKB hxK, hx.2⟩
      · exact Or.inl ⟨hx.1, hxK⟩
    calc
      μ (A \ ⋃ i, openDisjointify B i) ≤
          μ (A \ K) + μ ((⋃ i, B i) \ ⋃ i, openDisjointify B i) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ = μ (A \ K) := by rw [openDisjointify_ae_cover μ B hBo hBf, add_zero]
      _ < ε := hKμ

end ScalarConductivity

end

end OAI
