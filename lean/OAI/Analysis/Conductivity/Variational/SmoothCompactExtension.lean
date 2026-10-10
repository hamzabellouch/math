import Mathlib
import OAI.Analysis.Conductivity.Branching.OpenDisjointify
import OAI.Analysis.Conductivity.Flux.PiolaFluxContDiff

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
open Set MeasureTheory Filter Topology
open scoped Manifold

lemma exists_smooth_compact_extension
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U K : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (f : E → V)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞)) f U) :
    ∃ (g : E → V) (W : Set E), ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
      HasCompactSupport g ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ EqOn g f W := by
  obtain ⟨χ, hχ₀, hχ₁, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK.isClosed
      (disjoint_left.mpr (fun x hx hxK => hx (hKU hxK))) (n := ⊤)
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  let g : E → V := fun x => χ x • f x
  have hzero (x : E) (hx : x ∉ U) : g =ᶠ[𝓝 x] (fun _ => 0) := by
    have hh : ∀ᶠ z in 𝓝 x, χ z = 0 := hχ₀.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hh] with z hz
    simp [g, hz]
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
  have hs : tsupport g ⊆ U := by
    intro x hx
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hzero x hn)) hx
  let W : Set E := U ∩ interior {x | χ x = 1}
  refine ⟨g, W, hg, hUb.isCompact_closure.of_isClosed_subset isClosed_closure
    (hs.trans subset_closure), hU.inter isOpen_interior, ?_, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hKU hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hχ₁.filter_mono (nhds_le_nhdsSet hx)
  · intro x hx
    have hone : χ x = 1 := (interior_subset (s := {x | χ x = 1})) hx.2
    simp [g, hone]

lemma derivative_test_integral_congr
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace E]
    (μ : Measure E) (ψ : E → V) (F G : E → E) (hFG : EqOn F G (tsupport ψ)) :
    (∫ x, fderiv ℝ ψ x (F x) ∂μ) = ∫ x, fderiv ℝ ψ x (G x) ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport ψ
    · change fderiv ℝ ψ x (F x) = fderiv ℝ ψ x (G x)
      rw [hFG hx]
    · simp only [fderiv_of_notMem_tsupport ℝ hx, _root_.zero_apply]

theorem local_compact_piola_Cauchy_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U)
    (hdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y F x - F x) ∧
    HasCompactSupport (fun x => piolaFlux Y F x - F x) ∧
    tsupport (fun x => piolaFlux Y F x - F x) ⊆ K ∧
    ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (piolaFlux Y F x - F x) ∂μ) = 0 := by
  obtain ⟨G, W, hG, hcG, _, hKW, hWU, he⟩ :=
    exists_smooth_compact_extension hU hUb hK hKU F hF
  have hdivG : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → (∫ x, fderiv ℝ ψ x (G x) ∂μ) = 0 := by
    intro ψ hψ hc hs
    rw [derivative_test_integral_congr μ ψ G F (he.mono hs)]
    exact hdiv ψ hψ hc (hs.trans hWU)
  have hp := compact_piola_Cauchy_difference μ Y hY hi hK hKW hoff G hG hcG hdivG
  have hsame : (fun x => piolaFlux Y F x - F x) = (fun x => piolaFlux Y G x - G x) := by
    funext x
    by_cases hx : x ∈ K
    · have hix : Y.symm x ∈ K := by
        by_contra hn
        have hz := hoff (Y.symm x) hn
        rw [Y.apply_symm_apply] at hz
        exact hn (hz ▸ hx)
      dsimp only [piolaFlux]
      rw [he (hKW hx), he (hKW hix)]
    · rw [piolaFlux_eq_off Y hK.isClosed hoff F hx,
        piolaFlux_eq_off Y hK.isClosed hoff G hx, sub_self, sub_self]
  refine ⟨hsame ▸ hp.1, hsame ▸ hp.2.1, hsame ▸ hp.2.2.1, ?_⟩
  intro ψ hψ
  have hh := hp.2.2.2 ψ hψ
  simpa only [congrFun hsame] using hh

end ScalarConductivity

namespace ScalarConductivity
open Set MeasureTheory Metric
open scoped ENNReal Topology

lemma null_frontier_union {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) {s t : Set E} (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∪ t)) = 0 := by
  apply measure_mono_null ((frontier_union_subset s t).trans ?_) (measure_union_null hs ht)
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx.1
  · exact Or.inr hx.2

lemma null_frontier_biUnion_finset {E I : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) (s : Finset I) (U : I → Set E) (hU : ∀ i ∈ s, μ (frontier (U i)) = 0) :
    μ (frontier (⋃ i ∈ s, U i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact null_frontier_union μ (hU i (Finset.mem_insert_self _ _))
        (ih fun j hj => hU j (Finset.mem_insert_of_mem hj))

lemma openDisjointify_null_frontier {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) {n : ℕ} (U : Fin n → Set E)
    (hf : ∀ i, μ (frontier (U i)) = 0) (i : Fin n) :
    μ (frontier (openDisjointify U i)) = 0 := by
  unfold openDisjointify
  rw [sdiff_eq]
  apply null_frontier_inter (hf i)
  rw [frontier_compl]
  apply null_frontier_biUnion_finset
  intro j _
  exact measure_mono_null frontier_closure_subset (hf j)

theorem finite_disjoint_localization_null
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {A : Set E} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i)) (hc : A ⊆ ⋃ i, U i)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (n : ℕ) (Q : Fin n → Set E) (tag : Fin n → I),
      (∀ i, IsOpen (Q i) ∧ IsCompact (closure (Q i)) ∧ closure (Q i) ⊆ U (tag i) ∧ μ (frontier (Q i)) = 0) ∧
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
      (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl, hcl.trans (hri (e i).val),
      openDisjointify_null_frontier μ B hBf i⟩
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
