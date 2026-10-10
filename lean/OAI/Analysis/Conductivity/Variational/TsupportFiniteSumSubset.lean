import Mathlib
import OAI.Analysis.Conductivity.Flux.PiolaFluxAdd

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
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma tsupport_finite_sum_subset {X V I : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Fintype I] (f : I → X → V) :
    tsupport (fun x => ∑ i, f i x) ⊆ ⋃ i, tsupport (f i) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => isClosed_tsupport (f i)))
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))

lemma supported_sum_eq_on {X V I : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Fintype I] [DecidableEq I] (O : I → Set X)
    (hd : Pairwise (fun i j => Disjoint (O i) (O j))) (f : I → X → V)
    (hs : ∀ i, tsupport (f i) ⊆ O i) (i : I) :
    EqOn (fun x => ∑ j, f j x) (f i) (O i) := by
  intro x hx
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact image_eq_zero_of_notMem_tsupport
      (fun hj => Set.disjoint_left.mp (hd hji) (hs j hj) hx)
  · simp

lemma supported_sum_eq_zero_off {X V I : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Fintype I] (O : I → Set X) (f : I → X → V) (hs : ∀ i, tsupport (f i) ⊆ O i)
    {x : X} (hx : x ∉ ⋃ i, O i) : (∑ i, f i x) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hi => hx (mem_iUnion.mpr ⟨i, hs i hi⟩))

lemma finite_sum_cauchy_preserving
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] {I : Type*} [Fintype I]
    (F : I → Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
    (hF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i))
    (hc : ∀ i, HasCompactSupport (F i))
    (hpair : ∀ i j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x ((F i x).col j) ∂μ) = 0) :
    ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x ((∑ i, F i x).col j) ∂μ) = 0 := by
  intro j ψ hψ
  have he (x : Coord3) : fderiv ℝ ψ x ((∑ i, F i x).col j) =
      ∑ i, fderiv ℝ ψ x ((F i x).col j) := by
    rw [← map_sum]
    congr 1
    ext k
    simp only [col, transpose_apply, Matrix.sum_apply, Finset.sum_apply]
  simp_rw [he]
  rw [integral_finsetSum]
  · simp only [hpair _ j ψ hψ, Finset.sum_const_zero]
  · intro i _
    apply smooth_flux_integrable_pairing μ _ _ _ ψ hψ
    · apply continuous_pi; intro k
      exact continuous_apply j |>.comp (continuous_apply k |>.comp (hF i).continuous)
    · apply (hc i).mono
      intro x hx hn
      apply hx
      change (F i x).col j = 0
      rw [hn]; rfl

theorem assemble_compact_replacements
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (R : ∀ i, CompactTwoFieldReplacement μ (O i) u A) :
    ∃ (du : Coord3 → Fin 2 → ℝ) (dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) du ∧ HasCompactSupport du ∧ tsupport du ⊆ ⋃ i, O i ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) dF ∧ HasCompactSupport dF ∧ tsupport dF ⊆ ⋃ i, O i ∧
      (∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0) ∧
      (∀ i, EqOn du (R i).du (O i) ∧ EqOn dF (R i).dF (O i) ∧
        ∀ x ∈ O i,
          fderiv ℝ (fun y => u y+du y) x = fderiv ℝ (fun y => u y+(R i).du y) x) ∧
      (∀ x ∉ ⋃ i, O i, du x = 0 ∧ dF x = 0) := by
  let du : Coord3 → Fin 2 → ℝ := fun x => ∑ i, (R i).du x
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => ∑ i, (R i).dF x
  have heu : ∀ i, EqOn du (R i).du (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).du) (fun i => (R i).support_du)
  have heF : ∀ i, EqOn dF (R i).dF (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).dF) (fun i => (R i).support_dF)
  have hcdu : HasCompactSupport du := by
    simpa only [du, ← Finset.sum_apply] using
      (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_du))
  have hcdF : HasCompactSupport dF := by
    simpa only [dF, ← Finset.sum_apply] using
      (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_dF))
  refine ⟨du, dF, ContDiff.sum (fun i _ => (R i).smooth_du),
    hcdu,
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_du)),
    ContDiff.sum (fun i _ => (R i).smooth_dF),
    hcdF,
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_dF)), ?_, ?_, ?_⟩
  · exact finite_sum_cauchy_preserving μ (fun i => (R i).dF)
      (fun i => (R i).smooth_dF) (fun i => (R i).compact_dF) (fun i => (R i).cauchy_dF)
  · intro i
    refine ⟨heu i, heF i, ?_⟩
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hO i).mem_nhds hx] with y hy
    rw [heu i hy]
  · intro x hx
    exact ⟨supported_sum_eq_zero_off O _ (fun i => (R i).support_du) hx,
      supported_sum_eq_zero_off O _ (fun i => (R i).support_dF) hx⟩

end ScalarConductivity

end

end OAI
