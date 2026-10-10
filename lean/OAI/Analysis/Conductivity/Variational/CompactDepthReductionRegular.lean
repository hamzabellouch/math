import Mathlib
import OAI.Analysis.Conductivity.Variational.TsupportFiniteSumSubset
import OAI.Analysis.Conductivity.Variational.Unchanged

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

theorem exists_compact_depth_reduction_regular
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hr : TwoFieldRankRegular u U)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hsc : (spectralExtension (depthClass T n)).Nonempty) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactCompatibleReplacement μ O u A,
        TwoFieldRankRegular (fun x => u x+R.du x) O ∧
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  classical
  by_cases hn : A p ∈ spectralExtension (depthClass T n)
  · have hTo := isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)
    have hAc : ContinuousAt A p := Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hA.continuousOn.continuousAt (hU.mem_nhds hpU))
    have hev : ∀ᶠ x in 𝓝 p, x ∈ U ∧ A x ∈ spectralExtension (depthClass T n) :=
      Filter.Eventually.and (hU.mem_nhds hpU) (hAc.preimage_mem_nhds (hTo.mem_nhds hn))
    obtain ⟨V, hVs, hV, hpV⟩ := mem_nhds_iff.mp hev
    obtain ⟨W, hW, hpW, hWV, hWc⟩ := exists_precompact_open_inside hV hpV
    have hVU : V ⊆ U := fun x hx => (hVs hx).1
    refine ⟨W, hW, hpW, hWV.trans hVU, hWc, ?_⟩
    intro O hO hOW ε _
    have hOV := hOW.trans (subset_closure.trans hWV)
    have hOU := hOV.trans hVU
    let R := CompactCompatibleReplacement.unchanged μ O u A (hA.mono hOU)
    refine ⟨R, ?_, fun x hx => spectral_depth_subset hsub n (hVs (hOV hx)).2, ?_⟩
    · simpa only [R, CompactCompatibleReplacement.unchanged, Pi.zero_apply, add_zero] using hr.mono hOU
    · have he : {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
        intro hx
        exact (hVs (hOV hx)).2
      rw [he, measure_empty]
      exact bot_le
  · exact exists_compact_depth_reduction_regular_nontrivial μ u A hU hUb hu hA hdiv hr
      ha hT hsub hperm hpU hp hn hsc

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem assemble_compatible_replacements
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (R : ∀ i, CompactCompatibleReplacement μ (O i) u A) :
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
