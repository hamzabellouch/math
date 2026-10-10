import Mathlib
import OAI.Analysis.AffineBernstein.CompactIntegration

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

def flatTestContraction (A : ι → ι → E → ℝ) (e : ι → E) (η : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j, A i j x * dirDeriv (e i) (dirDeriv (e j) η) x

def flatDoubleDivergence (A : ι → ι → E → ℝ) (e : ι → E) (x : E) : ℝ :=
  ∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) (A i j)) x

lemma integrable_flatTestContraction (A : ι → ι → E → ℝ) (e : ι → E)
    {η : E → ℝ} (ha : ∀ i j x, x ∈ tsupport η → ContDiffAt ℝ ∞ (A i j) x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    Integrable (flatTestContraction A e η) μ := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_of_support_subset_compact hc.isCompact
  · exact (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (e i)).trans
        (tsupport_fderiv_apply_subset ℝ (e j))))
  · exact (show ContinuousOn (A i j) (tsupport η) from
      fun x hx => (ha i j x hx).continuousAt.continuousWithinAt).mul
      ((contDiff_dirDeriv (contDiff_dirDeriv hη (e j)) (e i)).continuous.continuousOn)

omit [MeasurableSpace E] [BorelSpace E] in
lemma contDiffAt_flatDoubleDivergence {A : ι → ι → E → ℝ} (e : ι → E) {x : E}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (A i j) x) :
    ContDiffAt ℝ ∞ (flatDoubleDivergence A e) x := by
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_dirDeriv (contDiffAt_dirDeriv (ha i j) (e i)) (e j)

lemma integrable_flatDoubleDivergence_mul (A : ι → ι → E → ℝ) (e : ι → E)
    {η : E → ℝ} (ha : ∀ i j x, x ∈ tsupport η → ContDiffAt ℝ ∞ (A i j) x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    Integrable (fun x => flatDoubleDivergence A e x * η x) μ := by
  apply integrable_of_support_subset_compact hc.isCompact
  · exact (Function.support_mul_subset_right _ _).trans (subset_tsupport η)
  · exact (show ContinuousOn (flatDoubleDivergence A e) (tsupport η) from
      fun x hx => (contDiffAt_flatDoubleDivergence e (fun i j => ha i j x hx)).continuousAt.continuousWithinAt).mul
      hη.continuous.continuousOn

omit [MeasurableSpace E] [BorelSpace E] in
lemma flatTestContraction_eq_zero_of_notMem_tsupport (A : ι → ι → E → ℝ)
    (e : ι → E) {η : E → ℝ} {x : E} (hx : x ∉ tsupport η) :
    flatTestContraction A e η x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hz : dirDeriv (e i) (dirDeriv (e j) η) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hh => hx ((tsupport_fderiv_apply_subset ℝ (e j))
      ((tsupport_fderiv_apply_subset ℝ (e i)) hh))
  rw [hz,mul_zero]

variable [FiniteDimensional ℝ E]

/- The fundamental variational lemma applied to two independent flat Hessian
blocks. No pointwise PDE is an assumption. -/
theorem flatDoubleDivergence_eq_zero_of_stationary {W : Set E} (hW : IsOpen W)
    (A : ι → ι → E → ℝ) (B : κ → κ → E → ℝ) (e : ι → E) (f : κ → E)
    (ha : ∀ i j x, x ∈ W → ContDiffAt ℝ ∞ (A i j) x)
    (hb : ∀ i j x, x ∈ W → ContDiffAt ℝ ∞ (B i j) x)
    (hstat : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ W →
      (∫ x, flatTestContraction A e η x + flatTestContraction B f η x ∂μ) = 0)
    {x : E} (hx : x ∈ W) :
    flatDoubleDivergence A e x + flatDoubleDivergence B f x = 0 := by
  let F := fun x => flatDoubleDivergence A e x + flatDoubleDivergence B f x
  have hF : ContinuousOn F W := fun y hy =>
    ((contDiffAt_flatDoubleDivergence e (fun i j => ha i j y hy)).add
      (contDiffAt_flatDoubleDivergence f (fun i j => hb i j y hy))).continuousAt.continuousWithinAt
  have he : ∀ᵐ y ∂μ, y ∈ W → F y = 0 := by
    apply hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF.locallyIntegrableOn hW.measurableSet)
    intro η hη hc hs
    have hA := fun i j y (hy : y ∈ tsupport η) => ha i j y (hs hy)
    have hB := fun i j y (hy : y ∈ tsupport η) => hb i j y (hs hy)
    have heq := hstat η hη hc hs
    rw [integral_add (integrable_flatTestContraction A e hA hη hc)
      (integrable_flatTestContraction B f hB hη hc)] at heq
    change (∫ y, ∑ i, ∑ j, A i j y * dirDeriv (e i) (dirDeriv (e j) η) y ∂μ) +
      (∫ y, ∑ i, ∑ j, B i j y * dirDeriv (f i) (dirDeriv (f j) η) y ∂μ) = 0 at heq
    rw [integral_double_contraction_compact A e η hA hη hc,
      integral_double_contraction_compact B f η hB hη hc] at heq
    have heFun : (fun y => η y • F y) =
        (fun y => flatDoubleDivergence A e y * η y + flatDoubleDivergence B f y * η y) := by
      funext y
      dsimp [F]
      ring
    rw [heFun,integral_add (integrable_flatDoubleDivergence_mul A e hA hη hc)
      (integrable_flatDoubleDivergence_mul B f hB hη hc)]
    exact heq
  have he' : F =ᵐ[μ.restrict W] (fun _ => 0) :=
    (ae_restrict_iff' hW.measurableSet).mpr he
  exact (MeasureTheory.Measure.eqOn_open_of_ae_eq he' hW hF continuousOn_const) hx

end AffineBernstein
end

end OAI
