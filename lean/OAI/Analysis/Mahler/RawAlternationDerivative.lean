import OAI.Analysis.Mahler.RawCoefficientDerivative
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def rawAlternatedCoefficientDerivative
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (v : ι → E) : E →L[ℝ] ℂ :=
  ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • rawCoefficientDerivative D (v ∘ σ)

lemma rawAlternatedCoefficientDerivative_apply
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (v : ι → E) (w : E) :
    rawAlternatedCoefficientDerivative D v w = (D w).alternatization v := by
  simp [rawAlternatedCoefficientDerivative, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, Function.comp_def]

theorem HasRawFDerivAt.alternatization
    {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ} {x : E}
    (ha : HasRawFDerivAt a D x) (v : ι → E) :
    HasFDerivAt (fun y => (a y).alternatization v)
      (rawAlternatedCoefficientDerivative D v) x := by
  simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  have hd : HasFDerivAt
      (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • (fun y => a y (v ∘ σ)))
      (rawAlternatedCoefficientDerivative D v) x :=
    HasFDerivAt.sum (u := Finset.univ)
      (fun (σ : Equiv.Perm ι) _ => (ha (v ∘ σ)).const_smul (Equiv.Perm.sign σ))
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => by simp [Finset.sum_apply, Function.comp_def])

/-- Differentiating an actual continuous form presented as a full
alternatization is full alternatization of its raw coefficient derivative.
The normalization is exactly the exterior derivative, with no factor. -/
theorem extDeriv_of_raw_alternatization {n : ℕ}
    {a : E → MultilinearMap ℝ (fun _ : Fin n => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => E) ℂ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hω : DifferentiableAt ℝ ω x)
    (heq : ∀ᶠ y in 𝓝 x, (ω y).toAlternatingMap = (a y).alternatization)
    (ha : HasRawFDerivAt a D x) :
    (extDeriv ω x).toAlternatingMap = D.uncurryLeft.alternatization := by
  ext v
  change extDeriv ω x v = _
  rw [extDeriv_apply hω, alternatization_uncurryLeft_apply]
  apply Finset.sum_congr rfl
  intro p _
  have he : (fun y => ω y (p.removeNth v)) =ᶠ[𝓝 x]
      (fun y => (a y).alternatization (p.removeNth v)) :=
    heq.mono (fun y hy => congrArg (fun b => b (p.removeNth v)) hy)
  rw [he.fderiv_eq, (ha.alternatization (p.removeNth v)).fderiv,
    rawAlternatedCoefficientDerivative_apply]

end
end Mahler

end OAI
