import Mathlib
import OAI.Geometry.Borsuk.Support.FullSupport

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

lemma Admissible.signedExtension_eq_zero_iff {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) : signedExtension f A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    have ht : Matrix.trace (CFC.abs A) = 0 := by
      rw [← hf.signedExtension_abs_sum hA, hz]
      simp
    have habs : CFC.abs A = 0 := matrix_psd_trace_zero (CFC.abs_nonneg A) ht
    have hsq := CFC.abs_mul_abs A
    rw [habs, zero_mul] at hsq
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.star_eq_conjTranspose] using hsq.symm
  · rintro rfl
    simp [signedExtension]

noncomputable def normalizedSignedExtension (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    EuclideanSpace ℝ ι :=
  ‖WithLp.toLp 2 (signedExtension f A)‖⁻¹ • WithLp.toLp 2 (signedExtension f A)

lemma Admissible.normalizedSignedExtension_norm {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hneq : A ≠ 0) :
    ‖normalizedSignedExtension f A‖ = 1 := by
  have hn : WithLp.toLp 2 (signedExtension f A) ≠ 0 := by
    intro hz
    have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hz
    exact hneq ((hf.signedExtension_eq_zero_iff hA).mp hs)
  simp [normalizedSignedExtension, norm_smul, norm_inv, hn]

omit [Nonempty ν] in
lemma normalizedSignedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    normalizedSignedExtension f (-A) = -normalizedSignedExtension f A := by
  simp [normalizedSignedExtension, signedExtension_odd, WithLp.toLp_neg]

lemma Admissible.normalizedSignedExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (normalizedSignedExtension f) {A : Matrix ν ν ℝ | IsSelfAdjoint A ∧ A ≠ 0} := by
  have hc : ContinuousOn (fun A : Matrix ν ν ℝ => WithLp.toLp 2 (signedExtension f A))
      {A | IsSelfAdjoint A ∧ A ≠ 0} :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hf.signedExtension_continuousOn.mono (fun _ h => h.1))
  apply ContinuousOn.smul (ContinuousOn.inv₀ hc.norm _) hc
  intro A hA
  rw [norm_ne_zero_iff]
  intro hh
  have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hh
  exact hA.2 ((hf.signedExtension_eq_zero_iff hA.1).mp hs)

end SphereExtension

end BorsukNine

end OAI
