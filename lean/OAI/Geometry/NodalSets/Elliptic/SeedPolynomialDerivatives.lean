import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import OAI.Geometry.NodalSets.Elliptic.SphericalSeed

namespace OAI

namespace Yau.Target
open scoped ContDiff
noncomputable section

def seedQuadraticDerivative (x : SeedAmbient) : SeedAmbient →L[ℝ] ℂ :=
  seedZ1 x • seedZ2 + seedZ2 x • seedZ1

lemma seedQuadratic_hasFDerivAt (x : SeedAmbient) :
    HasFDerivAt seedQuadratic (seedQuadraticDerivative x) x :=
  (seedZ1.hasFDerivAt).mul (seedZ2.hasFDerivAt)

lemma ambientComplexSeed_hasFDerivAt (N : ℕ) (x : SeedAmbient) :
    HasFDerivAt (ambientComplexSeed N)
      (((N:ℂ) * seedQuadratic x^(N-1)) • seedQuadraticDerivative x) x := by
  convert! (seedQuadratic_hasFDerivAt x).pow N using 1
  simp [nsmul_eq_mul]

lemma ambientComplexSeed_fderiv (N : ℕ) (x v : SeedAmbient) :
    fderiv ℝ (ambientComplexSeed N) x v =
      (N:ℂ) * seedQuadratic x^(N-1) *
        (seedZ1 x * seedZ2 v + seedZ2 x * seedZ1 v) := by
  rw [(ambientComplexSeed_hasFDerivAt N x).fderiv]
  rfl

lemma seedQuadraticDerivative_apply_hasFDerivAt (x v : SeedAmbient) :
    HasFDerivAt (fun y ↦ seedQuadraticDerivative y v)
      (seedZ2 v • seedZ1 + seedZ1 v • seedZ2) x := by
  convert! (seedZ1.hasFDerivAt.mul_const (seedZ2 v)).add
    (seedZ2.hasFDerivAt.mul_const (seedZ1 v)) using 1

lemma ambientComplexSeed_second (N : ℕ) (x v w : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientComplexSeed N) y v) x w =
      (N:ℂ) * ((N-1:ℕ):ℂ) * seedQuadratic x^(N-1-1) *
        seedQuadraticDerivative x w * seedQuadraticDerivative x v +
      (N:ℂ) * seedQuadratic x^(N-1) *
        (seedZ2 v * seedZ1 w + seedZ1 v * seedZ2 w) := by
  have he : (fun y ↦ fderiv ℝ (ambientComplexSeed N) y v) =
      (fun y ↦ (N:ℂ) * seedQuadratic y^(N-1) * seedQuadraticDerivative y v) := by
    funext y
    rw [(ambientComplexSeed_hasFDerivAt N y).fderiv]
    rfl
  rw [he]
  have hd := (((seedQuadratic_hasFDerivAt x).pow (N-1)).const_mul (N:ℂ)).mul
    (seedQuadraticDerivative_apply_hasFDerivAt x v)
  change HasFDerivAt (fun y ↦ (N:ℂ) * seedQuadratic y^(N-1) * seedQuadraticDerivative y v) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul]
  ring

lemma ambientRealSeed_fderiv (N : ℕ) (x v : SeedAmbient) :
    fderiv ℝ (ambientRealSeed N) x v = (fderiv ℝ (ambientComplexSeed N) x v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x (ambientComplexSeed_hasFDerivAt N x)
  change HasFDerivAt (ambientRealSeed N) _ x at h
  rw [h.fderiv,(ambientComplexSeed_hasFDerivAt N x).fderiv]
  rfl

lemma ambientRealSeed_second (N : ℕ) (x v w : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientRealSeed N) y v) x w =
      (fderiv ℝ (fun y ↦ fderiv ℝ (ambientComplexSeed N) y v) x w).re := by
  simp_rw [ambientRealSeed_fderiv]
  have hc := ((ambientComplexSeed_contDiff N).fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)).clm_apply
    (contDiff_const (c := v))
  exact congrArg (fun L : SeedAmbient →L[ℝ] ℝ ↦ L w)
    (Complex.reCLM.hasFDerivAt.comp x
      (hc.differentiable (by simp) x).hasFDerivAt).fderiv

end
end Yau.Target

end OAI
