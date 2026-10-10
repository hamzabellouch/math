import OAI.Geometry.NodalSets.Elliptic.SeedConcretePoint
import OAI.Geometry.NodalSets.Elliptic.SeedPolynomialDerivatives

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩

def seedLogDomain : Set SeedAmbient := seedQuadratic ⁻¹' Complex.slitPlane

def seedLog (x : SeedAmbient) : ℂ := Complex.log (seedQuadratic x)

def seedLogReal (x : SeedAmbient) : ℝ := (seedLog x).re

def seedLogImag (x : SeedAmbient) : ℝ := (seedLog x).im

def sphereSeedLogReal (x : Base) : ℝ := seedLogReal x

def sphereSeedLogImag (x : Base) : ℝ := seedLogImag x

lemma seedLogDomain_open : IsOpen seedLogDomain :=
  Complex.isOpen_slitPlane.preimage seedQuadratic_contDiff.continuous

lemma seedPoint_mem_logDomain : (seedPoint : SeedAmbient) ∈ seedLogDomain := seedPoint_slitPlane

lemma seedLog_contDiffAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedLog x :=
  ((Complex.contDiffAt_log hx (n := ∞)).restrict_scalars ℝ).comp x seedQuadratic_contDiff.contDiffAt

lemma seedLog_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    HasFDerivAt seedLog ((seedQuadratic x)⁻¹ • seedQuadraticDerivative x) x := by
  convert! ((Complex.hasStrictFDerivAt_log_real hx).hasFDerivAt).comp x
    (seedQuadratic_hasFDerivAt x) using 1

lemma seedLog_fderiv {x : SeedAmbient} (hx : x ∈ seedLogDomain) (v : SeedAmbient) :
    fderiv ℝ seedLog x v = (seedQuadraticDerivative x v) / seedQuadratic x := by
  rw [(seedLog_hasFDerivAt hx).fderiv]
  simp [div_eq_mul_inv,mul_comm]

lemma seedLogReal_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    HasFDerivAt seedLogReal
      (Complex.reCLM.comp ((seedQuadratic x)⁻¹ • seedQuadraticDerivative x)) x :=
  Complex.reCLM.hasFDerivAt.comp x (seedLog_hasFDerivAt hx)

lemma seedLogImag_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    HasFDerivAt seedLogImag
      (Complex.imCLM.comp ((seedQuadratic x)⁻¹ • seedQuadraticDerivative x)) x :=
  Complex.imCLM.hasFDerivAt.comp x (seedLog_hasFDerivAt hx)

lemma sphereSeedLogReal_smoothAt {x : Base} (hx : (x : SeedAmbient) ∈ seedLogDomain) :
    ContMDiffAt (𝓡 4) 𝓘(ℝ,ℝ) ∞ sphereSeedLogReal x :=
  (Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hx)).contMDiffAt.comp x
    (contMDiff_coe_sphere (n := 4)).contMDiffAt

lemma sphereSeedLogImag_smoothAt {x : Base} (hx : (x : SeedAmbient) ∈ seedLogDomain) :
    ContMDiffAt (𝓡 4) 𝓘(ℝ,ℝ) ∞ sphereSeedLogImag x :=
  (Complex.imCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hx)).contMDiffAt.comp x
    (contMDiff_coe_sphere (n := 4)).contMDiffAt

lemma ambientSeed_exp_log (N : ℕ) {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ambientComplexSeed N x = Complex.exp ((N:ℂ)*seedLog x) := by
  rw [Complex.exp_nat_mul,seedLog,Complex.exp_log (Complex.slitPlane_ne_zero hx)]
  rfl

lemma ambientSeed_log_trigonometric (N : ℕ) {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ambientRealSeed N x = Real.exp ((N:ℝ)*seedLogReal x) * Real.cos ((N:ℝ)*seedLogImag x) := by
  rw [ambientRealSeed,ambientSeed_exp_log N hx,Complex.exp_re]
  simp [Complex.mul_re,Complex.mul_im,seedLogReal,seedLogImag]

lemma sphericalSeed_log_trigonometric (N : ℕ) {x : Base}
    (hx : (x : SeedAmbient) ∈ seedLogDomain) :
    sphericalSeed N x = Real.exp ((N:ℝ)*sphereSeedLogReal x) *
      Real.cos ((N:ℝ)*sphereSeedLogImag x) := ambientSeed_log_trigonometric N hx

end
end Yau.Target

end OAI
