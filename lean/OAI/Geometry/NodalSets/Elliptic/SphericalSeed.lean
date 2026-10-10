import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import OAI.Geometry.NodalSets.Model

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

abbrev SeedAmbient := EuclideanSpace ℝ (Fin 5)
local instance : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩

def seedCoordinate (i : Fin 5) : SeedAmbient →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

def seedZ1 : SeedAmbient →L[ℝ] ℂ := seedCoordinate 0 + Complex.I • seedCoordinate 1

def seedZ2 : SeedAmbient →L[ℝ] ℂ := seedCoordinate 2 + Complex.I • seedCoordinate 3

def seedQuadratic (x : SeedAmbient) : ℂ := seedZ1 x * seedZ2 x

def ambientComplexSeed (N : ℕ) (x : SeedAmbient) : ℂ := seedQuadratic x ^ N

def ambientRealSeed (N : ℕ) (x : SeedAmbient) : ℝ := (ambientComplexSeed N x).re

def sphericalSeed (N : ℕ) (x : Base) : ℝ := ambientRealSeed N x

def seedEigenvalue (N : ℕ) : ℝ := 4*(N:ℝ)^2 + 6*(N:ℝ)

lemma seedZ1_apply (x : SeedAmbient) : seedZ1 x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := rfl
lemma seedZ2_apply (x : SeedAmbient) : seedZ2 x = (x 2 : ℂ) + Complex.I * (x 3 : ℂ) := rfl

lemma sphericalSeed_literal (N : ℕ) (x : Base) : sphericalSeed N x =
    Complex.re (((((x : SeedAmbient) 0 : ℂ) + Complex.I * ((x : SeedAmbient) 1 : ℂ)) *
      (((x : SeedAmbient) 2 : ℂ) + Complex.I * ((x : SeedAmbient) 3 : ℂ)))^N) := rfl

lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

lemma ambientComplexSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientComplexSeed N) :=
  seedQuadratic_contDiff.pow N

lemma ambientRealSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientRealSeed N) :=
  Complex.reCLM.contDiff.comp (ambientComplexSeed_contDiff N)

lemma sphericalSeed_smooth (N : ℕ) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (sphericalSeed N) :=
  (ambientRealSeed_contDiff N).contMDiff.comp (contMDiff_coe_sphere (n := 4))

lemma ambientComplexSeed_homogeneous (N : ℕ) (r : ℝ) (x : SeedAmbient) :
    ambientComplexSeed N (r • x) = (r : ℂ)^(2*N) * ambientComplexSeed N x := by
  simp only [ambientComplexSeed,seedQuadratic,map_smul,Complex.real_smul]
  rw [show (r:ℂ) * seedZ1 x * ((r:ℂ) * seedZ2 x) = (r:ℂ)^2 * (seedZ1 x * seedZ2 x) by ring,
    mul_pow,← pow_mul]

lemma ambientRealSeed_homogeneous (N : ℕ) (r : ℝ) (x : SeedAmbient) :
    ambientRealSeed N (r • x) = r^(2*N) * ambientRealSeed N x := by
  simp [ambientRealSeed,ambientComplexSeed_homogeneous,← Complex.ofReal_pow]

lemma seedEigenvalue_degree (N : ℕ) : seedEigenvalue N = (2*(N:ℝ))*(2*(N:ℝ)+3) := by
  unfold seedEigenvalue; ring

lemma seedEigenvalue_pos {N : ℕ} (hN : 0 < N) : 0 < seedEigenvalue N := by
  unfold seedEigenvalue
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

end
end Yau.Target

end OAI
