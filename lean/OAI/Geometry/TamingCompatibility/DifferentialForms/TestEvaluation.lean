import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexReal

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {n m : ℕ} {ι : Type*} [Fintype ι]

def componentTest (j : Fin n) (φ : 𝓢(D,ℝ)) : 𝓢(D,R n) :=
  SchwartzMap.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j 1)) φ

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
@[simp] lemma componentTest_apply (j : Fin n) (φ : 𝓢(D,ℝ)) (x : D) :
    componentTest j φ x = φ x • EuclideanSpace.single j 1 := rfl

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma componentTest_inner (j : Fin n) (φ : 𝓢(D,ℝ)) (u : R n) (x : D) :
    ⟪u,componentTest j φ x⟫ = φ x * u j := by
  rw [componentTest_apply,real_inner_smul_right]
  rw [EuclideanSpace.inner_single_right]
  simp

lemma embedded_distribution_apply (u : 𝓢(D,R n)) (φ : 𝓢(D,ℝ)) :
    (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = embed n (∫ x, φ x • u x) := by
  rw [SchwartzMap.coe_apply]
  have hi : Integrable (fun x => φ x • u x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM (R n) φ u).integrable (μ := volume)
  rw [← ContinuousLinearMap.integral_comp_comm (embed n) hi]
  apply integral_congr_ae
  filter_upwards [] with x
  ext j
  simp [embed_apply]

lemma embedded_component_apply (u : 𝓢(D,R n)) (φ : 𝓢(D,ℝ)) (j : Fin n) :
    ((SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      ((∫ x, ⟪u x,componentTest j φ x⟫ : ℝ) : ℂ) := by
  rw [embedded_distribution_apply,embed_apply]
  congr 1
  have hi : Integrable (fun x => φ x • u x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM (R n) φ u).integrable (μ := volume)
  change EuclideanSpace.proj j (∫ x, φ x • u x) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [componentTest_inner]
  rfl

lemma square_component_apply (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (u : 𝓢(D,R n))
    (φ : 𝓢(D,ℝ)) (j : Fin n) :
    (square e a b ρ (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      ((∫ x, ρ x * ⟪LocalFormalAdjoint.firstOrder e a b u x,
        LocalFormalAdjoint.firstOrder e a b (componentTest j φ) x⟫ : ℝ) : ℂ) := by
  rw [square_embed,embedded_component_apply]
  congr 1
  have h := LocalFormalAdjoint.firstOrder_pairing e
    (fun i => LocalFormalAdjoint.weightedCoefficient ρ (a i))
    (LocalFormalAdjoint.weightedCoefficient ρ b) (componentTest j φ)
    (LocalFormalAdjoint.firstOrder e a b u)
  simp_rw [LocalFormalAdjoint.weighted_firstOrder e a b ρ ρ.hasTemperateGrowth] at h
  simpa only [real_inner_smul_left,real_inner_smul_right,real_inner_comm] using h.symm
end TamingCompatibility.ComplexMatrix

end

end OAI
