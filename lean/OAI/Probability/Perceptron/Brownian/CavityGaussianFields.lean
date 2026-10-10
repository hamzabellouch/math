import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereHeat
import OAI.Probability.Perceptron.Cavity.CavityGaussianQuadratic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma gaussian_inner_preserving (L : ℕ) (z : Spin L) :
    MeasurePreserving (fun y : Spin L=>inner ℝ z y) (stdGaussian (Spin L))
      (gaussianReal 0 (‖z‖₊^2)) := by
  refine ⟨by fun_prop,?_⟩
  have h := IsGaussian.map_eq_gaussianReal (μ:=stdGaussian (Spin L)) (innerSL ℝ z)
  simp only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm] at h
  have he : (‖z‖^2).toNNReal = (‖z‖₊^2) := by
    ext; simp
  simpa only [he,coe_innerSL_apply] using h

lemma gaussian_cavity_projection (M L : ℕ) (z : Spin L) :
    MeasurePreserving (fun y : Fin M→Spin L=>fun i=>inner ℝ z (y i))
      (Measure.pi (fun _=>stdGaussian (Spin L)))
      (Measure.pi (fun _ : Fin M=>gaussianReal 0 (‖z‖₊^2))) := by
  have (_index : Fin M) : SigmaFinite (gaussianReal 0 (‖z‖₊^2)) := inferInstance
  exact measurePreserving_pi _ _ (fun _=>gaussian_inner_preserving L z)

def cavityQuadraticField (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (y : Fin M→Spin L) : ℝ :=
  t*∑ i,a i*((inner ℝ z (y i))^2-‖z‖^2)

lemma cavityQuadraticField_memLp (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) :
    MemLp (cavityQuadraticField M L a t z) 2 (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  have h := (cavityQuadraticScalar_memLp M a t (‖z‖₊^2)).comp_measurePreserving
    (gaussian_cavity_projection M L z)
  change MemLp (fun y : Fin M→Spin L=>t*∑ i,a i*((inner ℝ z (y i))^2-‖z‖^2)) 2 _
  simpa only [Function.comp_def,cavityQuadraticScalar,NNReal.coe_pow,coe_nnnorm] using h

lemma cavityQuadraticField_second_moment (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) :
    (∫ y,(cavityQuadraticField M L a t z y)^2 ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
      t^2*‖z‖^4*squareGaussianVariance*∑ i,(a i)^2 := by
  have hm := gaussian_cavity_projection M L z
  have he := (integral_map hm.aemeasurable (f:=fun y=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) (show AEStronglyMeasurable (fun y : Fin M→ℝ=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) _ from (show Continuous (fun y : Fin M→ℝ=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) from by unfold cavityQuadraticScalar; fun_prop).aestronglyMeasurable)).symm
  rw [hm.map_eq] at he
  rw [cavityQuadraticScalar_second_moment] at he
  simp only [cavityQuadraticScalar,NNReal.coe_pow,coe_nnnorm] at he
  calc
    _ = ∫ y : Fin M→Spin L,(t*∑ i,a i*((inner ℝ z (y i))^2-‖z‖^2))^2 ∂Measure.pi (fun _=>stdGaussian (Spin L)) := rfl
    _ = _ := he
    _ = t^2*‖z‖^4*squareGaussianVariance*∑ i,(a i)^2 := by ring

lemma cavityQuadraticField_second_bound (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L)
    {C D : ℝ} (hC : 0≤C) (_hD : 0≤D) (ha : ∀ i,|a i|≤C) (hz : ‖z‖^2≤D) :
    (∫ y,(cavityQuadraticField M L a t z y)^2 ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      t^2*D^2*squareGaussianVariance*M*C^2 := by
  have hm := gaussian_cavity_projection M L z
  have he := (integral_map hm.aemeasurable (f:=fun y=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) (show AEStronglyMeasurable (fun y : Fin M→ℝ=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) _ from (show Continuous (fun y : Fin M→ℝ=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) from by unfold cavityQuadraticScalar; fun_prop).aestronglyMeasurable)).symm
  rw [hm.map_eq] at he
  have hf : (fun y : Fin M→Spin L=>(cavityQuadraticScalar M a t (‖z‖₊^2) (fun i=>inner ℝ z (y i)))^2)=
      (fun y=>(cavityQuadraticField M L a t z y)^2) := by
    ext y; simp only [cavityQuadraticScalar,cavityQuadraticField,NNReal.coe_pow,coe_nnnorm]
  rw [hf] at he
  rw [he]
  apply (cavityQuadraticScalar_second_moment_bound M a t (‖z‖₊^2) hC ha).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg C)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg M)
  apply mul_le_mul_of_nonneg_right _ squareGaussianVariance_nonneg
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg ‖z‖) hz 2) (sq_nonneg t)

def cavityLinearField (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (y : Fin M→Spin L) : ℝ :=
  t*∑ i,a i*inner ℝ z (y i)

lemma cavityLinearField_exp_moment (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (p : ℝ) :
    (∫ y,Real.exp (p*cavityLinearField M L a t z y) ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
      Real.exp (p^2*t^2*‖z‖^2/2*∑ i,(a i)^2) := by
  have he y : Real.exp (p*cavityLinearField M L a t z y)=
      ∏ i,Real.exp ((p*t*a i)*inner ℝ z (y i)) := by
    unfold cavityLinearField
    rw [←mul_assoc,Finset.mul_sum,Real.exp_sum]
    congr 1
    ext i
    congr 1
    ring
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun i (x : Spin L)=>Real.exp ((p*t*a i)*inner ℝ z x))]
  simp_rw [integral_exp_inner_stdGaussian]
  rw [←Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
