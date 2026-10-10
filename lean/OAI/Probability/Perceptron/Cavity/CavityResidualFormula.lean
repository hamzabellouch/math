import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityFiniteEvaluation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
lemma cavity_scalar_residual (d : ℕ) (f : ℝ→ᵇℝ) (s : ℝ≥0) (x : Fin d→ℝ) :
    (∫ y : Spin d,Real.exp (∑ i,f (x i+Real.sqrt s*y i)) ∂stdGaussian (Spin d))=
      Real.exp (∑ i,heatLog s 1 f (x i)) := by
  let G : (Fin d→ℝ)→ℝ := fun y=>∏ i,Real.exp (f (x i+Real.sqrt s*y i))
  have hm : Measurable G := by unfold G; fun_prop
  have hp:=stdGaussian_ofLp_preserving d
  simp only [Real.exp_sum]
  change (∫ y,G (WithLp.ofLp y) ∂stdGaussian (Spin d))=_
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]
  dsimp only [G]
  rw [integral_fintype_prod_eq_prod (fun i t=>Real.exp (f (x i+Real.sqrt s*t)))]
  apply Finset.prod_congr rfl
  intro i hi
  have he:=exp_heatLog s 1 (by norm_num) f (x i)
  rw [gaussianAverage_scaling] at he
  simpa only [NNReal.coe_one,one_mul,expBCF_apply] using he.symm

def cavityFullSingle (n d : ℕ) (f : ℝ→ᵇℝ)
    (v : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) : ℝ :=
  sphericalExp n (gaussianSumSplit v).1 (Real.sqrt (n+1:ℕ))*Real.exp (∑ i,f (v (Sum.inr i)))

lemma cavityFullSingle_measurable (n d : ℕ) (f : ℝ→ᵇℝ) : Measurable (cavityFullSingle n d f) := by
  apply ((sphericalExp_continuous n _).measurable.comp gaussianSumSplit_measurable.fst).mul
  apply Measurable.exp
  apply Finset.measurable_sum
  intro i hi
  exact f.measurable.comp ((measurable_pi_apply (Sum.inr i)).comp (MeasurableEquiv.toLp 2 _).symm.measurable)

lemma cavity_full_residual (n d : ℕ) (f : ℝ→ᵇℝ) (a s : ℝ≥0)
    (v : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    (∫ y,cavityFullSingle n d f (WithLp.toLp 2 (fun i=>v i+
      Sum.elim (fun _=>Real.sqrt a) (fun _=>Real.sqrt s) i*y i))
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))=
    Real.exp ((n+1:ℕ)*a/2+logSphericalExp n (Real.sqrt (n+1:ℕ)) (gaussianSumSplit v).1+
      ∑ i,heatLog s 1 f (v (Sum.inr i))) := by
  let G : Spin (n+1)×Spin d→ℝ:=fun y=>
    sphericalExp n ((gaussianSumSplit v).1+Real.sqrt a • y.1) (Real.sqrt (n+1:ℕ))*
      Real.exp (∑ i,f (v (Sum.inr i)+Real.sqrt s*y.2 i))
  have hm : Measurable G := by
    apply ((sphericalExp_continuous n _).measurable.comp (by fun_prop)).mul
    fun_prop
  have he y : cavityFullSingle n d f (WithLp.toLp 2 (fun i=>v i+
      Sum.elim (fun _=>Real.sqrt a) (fun _=>Real.sqrt s) i*y i))=G (gaussianSumSplit y) := rfl
  simp_rw [he]
  have hp:=gaussianSumSplit_preserving (I:=Fin (n+1)) (J:=Fin d)
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]
  dsimp only [G]
  rw [integral_prod_mul (fun y=>sphericalExp n ((gaussianSumSplit v).1+Real.sqrt a • y) (Real.sqrt (n+1:ℕ)))
      (fun y : Spin d=>Real.exp (∑ i,f (v (Sum.inr i)+Real.sqrt s*y i))),
    sphericalExp_gaussian_average,Real.sq_sqrt (by positivity : 0≤((n+1:ℕ):ℝ)),
    Real.sq_sqrt a.coe_nonneg,cavity_scalar_residual]
  simp only [Real.exp_add,logSphericalExp,Real.exp_log (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n _ _))]
end SphericalPerceptronFreeEnergy

end

end OAI
