import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityBulkCoefficients
import OAI.Probability.Perceptron.Cavity.CavitySphericalMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace SphericalPerceptronFreeEnergy

lemma finiteGaussian_coordinate_projection {I J : Type*} [Fintype I] [Fintype J]
    (e : J→I) (he : Function.Injective e) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I=>fun j=>x (e j))
      (stdGaussian (EuclideanSpace ℝ I)) (Measure.pi fun _ : J=>gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (PiLp.continuous_toLp 2 _).measurable]
  change (Measure.pi fun _ : I=>gaussianReal 0 1).map (fun x j=>x (e j))=_
  rw [←Measure.infinitePi_eq_pi,Measure.map_infinitePi_infinitePi_of_inj he,Measure.infinitePi_eq_pi]

lemma finiteGaussian_curry_preserving (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (fun x : I×J→ℝ=>fun i j=>x (i,j))
      (Measure.pi fun _ : I×J=>gaussianReal 0 1)
      (Measure.pi fun _ : I=>Measure.pi fun _ : J=>gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  have h:=Measure.infinitePi_map_curry (μ:=fun (_ : I) (_ : J)=>gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  rfl

def cavityBulkNoiseSplit (n d m M : ℕ)
    (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ) :=
  (fun t=>WithLp.toLp 2 (fun i=>y (Sum.inl i,Sum.inl t)),
    fun t i=>y (Sum.inr t,Sum.inr i))

lemma cavityBulkNoiseSplit_preserving (n d m M : ℕ) :
    MeasurePreserving (cavityBulkNoiseSplit n d m M)
      (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
      ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
        (finitePatternRowsLaw (m+1) d)) := by
  let e : (Fin M×Fin (n+1))⊕(Fin d×Fin (m+1))→CavityBulkNoiseIndex n d m M :=
    Sum.elim (fun p=>(Sum.inl p.2,Sum.inl p.1)) (fun p=>(Sum.inr p.1,Sum.inr p.2))
  have he : Function.Injective e := by
    intro a b h
    cases a <;> cases b <;> simp only [e,Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq,Sum.inl.injEq,
      Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,false_and] at h
    · exact congrArg Sum.inl (Prod.ext h.2 h.1)
    · exact congrArg Sum.inr (Prod.ext h.1 h.2)
  have hp:=(measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin M×Fin (n+1))⊕(Fin d×Fin (m+1))=>gaussianReal 0 1)).comp
    (finiteGaussian_coordinate_projection e he)
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin (n+1)→ℝ)→Spin (n+1))
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin (n+1))) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hleft:=(measurePreserving_pi (fun _ : Fin M=>Measure.pi fun _ : Fin (n+1)=>gaussianReal 0 1)
    (fun _=>stdGaussian (Spin (n+1))) (fun _=>ht)).comp (finiteGaussian_curry_preserving (Fin M) (Fin (n+1)))
  convert (hleft.prod (finiteGaussian_curry_preserving (Fin d) (Fin (m+1)))).comp hp using 1
  · rfl
  · rfl

lemma cavityBulkNoiseSplit_scalar (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) (t : Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x (Sum.inr t)) y=
      ∑ i,(cavityBulkNoiseSplit n d m M y).2 t i*x.val i := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,cavityBulkFeature,
    star_trivial,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,cavityBulkBase,Fintype.sum_sum_type,cavityBulkNoiseSplit]
  simp only [Sum.inl_ne_inr,Sum.inr.injEq,ite_false,ite_self,Finset.sum_const_zero,zero_add]
  rw [Finset.sum_comm]
  simp

lemma cavityBulkNoiseSplit_vector (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y=
      cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,a.1 t i*x.val i))
        (Real.sqrt (m+1:ℕ))⁻¹ (cavityBulkNoiseSplit n d m M y).1 := by
  classical
  ext i
  simp only [gaussianRows_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,cavityBulkFeature,
    star_trivial,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,cavityBulkBase,Fintype.sum_sum_type,
    cavityBulkNoiseSplit,cavityVectorField,PiLp.smul_apply,smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  simp only [Sum.inl.injEq,Sum.inr_ne_inl,ite_false,ite_self,Finset.sum_const_zero,add_zero]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']
  try simp only [cavityVectorField,PiLp.smul_apply,smul_eq_mul,PiLp.sum_apply,PiLp.toLp_apply]
  simp_rw [mul_comm (y.ofLp _) _]
  simp only [WithLp.ofLp_sum,PiLp.smul_apply,Finset.sum_apply,smul_eq_mul]
  simp only [mul_assoc,Finset.mul_sum]
end SphericalPerceptronFreeEnergy

end

end OAI
