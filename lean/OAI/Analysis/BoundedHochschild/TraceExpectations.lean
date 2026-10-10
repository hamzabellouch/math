import Mathlib
import OAI.Analysis.BoundedHochschild.CentralPrimitives

namespace OAI

/-! Trace pairing norms, predual vectors and trace-preserving expectations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder
namespace HochschildTraceNorm
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_mul_eq_abs_mul (b d : A) : ‖b*d‖=‖CFC.abs b*d‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two,pow_two,← CStarRing.norm_star_mul_self,← CStarRing.norm_star_mul_self]
  congr 1
  simp only [star_mul,(IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)).star_eq]
  rw [mul_assoc,← mul_assoc (star b),← CFC.abs_mul_abs b]
  simp only [mul_assoc]

 

theorem exists_approx_polar (b : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖v‖ ≤ 1 ∧ ‖b-v*CFC.abs b‖ ≤ ε ∧
      ‖CFC.abs b-star v*b‖ ≤ ε := by
  let a := CFC.abs b
  have ha0 : 0 ≤ a := CFC.abs_nonneg b
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  let f : ℝ → ℝ := fun t => (t+ε)⁻¹
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply ContinuousOn.inv₀ ((continuous_id.add continuous_const).continuousOn)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg ha0 ht
    exact (show 0 < t+ε from by linarith).ne'
  let q := cfc f a
  have hq : IsSelfAdjoint q := cfc_predicate f a
  have hqa : Commute q a := (Commute.refl a).cfc_real f
  have hab : a*a=star b*b := CFC.abs_mul_abs b
  have haq : a*q=cfc (fun t => t*f t) a := by
    change a*cfc f a = cfc (fun t => id t*f t) a
    rw [cfc_mul id f a continuousOn_id hf,cfc_id ℝ a ha]
  have hnormaq : ‖a*q‖ ≤ 1 := by
    rw [haq]
    apply norm_cfc_le (by positivity)
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    dsimp [f]
    rw [abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
    exact (mul_inv_le_iff₀ hp).mpr (by linarith)
  have hres : a-q*a*a=cfc (fun t => t-f t*t*t) a := by
    change a-cfc f a*a*a=cfc (fun t => id t - (fun s => f s * id s * id s) t) a
    rw [cfc_sub id (fun s => f s * id s * id s) a continuousOn_id ((hf.mul continuousOn_id).mul continuousOn_id),
      cfc_mul (fun t => f t * id t) id a (hf.mul continuousOn_id) continuousOn_id,
      cfc_mul f id a hf continuousOn_id,cfc_id ℝ a ha]
  have hresnorm : ‖a-q*a*a‖ ≤ ε := by
    rw [hres]
    apply norm_cfc_le hε.le
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    have heq : t-(t+ε)⁻¹*t*t=ε*t/(t+ε) := by field_simp; ring
    dsimp [f]
    rw [heq,abs_of_nonneg (div_nonneg (mul_nonneg hε.le ht0) hp.le)]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨b*q,?_,?_,?_⟩
  · have hh : ‖b*q‖^2 ≤ 1 := by
      rw [pow_two,← CStarRing.norm_star_mul_self]
      have heq : star (b*q)*(b*q)=(a*q)*(a*q) := by
        rw [star_mul,hq.star_eq]
        calc
          q*star b*(b*q)=q*(star b*b)*q := by simp only [mul_assoc]
          _ = q*(a*a)*q := by rw [hab]
          _ = (a*q)*(a*q) := by rw [← mul_assoc q a,hqa.eq]; simp only [mul_assoc]
      rw [heq]
      exact (norm_mul_le _ _).trans ((mul_le_mul hnormaq hnormaq (norm_nonneg _) (by positivity)).trans_eq (by norm_num))
    nlinarith [norm_nonneg (b*q)]
  · have heq : b-b*q*a=b*(1-q*a) := by simp only [mul_sub,mul_one,mul_assoc]
    rw [heq,norm_mul_eq_abs_mul]
    change ‖a*(1-q*a)‖ ≤ ε
    have heq' : a*(1-q*a)=a-q*a*a := by
      rw [mul_sub,mul_one,← mul_assoc,hqa.eq]
    rw [heq']
    exact hresnorm
  · simp only [star_mul,hq.star_eq]
    rw [mul_assoc q (star b),← hab]
    simpa only [mul_assoc] using hresnorm
end HochschildTraceNorm

 

open scoped ComplexOrder
namespace HochschildTraceNorm
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

def traceCLM : A →L[ℂ] ℂ where
  toLinearMap := τ.toLinearMap
  cont := map_continuous τ

@[simp] lemma traceCLM_apply (a : A) : traceCLM τ a=τ a := rfl

include htr in
lemma positive_weight_trace_bound (a x : A) (ha : 0 ≤ a) :
    ‖τ (a*x)‖ ≤ (τ a).re * ‖x‖ := by
  let r := CFC.sqrt a
  have hr : IsSelfAdjoint r := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have hrr : r*r=a := CFC.sqrt_mul_sqrt_self a ha
  have hin : inner ℂ (τ.toPreGNS r) (τ.toPreGNS (x*r)) = τ (a*x) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,hr.star_eq]
    rw [htr r (x*r),mul_assoc,hrr,htr x a]
  have hh : ‖τ.toPreGNS r‖^2=(τ a).re := by
    have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS r))
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re,
      PositiveLinearMap.ofPreGNS_toPreGNS,hr.star_eq,hrr] using h
  calc
    _ = ‖inner ℂ (τ.toPreGNS r) (τ.toPreGNS (x*r))‖ := congrArg norm hin.symm
    _ ≤ ‖τ.toPreGNS r‖*‖τ.toPreGNS (x*r)‖ := norm_inner_le_norm _ _
    _ ≤ ‖τ.toPreGNS r‖*(‖x‖*‖τ.toPreGNS r‖) :=
      mul_le_mul_of_nonneg_left (preGNS_norm_mul_le τ x r) (norm_nonneg _)
    _ = (τ a).re*‖x‖ := by rw [← hh]; ring

include htr in
 
lemma trace_pair_bound (b x : A) :
    ‖τ (b*x)‖ ≤ (τ (CFC.abs b)).re * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro η hη
  let C := ‖(traceCLM τ)‖*‖x‖
  let ε := η/(C+1)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨v,hv,he,_⟩ := exists_approx_polar b ε hε
  have hdiff : ‖τ ((b-v*CFC.abs b)*x)‖ ≤ C*ε := by
    apply ((traceCLM τ).le_opNorm _).trans
    have ht := (norm_mul_le (b-v*CFC.abs b) x).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg x))
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by dsimp [C]; ring)
  have hmain : ‖τ (v*CFC.abs b*x)‖ ≤ (τ (CFC.abs b)).re * ‖x‖ := by
    have heq : τ (v*CFC.abs b*x)=τ (CFC.abs b*(x*v)) := by
      rw [mul_assoc,htr v (CFC.abs b*x),mul_assoc]
    rw [heq]
    apply (positive_weight_trace_bound τ htr _ _ (CFC.abs_nonneg b)).trans
    apply mul_le_mul_of_nonneg_left _ (τ.map_nonneg (CFC.abs_nonneg b)).1
    simpa only [mul_one] using (norm_mul_le x v).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg x))
  have hsum : τ (b*x)=τ ((b-v*CFC.abs b)*x)+τ (v*CFC.abs b*x) := by
    rw [← map_add,← add_mul,sub_add_cancel]
  rw [hsum]
  apply (norm_add_le _ _).trans
  have hεeq : ε*(C+1)=η := div_mul_cancel₀ _ (by positivity)
  linarith [add_le_add hdiff hmain]

def tracePair (b : A) : A →L[ℂ] ℂ :=
  (traceCLM τ).comp (ContinuousLinearMap.mul ℂ A b)

@[simp] lemma tracePair_apply (b x : A) : tracePair τ b x=τ (b*x) := rfl

include htr in
 

theorem norm_tracePair (b : A) : ‖tracePair τ b‖=(τ (CFC.abs b)).re := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (τ.map_nonneg (CFC.abs_nonneg b)).1
    exact trace_pair_bound τ htr b
  · apply le_of_forall_pos_le_add
    intro η hη
    let C := ‖(traceCLM τ)‖
    let ε := η/(C+1)
    have hC : 0 ≤ C := norm_nonneg _
    have hε : 0 < ε := div_pos hη (by positivity)
    obtain ⟨v,hv,_,he⟩ := exists_approx_polar b ε hε
    have hτpos := τ.map_nonneg (CFC.abs_nonneg b)
    have hτreal : (τ (CFC.abs b)).re=‖τ (CFC.abs b)‖ := by
      have heq : τ (CFC.abs b) = ((τ (CFC.abs b)).re : ℂ) := by
        exact Complex.ext rfl hτpos.2.symm
      rw [heq]
      exact (Complex.norm_of_nonneg hτpos.1).symm
    rw [hτreal]
    have hdiff : ‖τ (CFC.abs b-star v*b)‖ ≤ C*ε :=
      ((traceCLM τ).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left he hC)
    have hmain : ‖τ (star v*b)‖ ≤ ‖tracePair τ b‖ := by
      rw [htr]
      exact ((tracePair τ b).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (by simpa only [norm_star] using hv) (norm_nonneg _)).trans_eq (mul_one _))
    have hsum : τ (CFC.abs b)=τ (CFC.abs b-star v*b)+τ (star v*b) := by
      rw [← map_add,sub_add_cancel]
    rw [hsum]
    apply (norm_add_le _ _).trans
    have hεeq : ε*(C+1)=η := div_mul_cancel₀ _ (by positivity)
    linarith [add_le_add hdiff hmain]
end HochschildTraceNorm

 

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N X : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ)

omit [PartialOrder N] [StarOrderedRing N] in
lemma predual_vector_ext (z w : X) (h : ∀ a : N, e.symm a z=e.symm a w) : z=w := by
  apply (NormedSpace.inclusionInDoubleDualLi ℂ).injective
  ext f
  change f z=f w
  simpa only [e.symm_apply_apply] using h (e f)

variable (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing N] in
include hL hτ in
lemma exists_trace_vector (b : N) : ∃ z : X, ∀ a : N, e.symm a z=star (τ (star b*a)) := by
  obtain ⟨z,hz⟩ := hτ
  obtain ⟨w,hw⟩ := hL (star b) z
  refine ⟨w,fun a => ?_⟩
  rw [hz,star_star,← hw]
  rfl

def traceVector (b : N) : X := Classical.choose (exists_trace_vector e τ hL hτ b)

omit [StarOrderedRing N] in
lemma traceVector_spec (b a : N) : e.symm a (traceVector e τ hL hτ b)=star (τ (star b*a)) :=
  Classical.choose_spec (exists_trace_vector e τ hL hτ b) a

def traceVectorLinear : N →ₗ[ℂ] X where
  toFun := traceVector e τ hL hτ
  map_add' b c := by
    apply predual_vector_ext e
    intro a
    simp only [map_add,traceVector_spec,star_add,add_mul]
  map_smul' r b := by
    apply predual_vector_ext e
    intro a
    simp only [traceVector_spec,map_smul,star_smul,smul_mul_assoc,star_star,RingHom.id_apply]

omit [StarOrderedRing N] in
@[simp] lemma traceVectorLinear_apply (b : N) :
    traceVectorLinear e τ hL hτ b=traceVector e τ hL hτ b := rfl

lemma norm_traceVector (b : N) :
    ‖traceVector e τ hL hτ b‖=‖tracePair τ (star b)‖ := by
  apply le_antisymm
  · apply NormedSpace.norm_le_dual_bound ℂ _ (norm_nonneg _)
    intro f
    have hs := congrArg norm (traceVector_spec e τ hL hτ b (e f))
    simp only [e.symm_apply_apply,norm_star] at hs
    rw [hs]
    simpa only [e.norm_map,tracePair_apply] using (tracePair τ (star b)).le_opNorm (e f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    have hs := congrArg norm (traceVector_spec e τ hL hτ b a)
    simp only [norm_star] at hs
    change ‖τ (star b*a)‖ ≤ _
    rw [← hs]
    simpa only [e.symm.norm_map,mul_comm] using (e.symm a).le_opNorm (traceVector e τ hL hτ b)

omit [StarOrderedRing N] in
lemma traceVector_injective (hfaith : ∀ b : N, τ (star b*b)=0 → b=0) :
    Function.Injective (traceVectorLinear e τ hL hτ) := by
  intro b c hbc
  have hb : traceVector e τ hL hτ (b-c)=0 := by
    change traceVectorLinear e τ hL hτ (b-c)=0
    rw [map_sub,hbc,sub_self]
  apply sub_eq_zero.mp
  apply hfaith
  have hs := traceVector_spec e τ hL hτ (b-c) (b-c)
  rw [hb,map_zero] at hs
  exact star_eq_zero.mp hs.symm

end BoundedHochschild

 

open scoped ComplexOrder
namespace HochschildTraceNorm
variable {N M : Type*} [CStarAlgebra N] [CStarAlgebra M]
  [PartialOrder N] [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M]

lemma map_cstar_abs (I : N →⋆ₐ[ℂ] M) (b : N) : I (CFC.abs b)=CFC.abs (I b) := by
  symm
  apply CFC.sqrt_unique _ (map_nonneg I (CFC.abs_nonneg b))
  rw [← map_mul,CFC.abs_mul_abs,map_mul,map_star]

variable (τN : N →ₚ[ℂ] ℂ) (τM : M →ₚ[ℂ] ℂ)
  (htrN : ∀ a b : N, τN (a*b)=τN (b*a)) (htrM : ∀ a b : M, τM (a*b)=τM (b*a))

include htrN htrM in
lemma norm_tracePair_embedding (I : N →⋆ₐ[ℂ] M) (hp : ∀ a : N, τM (I a)=τN a) (b : N) :
    ‖tracePair τM (I b)‖=‖tracePair τN b‖ := by
  rw [norm_tracePair τM htrM,norm_tracePair τN htrN,← map_cstar_abs,hp]

end HochschildTraceNorm

 

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N M X : Type*} [CStarAlgebra N] [CStarAlgebra M]
  [PartialOrder N] [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
  (τN : N →ₚ[ℂ] ℂ) (τM : M →ₚ[ℂ] ℂ)
  (htrN : ∀ a b : N, τN (a*b)=τN (b*a)) (htrM : ∀ a b : M, τM (a*b)=τM (b*a))
  (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τN) (hfaith : ∀ b : N, τN (star b*b)=0 → b=0)
  (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b)

include htrN htrM hL hτ hfaith hp in
 

theorem exists_trace_expectation_value (x : M) :
    ∃ y : N, ‖y‖ ≤ ‖x‖ ∧ ∀ b : N, τN (star b*y)=τM (star (I b)*x) := by
  let J := traceVectorLinear e τN hL hτ
  let j : N ≃ₗ[ℂ] LinearMap.range J := LinearEquiv.ofInjective J
    (traceVector_injective e τN hL hτ hfaith)
  let L : N →ₗ[ℂ] ℂ := {
    toFun := fun b => star (τM (star (I b)*x))
    map_add' := fun b c => by simp only [map_add,star_add,add_mul]
    map_smul' := fun r b => by
      simp only [map_smul,star_smul,smul_mul_assoc,star_star,RingHom.id_apply] }
  let L0 : LinearMap.range J →ₗ[ℂ] ℂ := L.comp j.symm.toLinearMap
  have hbound (z : LinearMap.range J) : ‖L0 z‖ ≤ ‖x‖*‖z‖ := by
    let b := j.symm z
    have hj : J b=(z:X) := congrArg Subtype.val (j.apply_symm_apply z)
    change ‖star (τM (star (I b)*x))‖ ≤ _
    rw [norm_star,← map_star I]
    calc
      _ = ‖tracePair τM (I (star b)) x‖ := rfl
      _ ≤ ‖tracePair τM (I (star b))‖*‖x‖ := (tracePair τM (I (star b))).le_opNorm x
      _ = ‖tracePair τN (star b)‖*‖x‖ := by rw [norm_tracePair_embedding τN τM htrN htrM I hp]
      _ = ‖traceVector e τN hL hτ b‖*‖x‖ := by rw [norm_traceVector]
      _ = ‖x‖*‖z‖ := by change ‖J b‖*‖x‖=‖x‖*‖z‖; rw [hj]; exact mul_comm _ _
  let f := L0.mkContinuous ‖x‖ hbound
  obtain ⟨F,hF,hFn⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨e F,?_,fun b => ?_⟩
  · rw [e.norm_map,hFn]
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg x) _
  · apply star_injective
    rw [← traceVector_spec e τN hL hτ b (e F),e.symm_apply_apply]
    change F (J b) = _
    calc
      _ = f (j b) := hF (j b)
      _ = L (j.symm (j b)) := rfl
      _ = star (τM (star (I b)*x)) := by rw [j.symm_apply_apply]; rfl

omit [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M] in
include hfaith in
lemma trace_pair_separates (y z : N)
    (h : ∀ b : N, τN (star b*y)=τN (star b*z)) : y=z := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h,sub_self]

end BoundedHochschild

 

open scoped ComplexOrder
namespace BoundedHochschild
variable {N M X : Type*} [CStarAlgebra N] [CStarAlgebra M]
  [PartialOrder N] [StarOrderedRing N] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
  (τN : N →ₚ[ℂ] ℂ) (τM : M →ₚ[ℂ] ℂ)

 

theorem exists_expected_embedding
    (htrN : ∀ a b : N, τN (a*b)=τN (b*a)) (htrM : ∀ a b : M, τM (a*b)=τM (b*a))
    (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
    (hτ : TraceInPredual e τN) (hfaith : ∀ b : N, τN (star b*b)=0 → b=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b)
    (hI : ∀ b : N, ‖I b‖=‖b‖) :
    ∃ E : ExpectedEmbedding N M, (∀ b : N, E.includeMap b=I b) ∧
      ∀ x : M, ∀ b : N, τN (star b*E.expectMap x)=τM (star (I b)*x) := by
  choose E hEn hE using exists_trace_expectation_value e τN τM htrN htrM hL hτ hfaith I hp
  have hadd (x y : M) : E (x+y)=E x+E y := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE,mul_add,map_add,mul_add,map_add,hE,hE]
  have hsmul (r : ℂ) (x : M) : E (r • x)=r • E x := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE,mul_smul_comm,map_smul,mul_smul_comm,map_smul,hE]
  let El : M →ₗ[ℂ] N := {
    toFun := E
    map_add' := hadd
    map_smul' := hsmul }
  let Ec : M →L[ℂ] N := El.mkContinuous 1 (fun x => by change ‖E x‖ ≤ (1:ℝ)*‖x‖; simpa only [one_mul] using hEn x)
  let Ic : N →L[ℂ] M := I.toAlgHom.toLinearMap.mkContinuous 1
    (fun b => by change ‖I b‖ ≤ (1:ℝ)*‖b‖; rw [one_mul,hI])
  have hretract (a : N) : E (I a)=a := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE,← map_star I,← map_mul,hp]
  have hleft (a : N) (x : M) : E (I a*x)=a*E x := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE]
    calc
      τM (star (I b)*(I a*x)) = τM (star (I (star a*b))*x) := by
        simp only [map_mul,map_star,star_mul,star_star,mul_assoc]
      _ = τN (star (star a*b)*E x) := (hE x (star a*b)).symm
      _ = τN (star b*(a*E x)) := by simp only [star_mul,star_star,mul_assoc]
  have hright (x : M) (a : N) : E (x*I a)=E x*a := by
    apply trace_pair_separates τN hfaith
    intro b
    rw [hE]
    calc
      τM (star (I b)*(x*I a)) = τM (I a*(star (I b)*x)) := by
        rw [← mul_assoc,htrM]
      _ = τM (star (I (b*star a))*x) := by
        simp only [map_mul,map_star,star_mul,star_star,mul_assoc]
      _ = τN (star (b*star a)*E x) := (hE x (b*star a)).symm
      _ = τN (star b*(E x*a)) := by
        simp only [star_mul,star_star]
        rw [mul_assoc,htrN a (star b*E x),mul_assoc]
  refine ⟨{
    includeMap := Ic
    expectMap := Ec
    include_mul := fun a b => map_mul I a b
    include_one := map_one I
    include_star := fun a => map_star I a
    include_norm := hI
    expect_norm := hEn
    retract := hretract
    left_module := hleft
    right_module := hright },fun _ => rfl,hE⟩

end BoundedHochschild
end

end OAI
