import Mathlib
import OAI.Analysis.BoundedHochschild.NormalMultiplication

namespace OAI

/-! Primitives on operator algebras and polar partial isometries. -/

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
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
namespace BoundedHochschild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
def rankOneColumn (φ : StrongDual ℂ E) : E →L[ℂ] (E →L[ℂ] E) :=
  ContinuousLinearMap.smulRightL ℂ E E φ

@[simp] lemma rankOneColumn_apply (φ : StrongDual ℂ E) (x y : E) :
    rankOneColumn φ x y = φ y • x := rfl

lemma mul_rankOneColumn (φ : StrongDual ℂ E) (a : E →L[ℂ] E) (y : E) :
    a * rankOneColumn φ y = rankOneColumn φ (a y) := by
  ext z
  simp

 

def columnEvaluate (φ : StrongDual ℂ E) (x : E) :
    ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (E →L[ℂ] E) E ((ContinuousLinearMap.apply ℂ E) x)).comp
    ((ContinuousLinearMap.compL ℂ E (E →L[ℂ] E) (E →L[ℂ] E)).flip (rankOneColumn φ))

@[simp] lemma columnEvaluate_apply (φ : StrongDual ℂ E) (x y : E)
    (F : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) :
    columnEvaluate φ x F y = F (rankOneColumn φ y) x := rfl

 
def operatorHomotopy (φ : StrongDual ℂ E) (x : E) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) : Cochain (E →L[ℂ] E) n :=
  (columnEvaluate φ x).compContinuousMultilinearMap f.curryRight

@[simp] lemma operatorHomotopy_apply (φ : StrongDual ℂ E) (x y : E) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) (v : Fin n → (E →L[ℂ] E)) :
    operatorHomotopy φ x f v y = f (Fin.snoc v (rankOneColumn φ y)) x := rfl

lemma operatorHomotopy_cocycle (φ : StrongDual ℂ E) (x : E) (hφ : φ x=1) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1))
    (hf : ∀ v, differentialValue f v=0) (v : Fin (n+1) → (E →L[ℂ] E)) :
    differentialValue (operatorHomotopy φ x f) v = ((-1:ℂ)^(n+1)) • f v := by
  have hzero : differentialValue (operatorHomotopy φ x f) v +
      ((-1:ℂ)^(n+2)) • f v=0 := by
    ext y
    have h := congrArg (fun a : E →L[ℂ] E => a x) (hf (Fin.snoc v (rankOneColumn φ y)))
    rw [differentialValue_snoc] at h
    simpa only [differentialValue, add_apply,
      sum_apply, smul_apply,
      zero_apply, mul_apply_eq_comp, operatorHomotopy_apply,
      mul_rankOneColumn, rankOneColumn_apply, hφ, one_smul] using h
  have hp : (-1:ℂ)^(n+2) = -((-1:ℂ)^(n+1)) := by
    rw [show n+2=(n+1)+1 by omega, pow_succ]
    ring
  rw [hp,neg_smul] at hzero
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hzero)

lemma operatorHomotopy_norm (φ : StrongDual ℂ E) (x : E) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) :
    ‖operatorHomotopy φ x f‖ ≤ ‖f‖ * ‖φ‖ * ‖x‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  calc
    ‖operatorHomotopy φ x f v y‖ ≤ ‖f (Fin.snoc v (rankOneColumn φ y))‖ * ‖x‖ :=
      (f (Fin.snoc v (rankOneColumn φ y))).le_opNorm x
    _ ≤ (‖f‖ * (∏ i, ‖v i‖) * ‖rankOneColumn φ y‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (f.norm_map_snoc_le v (rankOneColumn φ y)) (norm_nonneg _)
    _ = ((‖f‖ * ‖φ‖ * ‖x‖) * ∏ i, ‖v i‖) * ‖y‖ := by
      change (‖f‖ * (∏ i, ‖v i‖) * ‖φ.smulRight y‖) * ‖x‖ = _
      rw [ContinuousLinearMap.norm_smulRight_apply]
      ring

 

theorem primitive_on_operators_of_dual_pair
    (φ : StrongDual ℂ E) (x : E) (hφ : φ x=1) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain (E →L[ℂ] E) n, ‖g‖ ≤ ‖f‖ * ‖φ‖ * ‖x‖ ∧
      ∀ v, differentialValue g v=f v := by
  refine ⟨((-1:ℂ)^(n+1)) • operatorHomotopy φ x f, ?_, ?_⟩
  · simpa only [norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      using operatorHomotopy_norm φ x f
  · intro v
    rw [differentialValue_smul, operatorHomotopy_cocycle φ x hφ f hf v, smul_smul]
    have hp : (-1:ℂ)^(n+1)*(-1:ℂ)^(n+1)=1 := by
      rw [← mul_pow]
      simp
    rw [hp,one_smul]

 

theorem primitive_on_operators {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain (E →L[ℂ] E) n, ‖g‖ ≤ ‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  classical
  by_cases hE : Nontrivial E
  · let := hE
    let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    obtain ⟨x,hx⟩ := exists_norm_eq E (show (0:ℝ) ≤ 1 by norm_num)
    obtain ⟨φ,hφn,hφ⟩ := exists_dual_vector ℂ x (by rw [hx]; norm_num)
    obtain ⟨g,hgn,hg⟩ := primitive_on_operators_of_dual_pair φ x
      (by simpa [hx] using hφ) f hf
    exact ⟨g,by simpa only [hx,hφn,mul_one] using hgn,hg⟩
  · let : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    exact ⟨0,by simp,fun _ => Subsingleton.elim _ _⟩

end BoundedHochschild

 

open Filter Topology
namespace HochschildPolar
open BoundedHochschild HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
 

theorem exists_polar_contraction (b : M) :
    ∃ v : M, ‖v‖ ≤ 1 ∧ b=v*CFC.abs b ∧ CFC.abs b=star v*b := by
  classical
  have hpos (n : ℕ) : 0 < (1:ℝ)/((n:ℝ)+1) := by positivity
  choose v hv hleft hright using
    fun n : ℕ => HochschildTraceNorm.exists_approx_polar b _ (hpos n)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨w,hw,ht⟩ := exists_predual_ultralimit e U v 1 hv
  have hε : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n => v n*CFC.abs b) atTop (𝓝 b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hleft n
  have hr : Tendsto (fun n => star (v n)*b) atTop (𝓝 (CFC.abs b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hright n
  exact ⟨w,hw,
    predual_tendsto_unique e (predual_tendsto_of_norm e (hl.mono_left hU))
      (predual_tendsto_mul_right e _ ht),
    predual_tendsto_unique e (predual_tendsto_of_norm e (hr.mono_left hU))
      (predual_tendsto_mul_right e _ (predual_tendsto_star e ht))⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma support_right_annihilate {a p : M} (hp : IsSupportProjection a p)
    (ha : IsSelfAdjoint a) {x : M} (hx : x*a=0) : x*p=0 := by
  have hh := hp.annihilate (star x) (by
    simpa only [star_mul,ha.star_eq,star_zero] using congrArg star hx)
  simpa only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq,star_zero]
    using congrArg star hh

include e in
 

theorem exists_polar_partial_isometry (b : M) :
    ∃ v p q : M, IsSupportProjection (CFC.abs b) p ∧
      star v*v=p ∧ v*star v=q ∧ IsStarProjection q ∧ b=v*CFC.abs b ∧
      v*p=v ∧ q*b=b := by
  obtain ⟨w,hw,hb,ha⟩ := exists_polar_contraction e b
  obtain ⟨p,hp⟩ := HochschildSakai.exists_support_projection e (CFC.abs b) (CFC.abs_nonneg b)
  let v := w*p
  have hvp : v*p=v := by
    dsimp [v]
    rw [mul_assoc,hp.proj.isIdempotentElem.eq]
  have hvb : v*CFC.abs b=b := by
    dsimp [v]
    rw [mul_assoc,hp.left,← hb]
  have hv : star v*b=CFC.abs b := by
    dsimp [v]
    rw [star_mul,hp.proj.isSelfAdjoint.star_eq,mul_assoc,← ha,hp.left]
  have hinit : star v*v=p := by
    have hz : (star v*v-p)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,hvb,hv,hp.left,sub_self]
    have hh := support_right_annihilate hp (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [sub_mul,mul_assoc,hvp,hp.proj.isIdempotentElem.eq,sub_eq_zero] at hh
    exact hh
  have hfinal : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc
        _ = v*(star v*v)*star v := by simp only [mul_assoc]
        _ = v*star v := by rw [hinit,hvp]
    · exact IsSelfAdjoint.mul_star_self v
  refine ⟨v,p,v*star v,hp,hinit,rfl,hfinal,hvb.symm,hvp,?_⟩
  rw [mul_assoc,hv,hvb]

end HochschildPolar
end

end OAI
