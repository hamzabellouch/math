import Mathlib
import OAI.Analysis.WeakInfiniteness.LocalConnection

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

def boundedCutFunction (r s : ℝ) : ℝ := Real.sqrt (max (s-r) 0) / max r s

lemma continuous_boundedCutFunction {r : ℝ} (hr : 0 < r) :
    Continuous (boundedCutFunction r) := by
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro s
    exact ne_of_gt (hr.trans_le (le_max_left _ _))

lemma boundedCutFunction_zero {r : ℝ} (hr : 0 < r) : boundedCutFunction r 0=0 := by
  simp only [boundedCutFunction,zero_sub,max_eq_right (neg_nonpos.mpr hr.le),Real.sqrt_zero,zero_div]

lemma boundedCutFunction_mul {r : ℝ} (hr : 0 < r) (s : ℝ) :
    s*boundedCutFunction r s=Real.sqrt (max (s-r) 0) := by
  by_cases hs : s ≤ r
  · simp only [boundedCutFunction,max_eq_right (sub_nonpos.mpr hs),Real.sqrt_zero,zero_div,mul_zero]
  · have hrs : r ≤ s := (lt_of_not_ge hs).le
    have hs0 : s ≠ 0 := ne_of_gt (hr.trans_le hrs)
    simp only [boundedCutFunction,max_eq_right hrs]
    field_simp

lemma boundedCutFunction_square_le {r : ℝ} (hr : 0 < r) (s : ℝ) :
    r^2*(boundedCutFunction r s)^2 ≤ (s*boundedCutFunction r s)^2 := by
  by_cases hs : s ≤ r
  · simp only [boundedCutFunction,max_eq_right (sub_nonpos.mpr hs),Real.sqrt_zero,zero_div,mul_zero]
    norm_num
  · have hrs : r ≤ s := (lt_of_not_ge hs).le
    have hsq : r^2 ≤ s^2 := sq_le_sq₀ hr.le (hr.le.trans hrs) |>.mpr hrs
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (boundedCutFunction r s))]

section General

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma boundedCutFunction_cfc_product {Q : A} (hQ : 0 ≤ Q) {r : ℝ} (hr : 0 < r) :
    Q*cfcₙ (boundedCutFunction r) Q=CFC.sqrt (positiveCut r Q) := by
  rw [CFC.sqrt_eq_real_sqrt _ (positiveCut_nonneg r Q),positiveCut]
  rw [← cfcₙ_comp Real.sqrt (fun s : ℝ => max (s-r) 0) Q
    Real.continuous_sqrt.continuousOn Real.sqrt_zero (by fun_prop)
    (by simpa using max_eq_right (neg_nonpos.mpr hr.le))]
  have hq : Q=cfcₙ (fun s : ℝ => s) Q := (cfcₙ_id' ℝ Q hQ.isSelfAdjoint).symm
  rw [hq] at ⊢
  rw [← hq]
  conv_lhs => arg 1; rw [hq]
  rw [← cfcₙ_mul (fun s : ℝ => s) (boundedCutFunction r) Q
    continuous_id.continuousOn rfl (continuous_boundedCutFunction hr).continuousOn
    (boundedCutFunction_zero hr)]
  apply cfcₙ_congr
  intro s _
  exact boundedCutFunction_mul hr s

lemma boundedCutFunction_cfc_norm {Q : A} (hQ : 0 ≤ Q) {r : ℝ} (hr : 0 < r) (v : A) :
    r*‖cfcₙ (boundedCutFunction r) Q*v‖ ≤ ‖Q*(cfcₙ (boundedCutFunction r) Q*v)‖ := by
  let j := cfcₙ (boundedCutFunction r) Q
  have hj : IsSelfAdjoint j := cfcₙ_predicate _ _
  have hqj : IsSelfAdjoint (Q*j) := by
    rw [boundedCutFunction_cfc_product hQ hr]
    exact (CFC.sqrt_nonneg _).isSelfAdjoint
  have hle : r^2 • (j*j) ≤ (Q*j)*(Q*j) := by
    have hjj : j*j=cfcₙ (fun s : ℝ => (boundedCutFunction r s)^2) Q := by
      simp only [pow_two]
      exact (cfcₙ_mul _ _ _ (continuous_boundedCutFunction hr).continuousOn
        (boundedCutFunction_zero hr) (continuous_boundedCutFunction hr).continuousOn
        (boundedCutFunction_zero hr)).symm
    have hprod : Q*j=cfcₙ (fun s : ℝ => s*boundedCutFunction r s) Q := by
      conv_lhs => arg 1; rw [(cfcₙ_id' ℝ Q hQ.isSelfAdjoint).symm]
      exact (cfcₙ_mul _ _ _ continuous_id.continuousOn rfl
        (continuous_boundedCutFunction hr).continuousOn (boundedCutFunction_zero hr)).symm
    have hf := continuous_boundedCutFunction hr
    rw [hjj,hprod,← cfcₙ_smul (r^2) (fun s : ℝ => boundedCutFunction r s ^ 2) Q (hf.pow 2).continuousOn
      (by simp [boundedCutFunction_zero hr]),← cfcₙ_mul
        (fun s : ℝ => s*boundedCutFunction r s) (fun s : ℝ => s*boundedCutFunction r s) Q
        (continuous_id.mul hf).continuousOn (by simp) (continuous_id.mul hf).continuousOn (by simp)]
    exact cfcₙ_mono (fun s _ => by simpa only [smul_eq_mul,pow_two] using boundedCutFunction_square_le hr s)
      ((hf.pow 2).const_smul (r^2)).continuousOn
      ((continuous_id.mul hf).mul (continuous_id.mul hf)).continuousOn
      (by simp [boundedCutFunction_zero hr]) (by simp)
  have ho := star_left_conjugate_le_conjugate hle v
  have he1 : star v*(r^2 • (j*j))*v=r^2 • (star (j*v)*(j*v)) := by
    simp only [star_mul,hj.star_eq,mul_smul_comm,smul_mul_assoc,mul_assoc]
  have he2 : star v*((Q*j)*(Q*j))*v=star (Q*(j*v))*(Q*(j*v)) := by
    calc
      _=star ((Q*j)*v)*((Q*j)*v) := by
        rw [star_mul (Q*j) v,hqj.star_eq]
        simp only [mul_assoc]
      _=_ := by simp only [mul_assoc]
  rw [he1,he2] at ho
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg ho
    (smul_nonneg (sq_nonneg r) (star_mul_self_nonneg (j*v)))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r),
    CStarRing.norm_star_mul_self,CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (j*v),norm_nonneg (Q*(j*v))]

lemma exists_bounded_cut_implementation {Q c : A} (hQ : 0 ≤ Q) (_hc : 0 ≤ c)
    (hcn : ‖c‖ ≤ 1) {m : ℝ} (hm : 0 < m)
    (hcomp : ElementCuntzSubequiv c (positiveCut (m/2) Q)) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ x : A, ‖star (Q*x)*(Q*x)-c‖ < δ ∧ ‖Q*x‖ ≤ 2 ∧ ‖x‖ ≤ 4/m := by
  obtain ⟨v,hv⟩ := elementCuntzSubequiv_iff.mp hcomp δ hδ
  let x := cfcₙ (boundedCutFunction (m/2)) Q*v
  have hprod : Q*x=CFC.sqrt (positiveCut (m/2) Q)*v := by
    rw [← mul_assoc,boundedCutFunction_cfc_product hQ (by positivity)]
  have he : star (Q*x)*(Q*x)=star v*positiveCut (m/2) Q*v := by
    rw [hprod,star_mul,(CFC.sqrt_nonneg (positiveCut (m/2) Q)).star_eq]
    calc
      (star v*CFC.sqrt (positiveCut (m/2) Q))*(CFC.sqrt (positiveCut (m/2) Q)*v)=
        star v*(CFC.sqrt (positiveCut (m/2) Q)*CFC.sqrt (positiveCut (m/2) Q))*v := by noncomm_ring
      _=star v*positiveCut (m/2) Q*v := by rw [CFC.sqrt_mul_sqrt_self _ (positiveCut_nonneg _ _)]
  have hxerr : ‖star (Q*x)*(Q*x)-c‖<δ := by rwa [he]
  have hxnorm : ‖Q*x‖ ≤ 2 := by
    have hn : ‖star (Q*x)*(Q*x)‖ ≤ ‖star (Q*x)*(Q*x)-c‖+‖c‖ := by
      calc
        _=‖(star (Q*x)*(Q*x)-c)+c‖ := by rw [sub_add_cancel]
        _≤_ := norm_add_le _ _
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg (Q*x)]
  refine ⟨x,hxerr,hxnorm,?_⟩
  have hn := boundedCutFunction_cfc_norm hQ (show 0 < m/2 by positivity) v
  change m/2*‖x‖ ≤ ‖Q*x‖ at hn
  apply (le_div_iff₀ hm).mpr
  nlinarith

end General

end

end WeakPureInfiniteness
end

end OAI
