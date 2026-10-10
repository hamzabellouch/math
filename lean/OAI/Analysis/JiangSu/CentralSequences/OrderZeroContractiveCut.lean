import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.CompletelyPositiveOperations

namespace OAI

section

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveOperations
variable {B E D : Type*} [CStarAlgebra B] [CStarAlgebra E] [CStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder E] [StarOrderedRing E]
  [PartialOrder D] [StarOrderedRing D]

lemma norm_le_of_order_zero_relation (φ : B →CP E)
    (hrel : ∀ a b, φ a*φ b=φ (a*b)*φ 1) (h1 : ‖φ 1‖≤1) (a : B) : ‖φ a‖≤‖a‖ := by
  have hsq : ‖φ a‖*‖φ a‖≤‖a‖*‖a‖ := by
    calc
      _=‖star (φ a)*φ a‖ := CStarRing.norm_star_mul_self.symm
      _=‖φ (star a*a)*φ 1‖ := by rw [←cp_map_star,hrel]
      _≤‖φ (star a*a)‖*‖φ 1‖ := norm_mul_le _ _
      _≤(‖φ 1‖*‖star a*a‖)*‖φ 1‖ := mul_le_mul_of_nonneg_right
        (PositiveLinearMap.norm_apply_le_of_nonneg (.ofClass φ) _ (star_mul_self_nonneg a)) (norm_nonneg _)
      _≤(1*‖star a*a‖)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h1 (norm_nonneg _) (by positivity)
      _=‖a‖*‖a‖ := by rw [one_mul,mul_one,CStarRing.norm_star_mul_self]
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg a) hsq

def cutoffMultiplier (t : ℝ) : ℝ := (max 1 t)⁻¹

lemma cutoffMultiplier_continuous : Continuous cutoffMultiplier := by
  exact (continuous_const.max continuous_id).inv₀ (fun t => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 t)))

lemma cutoffMultiplier_nonneg (t : ℝ) : 0≤cutoffMultiplier t := by
  exact inv_nonneg.mpr (le_trans zero_le_one (le_max_left 1 t))

lemma cutoffMultiplier_mul_le_one (t : ℝ) : cutoffMultiplier t*t≤1 := by
  change (max 1 t)⁻¹*t≤1
  rw [inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left 1 t)),mul_one]
  exact le_max_right 1 t

omit [PartialOrder D] [StarOrderedRing D] in
theorem order_zero_contractive_cut (q : E →⋆ₐ[ℂ] D) (π : B →⋆ₐ[ℂ] D) (φ : B →CP E)
    (hφ : ∀ a, q (φ a)=π a) (hrel : ∀ a b, φ a*φ b=φ (a*b)*φ 1) :
    ∃ θ : B →CP E, (∀ a, q (θ a)=π a) ∧ (∀ a, ‖θ a‖≤‖a‖) ∧
      (∀ a b, θ a*θ b=θ (a*b)*θ 1) := by
  let H := φ 1
  have hHp : 0≤H := map_nonneg φ zero_le_one
  have hHs : IsSelfAdjoint H := hHp.isSelfAdjoint
  have hHc (a : B) : Commute H (φ a) := by
    change φ 1*φ a=φ a*φ 1
    simpa only [one_mul] using hrel 1 a
  let r : E := cfc cutoffMultiplier H
  have hrp : 0≤r := cfc_nonneg (fun t _ => cutoffMultiplier_nonneg t)
  have hrc (a : B) : Commute r (φ a) :=
    (hHc a).cfc (by simpa only [hHs.star_eq] using hHc a) cutoffMultiplier
  have hqr : q r=1 := by
    change q (cfc cutoffMultiplier H)=1
    rw [q.map_cfc cutoffMultiplier H cutoffMultiplier_continuous.continuousOn]
    have hqH : q H=1 := by simpa only [_root_.map_one] using hφ 1
    rw [hqH]
    have he : (1 : D)=algebraMap ℝ D 1 := (map_one _).symm
    rw [he,cfc_algebraMap]
    norm_num [cutoffMultiplier]
  let θ := comp (conjugate (CFC.sqrt r)) φ
  have hθ (a : B) : θ a=r*φ a := by
    change star (CFC.sqrt r)*φ a*CFC.sqrt r=r*φ a
    rw [(CFC.sqrt_nonneg r).isSelfAdjoint.star_eq]
    have hc : Commute (CFC.sqrt r) (φ a) := (hrc a).cfcₙ_nnreal NNReal.sqrt
    rw [mul_assoc,←hc.eq,←mul_assoc,CFC.sqrt_mul_sqrt_self r hrp]
  have hθrel (a b : B) : θ a*θ b=θ (a*b)*θ 1 := by
    simp only [hθ]
    calc
      r*φ a*(r*φ b)=r*(r*(φ a*φ b)) := by
        rw [mul_assoc,←mul_assoc (φ a),←(hrc a).eq,mul_assoc]
      _=r*(r*(φ (a*b)*φ 1)) := by rw [hrel]
      _=r*φ (a*b)*(r*φ 1) := by
        rw [mul_assoc,←mul_assoc (φ (a*b)),←(hrc (a*b)).eq,mul_assoc]
  have hθ1 : ‖θ 1‖≤1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (map_nonneg θ zero_le_one)).mpr
    rw [hθ]
    change cfc cutoffMultiplier H*H≤1
    nth_rw 2 [←cfc_id' ℝ H]
    rw [←cfc_mul cutoffMultiplier (fun t : ℝ => t) H cutoffMultiplier_continuous.continuousOn]
    apply (cfc_le_one_iff _ H (cutoffMultiplier_continuous.mul continuous_id).continuousOn hHs).mpr
    intro t _
    exact cutoffMultiplier_mul_le_one t
  refine ⟨θ,?_,norm_le_of_order_zero_relation θ hθrel hθ1,hθrel⟩
  intro a
  rw [hθ,_root_.map_mul,hqr,hφ,one_mul]

end CompletelyPositiveOperations

end
end

end OAI
