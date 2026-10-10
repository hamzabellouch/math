import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressurePrimitive
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPlateauPotential

namespace OAI

/-! The limiting weighted pressure primitive is exactly that of the radial step b·1_[0,l]. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_step_primitive (R l b : ℝ) (hl : 0 < l) (hlR : l ≤ R)
    (A D V : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hV : ContinuousOn V (Icc 0 R))
    (hD0 : EqOn D (fun _ => 0) (Icc 0 l))
    (hVA : ∀ r ∈ Icc 0 l, V r*A r=b)
    (hDE : ∀ r ∈ Ioo l R, HasDerivAt D (-11/r*D r-V r*A r) r) :
    ∀ r ∈ Icc 0 R, r^11*D r+(∫ t in (0 : ℝ)..r, V t*A t*t^11)=
      b/12*(min r l)^12 := by
  have hint (a c : ℝ) (ha : a ∈ Icc 0 R) (hc : c ∈ Icc 0 R) (hac : a ≤ c) :
      IntervalIntegrable (fun t => V t*A t*t^11) volume a c :=
    ContinuousOn.intervalIntegrable_of_Icc hac
      (((hV.mul hA.continuousOn).mul (continuous_id.pow 11).continuousOn).mono
        (fun t ht => ⟨ha.1.trans ht.1,ht.2.trans hc.2⟩))
  have hcore (r : ℝ) (hr : r ∈ Icc 0 l) :
      (∫ t in (0 : ℝ)..r, V t*A t*t^11)=b/12*r^12 := by
    have heq : (∫ t in (0 : ℝ)..r, V t*A t*t^11)=∫ t in (0 : ℝ)..r, b*t^11 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Icc 0 l := ⟨(uIcc_of_le hr.1 ▸ ht).1,(uIcc_of_le hr.1 ▸ ht).2.trans hr.2⟩
      change V t*A t*t^11=b*t^11
      rw [hVA t htI]
    rw [heq,intervalIntegral.integral_const_mul,integral_pow]
    norm_num
    ring
  intro r hr
  by_cases hrl : r ≤ l
  · rw [hD0 ⟨hr.1,hrl⟩,hcore r ⟨hr.1,hrl⟩,min_eq_left hrl]
    ring
  · have hlr : l ≤ r := (not_le.mp hrl).le
    have hder : ∀ t ∈ Ioo l r, HasDerivAt (fun s : ℝ => s^11*D s) (-V t*A t*t^11) t := by
      intro t ht
      have htne : t ≠ 0 := ne_of_gt (hl.trans ht.1)
      have h := ((hasDerivAt_id t).pow 11).mul (hDE t ⟨ht.1,ht.2.trans_le hr.2⟩)
      convert h using 1
      · rfl
      · simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one]
        field_simp [htne]
        ring
    have hi := hint l r ⟨hl.le,hlR⟩ hr hlr
    have hin : IntervalIntegrable (fun t => -V t*A t*t^11) volume l r := by
      have heq : (fun t => -V t*A t*t^11)=-(fun t => V t*A t*t^11) := by
        funext t
        simp only [Pi.neg_apply,neg_mul]
      rw [heq]
      exact hi.neg
    have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun s : ℝ => s^11*D s) hlr
      ((continuous_id.pow 11).mul hD).continuousOn hder hin
    have hIeq : (∫ t in l..r, -V t*A t*t^11)=-(∫ t in l..r, V t*A t*t^11) := by
      simp only [neg_mul,intervalIntegral.integral_neg]
    rw [hIeq,hD0 ⟨hl.le,le_rfl⟩,mul_zero,sub_zero] at hI
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 l ⟨le_rfl,hl.le.trans hlR⟩ ⟨hl.le,hlR⟩ hl.le) hi
    rw [hcore l ⟨hl.le,le_rfl⟩] at hsplit
    rw [min_eq_right hlr]
    linarith

end DefocusingNLS

end OAI
