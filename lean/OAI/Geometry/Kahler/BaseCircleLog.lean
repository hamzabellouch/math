import OAI.Geometry.Kahler.BaseDensityLowMoments

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma circle_real_char_mean {n : ℤ} (hn : n ≠ 0) :
    (∫ z, (phaseChar n z).re ∂circleMeasure)=0 := by
  have he : (∫ z, (phaseChar n z).re ∂circleMeasure) = (∫ z, phaseChar n z ∂circleMeasure).re := integral_re (compact_continuous_integrable (phaseChar_continuous n))
  rw [he,circle_char_mean,ite_eq_right hn]
  rfl

lemma circle_real_char_cos {n : ℕ} (hn : 0 < n) :
    (∫ z : Circle, (phaseChar n z).re*(z:ℂ).re ∂circleMeasure)=if n=1 then 1/2 else 0 := by
  obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hh := phase_real_moment (1:ℂ) (1:ℤ) (index+1) (by norm_num)
  have he : ∫ z : Circle, (phaseChar (index+1) z*((z:ℂ).re:ℂ)) ∂circleMeasure = if index+1=1 then (1/2:ℂ) else 0 := by
    simpa [phaseChar,eq_comm] using hh
  have hh' := congrArg Complex.re he
  have hei : (∫ z : Circle, (phaseChar (index+1) z*((z:ℂ).re:ℂ)).re ∂circleMeasure) = (∫ z : Circle, phaseChar (index+1) z*((z:ℂ).re:ℂ) ∂circleMeasure).re := integral_re (compact_continuous_integrable ((phaseChar_continuous _).mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_subtype_val))))
  rw [← hei] at hh'
  simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,apply_ite,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.zero_re,Complex.div_ofNat_re,Complex.one_re] using hh'

lemma hasSum_circle_log {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (z : Circle) :
    HasSum (fun n : ℕ => (-2*r^(n+1)/(n+1))*(phaseChar (n+1) z).re)
      (Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)) := by
  have hnorm : ‖(r:ℂ)*(z:ℂ)‖ < 1 := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,z.norm_coe,mul_one]; exact hr1
  have hh := (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hnorm)).mul_left (-2)
  have heq : -2 * (-Complex.log (1-(r:ℂ)*(z:ℂ))).re = Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) := by
    rw [Complex.neg_re,Complex.log_re,Real.log_pow]
    ring
  rw [heq] at hh
  apply hh.congr_fun
  intro n
  have he : ((r:ℂ)*(z:ℂ))^(n+1)/((n:ℂ)+1) =
      ((r^(n+1)/(n+1):ℝ):ℂ)*phaseChar ((n:ℤ)+1) z := by
    have hz : phaseChar ((n:ℤ)+1) z=(z:ℂ)^(n+1) := by
      rw [show (n:ℤ)+1=((n+1:ℕ):ℤ) by omega]
      simp only [phaseChar,zpow_natCast,Circle.coe_pow]
    rw [hz]
    push_cast
    rw [mul_pow]
    ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

lemma circle_log_moments {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) ∂circleMeasure)=0 ∧
    (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)*(z:ℂ).re ∂circleMeasure)=-r := by
  let T : ℕ → Circle → ℝ := fun n z => (-2*r^(n+1)/(n+1))*(phaseChar (n+1) z).re
  have hb : ∀ n z, |T n z| ≤ 2*r^(n+1) := by
    intro n z
    have hz : |(phaseChar (n+1) z).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq (phaseChar_norm _ _)
    have hn : (1:ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
    calc
      _ = (2*r^(n+1)/(n+1))*|(phaseChar (n+1) z).re| := by dsimp [T]; rw [abs_mul,abs_div,abs_mul,abs_pow,abs_of_nonneg hr,abs_of_pos (by positivity : (0:ℝ)<n+1)]; norm_num
      _ ≤ 2*r^(n+1)/(n+1) := by nlinarith [div_nonneg (by positivity : 0 ≤ 2*r^(n+1)) (by positivity : (0:ℝ) ≤ n+1)]
      _ ≤ 2*r^(n+1) := div_le_self (by positivity) hn
  have hsum : Summable (fun n : ℕ => 2*r^(n+1)) := by
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      (summable_geometric_of_lt_one hr hr1).mul_left (2*r)
  have hzre : ∀ z : Circle, |(z:ℂ).re| ≤ 1 := fun z => (Complex.abs_re_le_norm _).trans_eq z.norm_coe
  have hmean : HasSum (fun n => ∫ z, T n z ∂circleMeasure) (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) ∂circleMeasure) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => 2*r^(n+1))
    · intro n; exact (continuous_const.mul (Complex.continuous_re.comp (phaseChar_continuous _))).aestronglyMeasurable
    · intro n; exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb n z)
    · exact Eventually.of_forall (fun _ => hsum)
    · exact integrable_const _
    · exact Eventually.of_forall (hasSum_circle_log hr hr1)
  have hcos : HasSum (fun n => ∫ z, T n z*(z:ℂ).re ∂circleMeasure) (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)*(z:ℂ).re ∂circleMeasure) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => 2*r^(n+1))
    · intro n; exact ((continuous_const.mul (Complex.continuous_re.comp (phaseChar_continuous _))).mul (Complex.continuous_re.comp continuous_subtype_val)).aestronglyMeasurable
    · intro n; exact Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs,abs_mul]
        calc _ ≤ (2*r^(n+1))*1 := mul_le_mul (hb n z) (hzre z) (abs_nonneg _) (by positivity)
             _ = _ := mul_one _)
    · exact Eventually.of_forall (fun _ => hsum)
    · exact integrable_const _
    · exact Eventually.of_forall (fun z => (hasSum_circle_log hr hr1 z).mul_right _)
  have hm0 : ∀ n, (∫ z, T n z ∂circleMeasure)=0 := by
    intro n
    dsimp only [T]
    rw [integral_const_mul,circle_real_char_mean (by omega : (n:ℤ)+1 ≠ 0),mul_zero]
  have hc0 : ∀ n, (∫ z : Circle, T n z*(z:ℂ).re ∂circleMeasure)=if n=0 then -r else 0 := by
    intro n
    simp only [T,mul_assoc]
    rw [integral_const_mul]
    have hh := circle_real_char_cos (Nat.succ_pos n)
    simp only [Nat.succ_eq_add_one, Nat.cast_add,Nat.cast_one] at hh
    rw [hh]
    by_cases hn : n=0
    · subst n
      norm_num
      ring
    · simp [hn]
  constructor
  · simpa only [hm0,tsum_zero] using hmean.tsum_eq.symm
  · simpa only [hc0,tsum_ite_eq,mem_univ,ite_true] using hcos.tsum_eq.symm

end PinchedHartogs.BaseConstruction

end

end OAI
