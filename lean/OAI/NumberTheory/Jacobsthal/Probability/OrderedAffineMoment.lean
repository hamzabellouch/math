import OAI.NumberTheory.Jacobsthal.Estimates.ScalarFreeGate

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

noncomputable def orderedFirstMoment : ℕ → ℝ → ℝ
  | 0,_ => 0
  | n+1,b => ∫ x in (1:ℝ)..baseCutoff b,
      (x*orderedMass n x+orderedFirstMoment n x)/(max 1 x)

theorem orderedFirstMoment_continuous (n : ℕ) : Continuous (orderedFirstMoment n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun x : ℝ => (x*orderedMass n x+orderedFirstMoment n x)/(max 1 x)) :=
      ((continuous_id.mul (orderedMass_continuous n)).add ih).div
        (continuous_const.max continuous_id) (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))
    exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
      (continuous_const.max (continuous_const.min continuous_id))

theorem first_moment_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x-1)*((Real.log x)^(n+1)/((n+1).factorial:ℝ)))
      ((Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x) x := by
  have hh := ((hasDerivAt_id x).sub_const 1).mul (log_power_primitive n hx)
  convert! hh using 1
  simp only [id_eq,one_mul]
  ring

theorem orderedFirstMoment_eq (n : ℕ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    orderedFirstMoment (n+1) b=(b-1)*((Real.log b)^n/(n.factorial:ℝ)) := by
  induction n generalizing b with
  | zero =>
    rw [orderedFirstMoment,baseCutoff_on hb1 hb2]
    have he : (∫ x in (1:ℝ)..b,(x*orderedMass 0 x+orderedFirstMoment 0 x)/(max 1 x))=
        ∫ _x in (1:ℝ)..b,(1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      simp [orderedMass,orderedFirstMoment,max_eq_right hx.1,hx0]
    rw [he]
    simp
  | succ n ih =>
    rw [orderedFirstMoment,baseCutoff_on hb1 hb2]
    have he : (∫ x in (1:ℝ)..b,(x*orderedMass (n+1) x+orderedFirstMoment (n+1) x)/(max 1 x))=
        ∫ x in (1:ℝ)..b,((Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      dsimp only
      rw [orderedMass_eq (n+1) hx.1 (hx.2.trans hb2),ih hx.1 (hx.2.trans hb2),max_eq_right hx.1]
      field_simp
    rw [he]
    have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn1 : ((n+1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
    have hc : ContinuousOn (fun x : ℝ => (Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x)
        (uIcc 1 b) := by
      rw [uIcc_of_le hb1]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := simp_all)
    have hd : ∀ x ∈ uIcc (1:ℝ) b, HasDerivAt
        (fun x : ℝ => (x-1)*((Real.log x)^(n+1)/((n+1).factorial:ℝ)))
        ((Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x) x := by
      intro x hx
      rw [uIcc_of_le hb1] at hx
      exact first_moment_primitive n (by linarith [hx.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
    simp

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

noncomputable def orderedAffine (m : ℝ) (n : ℕ) (S b : ℝ) : ℝ :=
  (3*S/m-2)*orderedMass n b+(3/m)*orderedFirstMoment n b

theorem orderedAffine_continuous (m : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ => orderedAffine m n p.1 p.2) := by
  have hM : Continuous (fun p : ℝ×ℝ => orderedMass n p.2) := (orderedMass_continuous n).comp continuous_snd
  have hF : Continuous (fun p : ℝ×ℝ => orderedFirstMoment n p.2) := (orderedFirstMoment_continuous n).comp continuous_snd
  exact (((continuous_const.mul continuous_fst).div_const m).sub continuous_const |>.mul hM).add
    (continuous_const.mul hF)

theorem orderedAffine_shift_continuous (m : ℝ) (n : ℕ) (S : ℝ) :
    Continuous (fun x : ℝ => orderedAffine m n (S+x) x) := by
  have hp : Continuous (fun x : ℝ => (S+x,x)) := by fun_prop
  exact (orderedAffine_continuous m n).comp hp

theorem orderedAffine_shift_div_continuous (m : ℝ) (n : ℕ) (S : ℝ) :
    Continuous (fun x : ℝ => orderedAffine m n (S+x) x/(max 1 x)) :=
  (orderedAffine_shift_continuous m n S).div (continuous_const.max continuous_id)
    (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))

theorem orderedAffine_zero (m S b : ℝ) : orderedAffine m 0 S b=3*S/m-2 := by
  simp [orderedAffine,orderedMass,orderedFirstMoment]

theorem orderedAffine_succ (m : ℝ) (n : ℕ) (S b : ℝ) :
    orderedAffine m (n+1) S b=
      ∫ x : ℝ in 1..baseCutoff b,orderedAffine m n (S+x) x/(max 1 x) := by
  have hd : ∀ x : ℝ,max 1 x ≠ 0 := fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _))
  have hM : Continuous (fun x : ℝ => orderedMass n x/(max 1 x)) :=
    (orderedMass_continuous n).div (continuous_const.max continuous_id) hd
  have hF : Continuous (fun x : ℝ => (x*orderedMass n x+orderedFirstMoment n x)/(max 1 x)) :=
    ((continuous_id.mul (orderedMass_continuous n)).add (orderedFirstMoment_continuous n)).div
      (continuous_const.max continuous_id) hd
  change (3*S/m-2)*(∫ x : ℝ in 1..baseCutoff b,orderedMass n x/(max 1 x))+
    (3/m)*(∫ x : ℝ in 1..baseCutoff b,(x*orderedMass n x+orderedFirstMoment n x)/(max 1 x))=_
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      ((hM.const_mul (3*S/m-2)).intervalIntegrable (μ := volume) 1 _)
      ((hF.const_mul (3/m)).intervalIntegrable (μ := volume) 1 _)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [orderedAffine]
  ring

theorem orderedAffine_at_two (n : ℕ) :
    orderedAffine ((n+1:ℕ):ℝ) (n+1) 0 2=
      (3/Real.log 2-2)*(Real.log 2)^(n+1)/((n+1).factorial:ℝ) := by
  rw [orderedAffine,orderedMass_eq (n+1) (by norm_num) le_rfl,
    orderedFirstMoment_eq n (by norm_num) le_rfl]
  norm_num only [mul_zero,zero_div,zero_sub,sub_self,sub_zero,show (2:ℝ)-1=1 by norm_num,one_mul]
  rw [Nat.factorial_succ,pow_succ,Nat.cast_mul]
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  have hf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  field_simp
  ring

end ErdosOmissionTail

end

end Erdos970

end OAI
