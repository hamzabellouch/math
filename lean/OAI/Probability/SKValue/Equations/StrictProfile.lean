import Mathlib
import OAI.Probability.SKValue.Evolution.GridConvergence

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def liftProfile (ε : ℝ≥0) (k : ℕ) : HeatProfile → HeatProfile
  | [] => []
  | p::l => (p.1,p.2+ε*k)::liftProfile ε (k+1) l

lemma liftProfile_time (ε : ℝ≥0) (k : ℕ) (l : HeatProfile) :
    profileTime (liftProfile ε k l)=profileTime l := by
  induction l generalizing k with
  | nil => rfl
  | cons p l ih => simp only [liftProfile,profileTime,ih]

lemma liftProfile_lower (ε : ℝ≥0) (k : ℕ) {c : ℝ≥0} {l : HeatProfile}
    (h : ∀ p∈l,c≤p.2) : ∀ r∈liftProfile ε k l,c+ε*k≤r.2 := by
  induction l generalizing k with
  | nil => simp [liftProfile]
  | cons p l ih =>
    intro r hr
    simp only [liftProfile,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact add_le_add_left (h p (List.mem_cons_self ..)) _
    · exact (add_le_add_right (mul_le_mul_of_nonneg_left (show (k : ℝ≥0)≤(k+1 : ℕ) by exact_mod_cast (Nat.le_succ k)) (show 0≤ε from zero_le)) c).trans
        (ih (k+1) (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)) r hr)

lemma liftProfile_strict {ε : ℝ≥0} (hε : 0<ε) (k : ℕ) {l : HeatProfile}
    (h : l.Pairwise (fun p r ↦ p.2≤r.2)) :
    (liftProfile ε k l).Pairwise (fun p r ↦ p.2<r.2) := by
  induction l generalizing k with
  | nil => exact List.Pairwise.nil
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (k+1) hl⟩
    intro r hr
    have hb := liftProfile_lower ε (k+1) hp r hr
    apply lt_of_lt_of_le _ hb
    apply add_lt_add_right
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (Nat.lt_succ_self k)) hε

lemma liftProfile_positive {ε : ℝ≥0} (hε : 0<ε) {k : ℕ} (hk : 0<k) (l : HeatProfile) :
    ∀ r∈liftProfile ε k l,(0 : ℝ)<r.2 := by
  intro r hr
  have hh := liftProfile_lower ε k (c := 0) (fun p _ ↦ (show 0≤p.2 from zero_le)) r hr
  have hp : (0 : ℝ≥0)<ε*k := mul_pos hε (by exact_mod_cast hk)
  exact_mod_cast hp.trans_le (by simpa only [zero_add] using hh)

lemma liftProfile_coeff_lower (ε : ℝ≥0) (k : ℕ) (l : HeatProfile) (t : ℝ) :
    profileCoeff l t≤profileCoeff (liftProfile ε k l) t := by
  induction l generalizing k t with
  | nil => exact le_rfl
  | cons p l ih =>
    change patchTime _ _ _ t≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht,patchTime_left _ _ ht]
      simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast]
      exact le_add_of_nonneg_right (by positivity)
    · rw [patchTime_right _ _ (lt_of_not_ge ht),patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ _

lemma liftProfile_error (ε : ℝ≥0) (k : ℕ) (l : HeatProfile) (t : ℝ) :
    |profileCoeff (liftProfile ε k l) t-profileCoeff l t|≤(ε : ℝ)*(k+l.length) := by
  induction l generalizing k t with
  | nil => simp only [liftProfile,profileCoeff,sub_self,abs_zero,List.length_nil,Nat.cast_zero,add_zero]; positivity
  | cons p l ih =>
    change |patchTime _ _ _ t-patchTime _ _ _ t|≤_
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht,patchTime_left _ _ ht]
      simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,add_sub_cancel_left,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [ε.coe_nonneg,(show (0 : ℝ)≤l.length by positivity)]
    · rw [patchTime_right _ _ (lt_of_not_ge ht),patchTime_right _ _ (lt_of_not_ge ht)]
      convert ih (k+1) (t-p.1) using 1
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ring

lemma liftProfile_mono {ε : ℝ≥0} (hε : 0<ε) (k : ℕ) {l : HeatProfile}
    (h : l.Pairwise (fun p r ↦ p.2≤r.2)) :
    (liftProfile ε k l).Pairwise (fun p r ↦ p.2≤r.2) :=
  (liftProfile_strict hε k h).imp (fun h ↦ h.le)

lemma SmoothTerminal.liftProfile_bound (W : BrownianSpace) {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {l : HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2≤r.2)) (hT : profileTime l=1)
    {ε : ℝ≥0} (hε : 0<ε) (k : ℕ) (x : ℝ) :
    |profileValue ψ (liftProfile ε k l) 0 x-profileValue ψ l 0 x|≤(3/2 : ℝ)*(ε : ℝ)*(k+l.length) := by
  have hhT : profileTime (liftProfile ε k l)=1 := by rw [liftProfile_time,hT]
  have hi : IntervalIntegrable (profileCoeff l) volume 0 1 := hT ▸ profileCoeff_integrable l
  have hj : IntervalIntegrable (profileCoeff (liftProfile ε k l)) volume 0 1 := hhT ▸ profileCoeff_integrable _
  have he := elapsedValue_difference_bound (f := shiftedFiltration W 0) (brownian_increment_memLp W 0)
    hψ.lipschitz hψ.lipschitz (fun y ↦ by simp : ∀ y,|ψ y-ψ y|≤(0 : ℝ))
    (profileCoeff_measurable (liftProfile ε k l)) (profileCoeff_measurable l) hj hi (by norm_num : (0 : ℝ)≤1) (x := x)
  have hid := (hj.sub hi).abs
  have hb : (∫ t in (0 : ℝ)..1,|profileCoeff (liftProfile ε k l) t-profileCoeff l t|)≤(ε : ℝ)*(k+l.length) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..1,(ε : ℝ)*(k+l.length) :=
        intervalIntegral.integral_mono (by norm_num) hid intervalIntegrable_const (fun t ↦ liftProfile_error ε k l t)
      _ = _ := by simp
  have he1 := hψ.profile_elapsedValue W (liftProfile_mono hε k hl) hhT (show (0 : ℝ)∈Ico 0 1 by norm_num) x
  have he2 := hψ.profile_elapsedValue W hl hT (show (0 : ℝ)∈Ico 0 1 by norm_num) x
  simp only [zero_add,sub_zero] at he1 he2
  rw [he1,he2] at he
  linarith

end SKValue

end

end OAI
