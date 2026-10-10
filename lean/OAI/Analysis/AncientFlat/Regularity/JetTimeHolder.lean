import OAI.Analysis.AncientFlat.Regularity.InterpolationAlgebra

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma time_lower_holder (j : ℕ) (hj : j≤3) (u ut : ℝ → V → E)
    (s t R q U M α : ℝ) (hq : 0<q) (hU : 0≤U) (hM : 0≤M)
    (hα : 0≤α) (hα1 : α≤1)
    (hs : ContDiff ℝ 4 (u s)) (ht : ContDiff ℝ 4 (u t))
    (hdt : ∀ r∈uIcc s t, ∀ x, ‖x‖<R → HasDerivAt (fun r => u r x) (ut r x) r)
    (hUt : ∀ r∈uIcc s t, ∀ x, ‖x‖<R → ‖ut r x‖≤M)
    (hus : ∀ y, ‖y‖<R → ‖u s y‖≤U)
    (hut : ∀ y, ‖y‖<R → ‖u t y‖≤U)
    (hDs : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 (u s) y‖≤M)
    (hDt : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 (u t) y‖≤M)
    (x : V) (hx : ‖x‖+12*q<R) :
    ‖iteratedFDeriv ℝ j (u t) x-iteratedFDeriv ℝ j (u s) x‖≤
      66*(U/q^j+q^(4-j)*M)/q^α*(|t-s|^((1:ℝ)/4))^α := by
  by_cases hst : t=s
  · subst t
    simp only [sub_self,norm_zero]
    positivity
  let d := |t-s|^((1:ℝ)/4)
  have hd : 0<d := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hst)) _
  have hd4 : d^4=|t-s| := by
    rw [←Real.rpow_mul_natCast (abs_nonneg (t-s)) ((1:ℝ)/4) 4]
    norm_num
  let B := U/q^j+q^(4-j)*M
  have hB : 0≤B := by dsimp [B]; positivity
  change _≤66*B/q^α*d^α
  by_cases hdq : d≤q
  · have hb := time_lower_jet j hj u ut s t R d M hd hM hs ht hdt hUt hDs hDt x (by linarith)
    have heq : |t-s| /d^j=d^(4-j) := by
      rw [←hd4,show (4:ℕ)=(4-j)+j by omega,pow_add,mul_div_cancel_right₀ _ (pow_ne_zero _ hd.ne')]
      congr 1
      omega
    rw [heq] at hb
    have hp := small_scale_power (4-j) (by omega) d q α hd.le hq hdq hα hα1
    calc
      _≤66*d^(4-j)*M := by linarith [hb]
      _≤66*(q^(4-j)/q^α*d^α)*M := by gcongr
      _≤66*B/q^α*d^α := by
        have hle : q^(4-j)*M≤B := by dsimp [B]; exact le_add_of_nonneg_left (by positivity)
        calc
          _=66*(q^(4-j)*M)/q^α*d^α := by ring
          _≤_ := by gcongr
  · have hsB := lower_jet_bound j hj (u s) hs x R q U M hq hU hM (by linarith) hus hDs
    have htB := lower_jet_bound j hj (u t) ht x R q U M hq hU hM (by linarith) hut hDt
    have hb : ‖iteratedFDeriv ℝ j (u t) x-iteratedFDeriv ℝ j (u s) x‖≤44*B :=
      (norm_sub_le _ _).trans (by dsimp [B]; linarith)
    have hp : q^α≤d^α := Real.rpow_le_rpow hq.le (le_of_not_ge hdq) hα
    have hqa : q^α≠0 := (Real.rpow_pos_of_pos hq α).ne'
    calc
      _≤44*B := hb
      _≤66*B := by nlinarith
      _=(66*B/q^α)*q^α := by field_simp
      _≤_ := mul_le_mul_of_nonneg_left hp (by positivity)
end ParabolicInterpolation

end

end OAI
