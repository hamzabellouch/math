import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.AllWindowCost

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Real
noncomputable section

lemma windowCodeBudget_coarse {σ q P b Cℓ : ℝ} {w H l : ℕ}
    (hσ : 1≤σ) (hq : σ≤q) (hP : 1≤P) (hH : 1≤H)
    (hb : b≤P) (hmeta : 2*Real.log (320/((9:ℝ)/100000)+320)≤P)
    (hlog4 : Real.log 4≤σ) (hC : 0≤Cℓ) (hl : Real.log (l+1)≤Cℓ*σ) :
    windowCodeBudget σ q P b w H+(w+1)*Real.log (l+1)≤
      (5+7*nodeChargeConstant+Cℓ)*q*(P*H*(σ+w*P)) := by
  have hs : 0≤σ := by linarith
  have hp : 0≤P := by linarith
  have hq0 : 0≤q := by linarith
  have hh : (1:ℝ)≤H := by exact_mod_cast hH
  have hh0 : (0:ℝ)≤H := by positivity
  have hn := nodeChargeConstant_nonneg
  have hl2 : Real.log 2≤1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
  have hx : (w:ℝ)+1≤σ+w*P := by nlinarith [mul_le_mul_of_nonneg_left hP (show (0:ℝ)≤w by positivity)]
  have hmul : 1≤q*P*H := by
    have hq1 : 1≤q := hσ.trans hq
    calc
      1 = (1:ℝ)*1*1 := by norm_num
      _ ≤ q*P*H := by gcongr
  have hmulσ : σ≤q*P*H := by
    calc
      σ≤q := hq
      _ =q*1*1 := by ring
      _ ≤q*P*H := by gcongr
  let A:=q*P*H*(σ+w*P)
  have ha0 : 0≤A := by dsimp [A];positivity
  have ha : σ+w*P≤A := by
    dsimp [A]
    exact le_mul_of_one_le_left (by positivity) hmul
  have hwA : (w:ℝ)≤A := by linarith
  have hhA : Real.log (w+1)≤A := by
    have hh' := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(w:ℝ)+1)
    exact (show Real.log (w+1)≤(w:ℝ) by linarith).trans hwA
  have hfirst : nodeChargeConstant*q*P*H*
      (3*σ+Real.log 4+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*w)≤4*nodeChargeConstant*A := by
    calc
      _ ≤ nodeChargeConstant*q*P*H*(4*σ+3*P*w) := by gcongr <;> nlinarith
      _ ≤ nodeChargeConstant*q*P*H*(4*(σ+w*P)) := by gcongr; nlinarith
      _ = _ := by dsimp [A];ring
  have hsecond : (Real.log 2+nodeChargeConstant*q*P*(b+1+P))*w≤
      (1+3*nodeChargeConstant)*A := by
    have hw : nodeChargeConstant*q*P*(3*P)*w≤3*nodeChargeConstant*A := by
      calc
        _ =3*nodeChargeConstant*(q*P*(w*P)) := by ring
        _ =3*nodeChargeConstant*(q*P*(1:ℝ)*(w*P)) := by ring
        _ ≤3*nodeChargeConstant*(q*P*H*(σ+w*P)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity))
            (by linarith) (by positivity) (by positivity)
    calc
      _ ≤ (1+nodeChargeConstant*q*P*(3*P))*w := by gcongr; linarith
      _ = w+nodeChargeConstant*q*P*(3*P)*w := by ring
      _ ≤ A+3*nodeChargeConstant*A := add_le_add hwA hw
      _ = _ := by ring
  have hstatus : (2*(w:ℝ)+1)*Real.log 2≤3*A := by
    calc
      _ ≤2*(w:ℝ)+1 := mul_le_of_le_one_right (by positivity) hl2
      _ ≤3*((w:ℝ)+1) := by linarith
      _ ≤3*A := by linarith
  have hassign : ((w:ℝ)+1)*Real.log (l+1)≤Cℓ*A := by
    calc
      _ ≤((w:ℝ)+1)*(Cℓ*σ) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ =Cℓ*(σ*((w:ℝ)+1)) := by ring
      _ ≤Cℓ*(q*P*H*(σ+w*P)) := by gcongr
  have ht:=add_le_add (add_le_add (add_le_add hhA (add_le_add hfirst hsecond)) hstatus) hassign
  exact ht.trans_eq (by dsimp [A];ring)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
