import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ThresholdObstruction

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

def greedySlack (t ρ : ℝ) : ℝ := (3*t/4)*ρ^19+2*ρ^100+ρ^20+3*ρ^10000

 theorem greedyScale_of_slack {n B H s : ℕ} {t ρ b b' q : ℝ}
    (hn : 0<n) (hB : 0<B) (hH : H<B) (hs : 0<s) (hpack : ⌈2/b^2⌉₊≤H)
    (ht : 0<t) (hb : 0<b) (hpack' : 3*t<b^2/2) (hcut : 3*t<b)
    (hρ : 0<ρ) (hρ1 : ρ<1)
    (hη : (n:ℝ)^(-(1:ℝ)/100)=ρ^100) (hInv : 1/(n:ℝ)=ρ^10000)
    (hp : (B*s:ℕ)*ρ≤t/8)
    (hF : greedySlack t ρ<ρ^8) (hFt : greedySlack t ρ<t)
    (hFb : 2*t+greedySlack t ρ<b') (hFq : 2*t+2*greedySlack t ρ<q)
    (hwidth : ρ^8<t/2) : GreedyScaleBounds n B H (B*s) t ρ (2/(n:ℝ)) b b' q := by
  have hρ8 : ρ^8≤ρ := pow_le_of_le_one hρ.le hρ1.le (by decide)
  have h20 : ρ^10000≤ρ^20 := pow_le_pow_of_le_one hρ.le hρ1.le (by decide)
  have h100 : ρ^100<ρ^20 := pow_lt_pow_right_of_lt_one₀ hρ hρ1 (by decide)
  have he : 6*(B*s:ℕ)*ρ^20≤(3*t/4)*ρ^19 := by
    have h := mul_le_mul_of_nonneg_right hp (show 0≤6*ρ^19 by positivity)
    nlinarith only [h]
  have hρ20 : 0≤ρ^20 := by positivity
  have hi : 0≤ρ^10000 := by positivity
  have hη0 : 0≤ρ^100 := by positivity
  have hd : 2/(n:ℝ)=2*ρ^10000 := by rw [← hInv]; ring
  have hp0 : 0≤6*(B*s:ℕ)*ρ^20 := by positivity
  have hF0 : 0≤greedySlack t ρ := by unfold greedySlack; positivity
  have heF : 6*(B*s:ℕ)*ρ^20+2*ρ^100+ρ^20+3*ρ^10000≤greedySlack t ρ := by
    unfold greedySlack; linarith only [he]
  constructor
  · exact Nat.mul_pos hB hs
  · exact hB
  · exact hH
  · exact hpack
  · exact ht
  · exact hρ
  · positivity
  · exact hb
  · exact hpack'
  · exact hcut
  · have := heF.trans_lt hFt; linarith only [this,hρ20,hi,hη0]
  · rw [hη]; linarith only [heF,hFb,hρ20,hi]
  · rw [hη]; nlinarith only [heF,hF,hρ8,hρ20,hi,hρ]
  · exact hwidth
  · rw [hη,hd]; linarith only [heF,hF,hi]
  · rw [hη,hd]; linarith only [heF,hF,hρ8,hρ]
  · rw [hd]; linarith only [h20]
  · rw [hη]; linarith only [h100]
  · rw [hη]; linarith only [heF,hFq,hi,hη0,hp0]
  · norm_num only [Nat.cast_mul] at hp ⊢; linarith only [hp,ht]

def levelLogScale (n : ℕ) : ℝ := (n:ℝ)^kappa
def levelRho (n : ℕ) : ℝ := (n:ℝ)^(-kappa)

theorem levelRho_pos {n : ℕ} (hn : 0<n) : 0<levelRho n := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
theorem levelRho_tendsto : Tendsto levelRho atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num [kappa] : 0<kappa)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem levelRho_pow {n : ℕ} (hn : 0<n) (a : ℕ) : (levelRho n)^a=(n:ℝ)^(-((a:ℝ)*kappa)) := by
  unfold levelRho
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0:ℝ)≤n)]
  congr 1
  ring

theorem levelRho_inv {n : ℕ} (hn : 0<n) : 1/(n:ℝ)=(levelRho n)^10000 := by
  rw [levelRho_pow hn]
  norm_num [kappa,Real.rpow_neg_one]

theorem levelRho_eta {n : ℕ} (hn : 0<n) : (n:ℝ)^(-(1:ℝ)/100)=(levelRho n)^100 := by
  rw [levelRho_pow hn]; norm_num [kappa]

theorem levelLogScale_mul_rho {n : ℕ} (hn : 0<n) : levelLogScale n*levelRho n=1 := by
  unfold levelLogScale levelRho
  rw [← Real.rpow_add (by exact_mod_cast hn : (0:ℝ)<n)]
  simp

def greedyBlockCount (B : ℕ) (t : ℝ) (n : ℕ) : ℕ := ⌊(t/(8*B))*levelLogScale n⌋₊

theorem greedyBlockCount_upper {n B : ℕ} (hn : 0<n) (hB : 0<B) {t : ℝ} (ht : 0<t) :
    (B*greedyBlockCount B t n:ℕ)*levelRho n≤t/8 := by
  have hB' : (0:ℝ)<B := by exact_mod_cast hB
  have h := Nat.floor_le (show 0≤(t/(8*B))*levelLogScale n by unfold levelLogScale; positivity)
  have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hB'.le) (levelRho_pos hn).le
  have he : (B:ℝ)*((t/(8*B))*levelLogScale n)*levelRho n=t/8 := by
    rw [mul_assoc (B:ℝ),mul_assoc,levelLogScale_mul_rho hn,mul_one]
    field_simp
  simpa only [greedyBlockCount,Nat.cast_mul,he] using h'

 theorem greedySlack_tendsto (t : ℝ) : Tendsto (fun n => greedySlack t (levelRho n)) atTop (𝓝 0) := by
  have H := (((levelRho_tendsto.pow 19).const_mul (3*t/4)).add ((levelRho_tendsto.pow 100).const_mul 2)).add
    (levelRho_tendsto.pow 20) |>.add ((levelRho_tendsto.pow 10000).const_mul 3)
  simpa only [greedySlack,zero_pow (by decide : 19≠0),zero_pow (by decide : 100≠0),zero_pow (by decide : 20≠0),zero_pow (by decide : 10000≠0),mul_zero,add_zero] using H

 theorem greedySlack_div_tendsto (t : ℝ) : Tendsto (fun n => greedySlack t (levelRho n)/(levelRho n)^8) atTop (𝓝 0) := by
  have H : Tendsto (fun n => (3*t/4)*(levelRho n)^11+2*(levelRho n)^92+(levelRho n)^12+3*(levelRho n)^9992) atTop (𝓝 0) := by
    convert (((levelRho_tendsto.pow 11).const_mul (3*t/4)).add ((levelRho_tendsto.pow 92).const_mul 2)).add
      (levelRho_tendsto.pow 12) |>.add ((levelRho_tendsto.pow 9992).const_mul 3) using 1
    norm_num
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hρ := (levelRho_pos hn).ne'
  unfold greedySlack
  field_simp

end SK.Analytic

end
end

end OAI
