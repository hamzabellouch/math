import OAI.NumberTheory.TotientAsymptotic.CoordinateErrorBudget
import OAI.NumberTheory.TotientAsymptotic.BootstrapCutoffs

namespace OAI

/-! Concrete integer parameters for the coordinate-deviation estimate. -/
noncomputable section
namespace TotientAsymptotic

def coordinateBottom (b ω : ℝ) (k : ℕ) : ℕ :=
  ⌊ω^2*b/(1000000*((k:ℝ)+2)^6)⌋₊

lemma coordinate_bottom_bounds {b ω : ℝ} {k : ℕ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6)) :
    3 ≤ coordinateBottom b ω k ∧
    (coordinateBottom b ω k:ℝ) ≤ b/1000000 ∧
    (coordinateBottom b ω k:ℝ)*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 ∧
    ω^2*b/(1000000*((k:ℝ)+2)^6)-1 < coordinateBottom b ω k := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp : 0 < ((k:ℝ)+2)^6 := by positivity
  have hp1 : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by linarith)
  have hωsq : ω^2 ≤ 1 := by nlinarith
  have ht : 0 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) := by positivity
  have hf : (coordinateBottom b ω k:ℝ) ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) := Nat.floor_le ht
  have htup : ω^2*b/(1000000*((k:ℝ)+2)^6) ≤ b/1000000 := by
    apply (div_le_iff₀ (by positivity : 0 < 1000000*((k:ℝ)+2)^6)).mpr
    have h1 := mul_le_mul_of_nonneg_right hωsq hb
    have h2 := mul_le_mul_of_nonneg_left hp1 hb
    nlinarith only [h1,h2]
  refine ⟨?_,hf.trans htup,?_,Nat.sub_one_lt_floor _⟩
  · exact (show 3 ≤ 4 by omega).trans (Nat.le_floor hlarge)
  · have hh := mul_le_mul_of_nonneg_right hf hp.le
    have he : ω^2*b/(1000000*((k:ℝ)+2)^6)*((k:ℝ)+2)^6 = ω^2*b/1000000 := by
      field_simp
    rwa [he] at hh

lemma coordinate_cutoff_bounds {b ω F : ℝ} {k : ℕ}
    (hb : 300000000 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hF : 0 ≤ F)
    (hlog : Real.log (20*b)+2 ≤ b/10000)
    (hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6))
    (hbudget : (Real.log (20*b)+9+F+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100) :
    3 ≤ coordinateBottom b ω k ∧ coordinateBottom b ω k ≤ bootstrapTop b ∧
    (bootstrapTop b:ℝ) ≤ b ∧ b-Real.log (20*b)-2 ≤ bootstrapTop b ∧
    Real.exp (bootstrapTop b) ≤ Real.exp b/(20*b) ∧
    (coordinateBottom b ω k:ℝ)*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 ∧
    ((coordinateBottom b ω k:ℝ)+1)*(k:ℝ)^2 < (1+ω)*b := by
  have hb0 : 0 < b := by linarith
  have hbot := coordinate_bottom_bounds hb0.le hω hω1 hlarge
  have htop := bootstrap_cutoff_bounds hb hlog
  have hLK : coordinateBottom b ω k ≤ bootstrapTop b := by
    have hlower : b-b/10000 ≤ (bootstrapTop b:ℝ) := by linarith [htop.2.2.2.2.1]
    exact_mod_cast (show (coordinateBottom b ω k:ℝ) ≤ bootstrapTop b by linarith [hbot.2.1])
  refine ⟨hbot.1,hLK,htop.2.2.2.1,htop.2.2.2.2.1,htop.2.2.2.2.2,hbot.2.2.1,?_⟩
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hm : 1 ≤ (k:ℝ)+2 := by linarith
  have hlin := coordinate_linear_budget hb0.le hω hω1
    (Nat.cast_nonneg (coordinateBottom b ω k)) hm hbot.2.2.1
  have hlogs : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hbase : 9*((k:ℝ)+2)^2 ≤ ω*b/100 := by
    have hmul := mul_le_mul_of_nonneg_right
      (show 9 ≤ Real.log (20*b)+9+F+Real.log (b+1) by linarith) (sq_nonneg ((k:ℝ)+2))
    exact hmul.trans hbudget
  have hsq : (k:ℝ)^2 ≤ ((k:ℝ)+2)^2 := by nlinarith
  have hlin' : (coordinateBottom b ω k:ℝ)*(k:ℝ)^2 ≤ ω*b/1000000 :=
    (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans hlin
  have hωb := mul_le_mul_of_nonneg_right hω1 hb0.le
  nlinarith only [hbase,hsq,hlin',hωb,hb0]

end TotientAsymptotic

end

end OAI
