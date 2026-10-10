import OAI.Geometry.TranslativeCovering.NumericTail

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace NumericTail
open Filter Real SourceParameters
open scoped Topology
lemma coarse_shift {n : ℕ} (hn : 1 ≤ n)
    (hb : (RadialShell.high a n*(4*Real.sqrt ε)/D)^n ≤ Real.exp (-(n:ℝ))) :
    (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1) ≤ 16*Real.exp (-(n:ℝ)) := by
  have he : Real.sqrt ε = 1/32768 := by norm_num [ε,Real.sqrt_div,Real.sqrt_eq_iff_mul_self_eq]
  have hbase : (1:ℝ)/16 ≤ RadialShell.high a n*(4*Real.sqrt ε)/D := by
    rw [he]
    have ha := a_one
    have hη : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
    have hi : 0 ≤ a*(n:ℝ)⁻¹ := mul_nonneg a_pos.le (inv_nonneg.mpr (Nat.cast_nonneg _))
    dsimp [RadialShell.high,D]
    nlinarith only [ha,hη,hi]
  have hp := pow_nonneg (le_trans (by norm_num) hbase) (n-1)
  have hm := mul_le_mul_of_nonneg_left hbase hp
  rw [← pow_succ, Nat.sub_add_cancel hn] at hm
  linarith only [hm,hb]

lemma activity_decay {B : ℝ} (hB : 0 < B) : ∀ᶠ n : ℕ in atTop,
    ∀ Q F : ℝ,0 ≤ Q → Q ≤ B*(n:ℝ)^2 → F ≤ (n:ℝ)*Real.log n/64 →
      8*Q*Real.exp F/(M n:ℝ) ≤ Real.exp (-(3/4:ℝ)*(n:ℝ)) := by
  filter_upwards [CoveringGrowth.exponential_domination (C := 8*B) (δ := 3/64)
    (r := -(3/4)) (by norm_num) 2,eventually_ge_atTop 1] with n hn hn1 Q F hQ hQB hF
  have hm := (target_count hn1).1
  have hMp : 0 < (M n:ℝ) := (Real.exp_pos _).trans_le hm
  calc
    _ ≤ 8*(B*(n:ℝ)^2)*Real.exp ((n:ℝ)*Real.log n/64)/Real.exp ((n:ℝ)*Real.log n/16) := by gcongr
    _ = (8*B)*(n:ℝ)^2*Real.exp (-(3/64:ℝ)*((n:ℝ)*Real.log n)) := by
      rw [mul_div_assoc,← Real.exp_sub]
      congr 1 <;> ring_nf
    _ ≤ _ := hn

lemma coarse_decay {B : ℝ} (hB : 0 < B) : ∀ᶠ n : ℕ in atTop,
    ∀ S Q : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
      0 ≤ Q → Q ≤ B*(n:ℝ)^2 →
      80*(n:ℝ)⁻¹^3*Q^2*(12*((n:ℝ)+1)*S^2*
        (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)) ≤
      Real.exp (-(3/4:ℝ)*(n:ℝ)) := by
  filter_upwards [SourceParameters.coarse_base,
    CoveringGrowth.polynomial (C := 30720*B^2) (δ := 23/100) (by norm_num) 5,
    eventually_ge_atTop 1] with n hb hn hn1 S Q hS hSb hQ hQb
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hi : (n:ℝ)⁻¹^3 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hnp)
  have hs := pow_le_pow_left₀ hS hSb 2
  rw [← Real.exp_nat_mul] at hs
  have hq := pow_le_pow_left₀ hQ hQb 2
  have hbasepos := hb.1.le
  have hc := coarse_shift hn1 hb.2
  have hnn : (n:ℝ)+1 ≤ 2*(n:ℝ) := by linarith only [hnp]
  calc
    _ ≤ 80*1*(B*(n:ℝ)^2)^2*(12*(2*(n:ℝ))*
      Real.exp ((2:ℕ)*((1/100:ℝ)*(n:ℝ)))*(16*Real.exp (-(n:ℝ)))) := by gcongr
    _ = (30720*B^2)*(n:ℝ)^5*Real.exp (-(49/50:ℝ)*(n:ℝ)) := by
      calc
        _ = (30720*B^2)*(n:ℝ)^5*(Real.exp ((2:ℕ)*((1/100:ℝ)*(n:ℝ)))*Real.exp (-(n:ℝ))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; norm_num; ring
    _ ≤ Real.exp ((23/100:ℝ)*(n:ℝ))*Real.exp (-(49/50:ℝ)*(n:ℝ)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma denominator {B : ℝ} (hB : 0 < B) : ∀ᶠ n : ℕ in atTop,
    ∀ S Q F : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
      0 ≤ Q → Q ≤ B*(n:ℝ)^2 → F ≤ (n:ℝ)*Real.log n/64 →
      8*(Q*Real.exp F/(M n:ℝ)+10*(n:ℝ)⁻¹^3*Q^2*
        (12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))) ≤
      Real.exp (-(1/2:ℝ)*(n:ℝ)) := by
  filter_upwards [activity_decay hB,coarse_decay hB,
    CoveringGrowth.polynomial (C := 2) (δ := 1/4) (by norm_num) 0] with n ha hc hn S Q F hS hSb hQ hQb hF
  have h₁ := ha Q F hQ hQb hF
  have h₂ := hc S Q hS hSb hQ hQb
  have hh : 2*Real.exp (-(3/4:ℝ)*(n:ℝ)) ≤ Real.exp (-(1/2:ℝ)*(n:ℝ)) := by
    have ht := mul_le_mul_of_nonneg_right hn (Real.exp_pos (-(3/4:ℝ)*(n:ℝ))).le
    simpa only [pow_zero,mul_one,← Real.exp_add,show (1/4:ℝ)*(n:ℝ)+(-(3/4:ℝ)*(n:ℝ))=-(1/2:ℝ)*(n:ℝ) by ring] using ht
  have hs := add_le_add h₁ h₂
  have he : 8*(Q*Real.exp F/(M n:ℝ)+10*(n:ℝ)⁻¹^3*Q^2*
        (12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))) =
      8*Q*Real.exp F/(M n:ℝ)+80*(n:ℝ)⁻¹^3*Q^2*
        (12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)) := by ring
  rw [he]
  exact hs.trans (by linarith only [hh])
end NumericTail

end OAI
