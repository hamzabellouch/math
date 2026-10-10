import OAI.Geometry.TranslativeCovering.CoveringAsymptotics

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
lemma target_count {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((n:ℝ)*Real.log n/16) ≤ (M n:ℝ) ∧
    (M n:ℝ) ≤ 2*Real.exp ((n:ℝ)*Real.log n/16) := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have he : 1 ≤ Real.exp ((n:ℝ)*Real.log n/16) := Real.one_le_exp_iff.mpr (by positivity)
  exact ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (Real.exp_pos _).le).le.trans (by linarith only [he])⟩

lemma fine_small {H : ℝ} (hH : 0 < H) : ∀ᶠ n : ℕ in atTop,
    ∀ S : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
    (M n:ℝ)^2*(12*((n:ℝ)+1)*S^2*
      (RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1)) < 1/2 := by
  have hDp := D_pos
  have hC : 0 < 2*H/D := by positivity
  have hh := CoveringGrowth.fine_base hC
  have hd := CoveringGrowth.exponential_domination (C := 96) (δ := 1/6) (r := -2) (by norm_num) 1
  filter_upwards [hh,hd,(RadialShell.high_limit a).eventually_le_const
    (by norm_num [a,ε] : a<2),eventually_ge_atTop 8] with n hf hd hu hn S hS hSb
  have hn1 : 1 ≤ n := by omega
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hn8 : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hhi : 0 ≤ RadialShell.high a n := by unfold RadialShell.high RadialShell.η; have := a_pos; positivity
  have hbase : RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D ≤
      Real.exp (-(1/3:ℝ)*Real.log n) := by
    apply le_trans _ hf
    have hh := mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ H*Real.sqrt (Real.log n/(n:ℝ)))
    apply (div_le_div_of_nonneg_right hh D_pos.le).trans_eq
    ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D) hbase (n-1)
  rw [← Real.exp_nat_mul] at hp
  have hm := pow_le_pow_left₀ (Nat.cast_nonneg (M n)) (target_count hn1).2 2
  rw [mul_pow,← Real.exp_nat_mul] at hm
  have hs := pow_le_pow_left₀ hS hSb 2
  rw [← Real.exp_nat_mul] at hs
  have hnn : (n:ℝ)+1 ≤ 2*(n:ℝ) := by linarith only [hnp]
  calc
    _ ≤ (2:ℝ)^2*Real.exp ((2:ℕ)*((n:ℝ)*Real.log n/16))*
      (12*(2*(n:ℝ))*Real.exp ((2:ℕ)*((1/100:ℝ)*(n:ℝ)))*
        Real.exp (((n-1:ℕ):ℝ)*(-(1/3:ℝ)*Real.log n))) := by gcongr
    _ = 96*(n:ℝ)*Real.exp ((1/50:ℝ)*(n:ℝ))*
      Real.exp (((n:ℝ)/8-((n:ℝ)-1)/3)*Real.log n) := by
        rw [Nat.cast_sub hn1]
        norm_num only [Nat.cast_ofNat,Nat.cast_one]
        calc
          _ = 96*(n:ℝ)*(Real.exp (2*((n:ℝ)*Real.log n/16))*
            Real.exp (2*((1/100:ℝ)*(n:ℝ)))*Real.exp (((n:ℝ)-1)*(-(1/3:ℝ)*Real.log n))) := by ring
          _ = _ := by
            simp only [← Real.exp_add,mul_assoc]
            congr 2
            ring_nf
    _ ≤ 96*(n:ℝ)*Real.exp ((1/50:ℝ)*(n:ℝ))*
      Real.exp (-(1/6:ℝ)*((n:ℝ)*Real.log n)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith only [mul_nonneg (by linarith only [hn8] : 0 ≤ (n:ℝ)-8) hlog.le]
    _ = (96*(n:ℝ)^1*Real.exp (-(1/6:ℝ)*((n:ℝ)*Real.log n)))*
      Real.exp ((1/50:ℝ)*(n:ℝ)) := by ring
    _ ≤ Real.exp (-2*(n:ℝ))*Real.exp ((1/50:ℝ)*(n:ℝ)) := by gcongr
    _ ≤ Real.exp (-1) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hnp]
    _ < 1/2 := Real.exp_neg_one_lt_half
end NumericTail

end OAI
