import OAI.NumberTheory.TotientAsymptotic.DyadicValueBounds

namespace OAI

/-! Integer cutoffs on the unit log-log grid used in Ford's counting argument. -/
noncomputable section
namespace TotientAsymptotic

def loglogCutoff (b : ℝ) : ℕ := ⌊Real.exp (Real.exp b)⌋₊

lemma loglogCutoff_mono : Monotone loglogCutoff := by
  intro b c hbc
  exact Nat.floor_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hbc))

lemma loglogCutoff_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ loglogCutoff b ∧ b-1 ≤ B (loglogCutoff b) ∧ B (loglogCutoff b) ≤ b ∧
      Real.log (loglogCutoff b) ≤ Real.exp b := by
  have he : 3 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have he4 : 4 ≤ Real.exp (Real.exp b) := by linarith [Real.add_one_le_exp (Real.exp b)]
  have hf := log_floor_lower he4
  change 2 ≤ loglogCutoff b ∧ _ at hf
  have hn1 : (1:ℝ) < loglogCutoff b := by exact_mod_cast (show 1 < loglogCutoff b by omega)
  have hl0 : 0 < Real.log (loglogCutoff b) := Real.log_pos hn1
  have hlu : Real.log (loglogCutoff b) ≤ Real.exp b := by
    have hh := Real.log_le_log (by linarith : (0:ℝ)<loglogCutoff b)
      (Nat.floor_le (Real.exp_pos (Real.exp b)).le)
    simpa only [Real.log_exp] using hh
  have hll : Real.exp b/2 ≤ Real.log (loglogCutoff b) := by
    simpa only [Real.log_exp,loglogCutoff] using hf.2
  have hBl : b-Real.log 2 ≤ B (loglogCutoff b) := by
    have hh := Real.log_le_log (by positivity : 0 < Real.exp b/2) hll
    simpa only [Real.log_div (Real.exp_ne_zero b) (by norm_num : (2:ℝ)≠0),Real.log_exp,B] using hh
  have hl2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hBu : B (loglogCutoff b) ≤ b := by
    have hh := Real.log_le_log hl0 hlu
    simpa only [B,Real.log_exp] using hh
  exact ⟨hf.1,by linarith,hBu,hlu⟩

lemma loglogCutoff_lt_of_lt_B {b : ℝ} {p : ℕ} (hp : 1 < p) (hb : b < B p) :
    loglogCutoff b < p := by
  have hpR : (1:ℝ) < p := by exact_mod_cast hp
  have he := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hb)
  have hlog : 0 < Real.log p := Real.log_pos hpR
  rw [B,Real.exp_log hlog,Real.exp_log (by linarith : (0:ℝ)<p)] at he
  have hf : (loglogCutoff b:ℝ) ≤ Real.exp (Real.exp b) := Nat.floor_le (Real.exp_pos _).le
  exact_mod_cast hf.trans_lt he

lemma loglog_grid_index_bounds {t : ℝ} (ht : 4 ≤ t) :
    let k := ⌊t⌋₊-1
    2 ≤ k ∧ (k:ℝ) < t ∧ t-2 < k := by
  have ht0 : 0 ≤ t := by linarith
  have hn4 : 4 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr ht
  have hn1 : 1 ≤ ⌊t⌋₊ := by omega
  dsimp only
  refine ⟨by omega,?_,?_⟩
  · rw [Nat.cast_sub hn1,Nat.cast_one]
    linarith [Nat.floor_le ht0]
  · rw [Nat.cast_sub hn1,Nat.cast_one]
    linarith [Nat.sub_one_lt_floor t]

/-- Every sufficiently large prime coordinate has an integer cutoff strictly
below the prime and loses at most three in its log-log coordinate. -/
lemma loglog_grid_prime {p : ℕ} (hp : 1 < p) (hBp : 4 ≤ B p) :
    let k := ⌊B p⌋₊-1
    loglogCutoff k < p ∧ B p-3 ≤ B (loglogCutoff k) ∧ B (loglogCutoff k) ≤ B p := by
  dsimp only
  have hk := loglog_grid_index_bounds hBp
  have hb := loglogCutoff_bounds (by exact_mod_cast hk.1 : (2:ℝ) ≤ (⌊B p⌋₊-1:ℕ))
  exact ⟨loglogCutoff_lt_of_lt_B hp hk.2.1,by linarith only [hb.2.1,hk.2.2],hb.2.2.1.trans hk.2.1.le⟩

end TotientAsymptotic

end

end OAI
