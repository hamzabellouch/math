import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Model
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RationalAlgorithms

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

def expAccurate (q : ℚ) (n k : ℕ) : Prop :=
  |q| / ((k + 1 : ℕ) : ℚ) ≤ 1 / 2 ∧
    |q| ^ k / ((k.factorial : ℕ) : ℚ) * 2 ≤ (1 / 2 : ℚ) ^ n

instance (q : ℚ) (n : ℕ) : DecidablePred (expAccurate q n) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma computable_decide_and {α : Type*} [Primcodable α]
    {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Computable fun a => decide (p a)) (hq : Computable fun a => decide (q a)) :
    Computable (fun a => decide (p a ∧ q a)) := by
  exact (Computable.cond hp hq (Computable.const false)).of_eq (fun a => by
    by_cases h : p a <;> simp [h])

lemma computable_expAccurate :
    Computable₂ (fun p : ℚ × ℕ => fun k => decide (expAccurate p.1 p.2 k)) := by
  have hq : Computable (fun p : (ℚ × ℕ) × ℕ => |p.1.1|) :=
    computable_rat_abs.comp (Computable.fst.comp Computable.fst)
  have hr : Computable (fun p : (ℚ × ℕ) × ℕ => |p.1.1| / ((p.2 + 1 : ℕ) : ℚ)) :=
    computable_rat_div.comp hq (computable_rat_natCast.comp (Computable.succ.comp Computable.snd))
  have ha : Computable (fun p : (ℚ × ℕ) × ℕ =>
      |p.1.1| ^ p.2 / (p.2.factorial : ℚ) * 2) :=
    computable_rat_mul.comp (computable_rat_div.comp (computable_rat_pow.comp hq Computable.snd)
      (computable_rat_natCast.comp (primrec_nat_factorial.to_comp.comp Computable.snd)))
      (Computable.const 2)
  exact computable_decide_and
    (computable_rat_le.comp hr (Computable.const (1 / 2)))
    (computable_rat_le.comp ha (computable_rat_pow.comp (Computable.const (1 / 2))
      (Computable.snd.comp Computable.fst)))

lemma exists_expAccurate (q : ℚ) (n : ℕ) : ∃ k, expAccurate q n k := by
  have h₀ : Tendsto (fun k : ℕ => (|q| : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.mpr (tendsto_add_atTop_nat 1))
  have h₁ : Tendsto (fun k : ℕ => (|q| : ℝ) ^ k / (k.factorial : ℝ) * 2)
      atTop (𝓝 0) := by
    simpa using (Real.summable_pow_div_factorial (|q| : ℝ)).tendsto_atTop_zero.mul_const 2
  have he : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hh₀ := h₀.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hh₁ := h₁.eventually_lt_const he
  obtain ⟨k, hk₀, hk₁⟩ := (hh₀.and hh₁).exists
  refine ⟨k, ?_, ?_⟩
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one] using hk₀.le
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hk₁.le

noncomputable def expCutoff (q : ℚ) (n : ℕ) : ℕ :=
  Nat.find (exists_expAccurate q n)

lemma computable_expCutoff : Computable₂ expCutoff :=
  computable_find computable_expAccurate (fun p => exists_expAccurate p.1 p.2)

noncomputable def expApprox (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (expCutoff q n), q ^ k / (k.factorial : ℚ)

lemma computable_expApprox : Computable₂ expApprox := by
  have hs : Computable₂ (fun q : ℚ => fun n : ℕ =>
      ∑ k ∈ Finset.range n, q ^ k / (k.factorial : ℚ)) :=
    computable_sum_range (computable_rat_div.comp computable_rat_pow
      (computable_rat_natCast.comp (primrec_nat_factorial.to_comp.comp Computable.snd)))
  exact hs.comp Computable.fst computable_expCutoff

lemma real_exp_tail_bound (x : ℝ) (k : ℕ) (h : |x| / (k + 1 : ℕ) ≤ 1 / 2) :
    |Real.exp x - ∑ j ∈ Finset.range k, x ^ j / (j.factorial : ℝ)| ≤
      |x| ^ k / (k.factorial : ℝ) * 2 := by
  have hc : ‖(x : ℂ)‖ / (k + 1 : ℕ) ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  have hh := @Complex.exp_bound' (x : ℂ) k hc
  rw [← Complex.ofReal_exp] at hh
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

lemma expApprox_spec (q : ℚ) (n : ℕ) :
    |(expApprox q n : ℝ) - Real.exp (q : ℝ)| ≤ error n := by
  have hk := Nat.find_spec (exists_expAccurate q n)
  change expAccurate q n (expCutoff q n) at hk
  have hrat : |(q : ℝ)| / ((expCutoff q n + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hk.1
    push_cast at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hb := real_exp_tail_bound (q : ℝ) (expCutoff q n) hrat
  have ht : |(q : ℝ)| ^ expCutoff q n / ((expCutoff q n).factorial : ℝ) * 2 ≤ error n := by
    dsimp [error]
    have hh := (Rat.cast_le (K := ℝ)).mpr hk.2
    push_cast at hh
    simpa only [one_div] using hh
  rw [abs_sub_comm]
  simpa only [expApprox, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    using hb.trans ht

end BalancedTransport.Effectivity
end

end OAI
