import OAI.MathematicalPhysics.AlternatingFlow.EffectiveProfiles
import OAI.MathematicalPhysics.AlternatingFlow.Names

namespace OAI

section ExpNamesDevelopment

open scoped BigOperators ContDiff Topology
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma rat_sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℚ}
    (hf : Computable₂ f) : Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Computable₂ (fun a : A => fun z : ℕ × ℚ => z.2 + f a z.1) :=
    Arithmetic.rat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have h := Computable.nat_rec (Computable.snd : Computable (fun z : A × ℕ => z.2))
    (Computable.const (0 : ℚ))
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  refine h.to₂.of_eq ?_
  rintro ⟨a,n⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

lemma abs_rat_cast_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have h : (q.den : ℝ) ≥ 1 := by exact_mod_cast q.den_pos
  rw [Rat.cast_def, abs_div, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_self (Nat.cast_nonneg _) h

lemma exp_named : Named (fun q : ℚ => Real.exp (q : ℝ)) := by
  let N (z : ℚ × ℕ) : ℕ := 2 * z.1.num.natAbs + z.2 + 1
  have hN : Computable N := (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Arithmetic.int_abs.comp (Arithmetic.rat_num.comp Primrec.fst))) Primrec.snd)
    (Primrec.const 1)).to_comp
  let a (z : ℚ × ℕ) : ℚ := ∑ i ∈ Finset.range (N z), z.1 ^ i / i.factorial
  let err (z : ℚ × ℕ) : ℚ := |z.1| ^ N z / (N z).factorial * 2
  have ht : Computable₂ (fun q : ℚ => fun i : ℕ => q ^ i / i.factorial) :=
    Arithmetic.rat_div.to_comp.comp Arithmetic.rat_pow.to_comp
      (Arithmetic.rat_natCast.to_comp.comp (factorial.to_comp.comp Computable.snd))
  have ha : Computable a := (rat_sum_range ht).comp Computable.fst hN
  have he : Computable err := Arithmetic.rat_mul.to_comp.comp
    (Arithmetic.rat_div.to_comp.comp
      (Arithmetic.rat_pow.to_comp.comp (Arithmetic.rat_abs.to_comp.comp Computable.fst) hN)
      (Arithmetic.rat_natCast.to_comp.comp (factorial.to_comp.comp hN))) (Computable.const 2)
  apply Named.of_certificate _ a err ha he
  · intro q n
    have hl : ‖(q : ℂ)‖ / (N (q,n)).succ ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N (q,n)).succ)]
      rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
      have hh := abs_rat_cast_le_num q
      dsimp [N]; push_cast; linarith
    have h := Complex.exp_bound' hl
    have hc : (∑ i ∈ Finset.range (N (q,n)), (q : ℂ) ^ i / i.factorial) = (a (q,n) : ℂ) := by
      simp [a]
    rw [hc, show (q : ℂ) = ((q : ℝ) : ℂ) by simp, ← Complex.ofReal_exp,
      show (a (q,n) : ℂ) = ((a (q,n) : ℝ) : ℂ) by simp,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs] at h
    simpa only [err, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_abs,
      Rat.cast_natCast, Rat.cast_ofNat] using h
  · intro q
    have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop |(q : ℝ)|).mul_const 2
    have hshift : Tendsto (fun n => N (q,n)) atTop atTop := by
      apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
      intro n; dsimp [N]; omega
    simpa only [err, Function.comp_def, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, zero_mul] using hlim.comp hshift

end AlternatingNS.Effective

end ExpNamesDevelopment

end OAI
