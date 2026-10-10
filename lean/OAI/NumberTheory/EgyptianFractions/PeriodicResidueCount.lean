import OAI.NumberTheory.EgyptianFractions.ResidueIntervalCount

namespace OAI
noncomputable section

namespace Problem337

/-- A periodic predicate has one full period's worth of solutions in each block. -/
theorem periodic_count_mul {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (q : ℕ) :
    Nat.count p (q * d) = q * Nat.count p d := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add']
    have hshift : (fun k => p (k + d)) = p := by
      funext k
      exact hp k
    simp only [hshift, ih]
    ring

/-- Exact quotient-and-remainder formula for a periodic counting function. -/
theorem periodic_count_div_mod {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (N : ℕ) :
    Nat.count p N = (N / d) * Nat.count p d + Nat.count p (N % d) := by
  conv_lhs => rw [← Nat.mod_add_div N d]
  rw [Nat.count_add']
  have hshift : (fun k => p (k + d * (N / d))) = p := by
    funext k
    simpa [Nat.mul_comm] using hp.nsmul (N / d) k
  simp only [hshift]
  rw [Nat.mul_comm d, periodic_count_mul hp]
  omega

/-- The count on a prefix differs from its periodic mean by at most the number
of allowed residues in one period. This bound is uniform in the prefix length. -/
theorem periodic_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (N : ℕ) :
    |(Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hcount := periodic_count_div_mod hp N
  have hrem := Nat.count_monotone p (Nat.mod_lt N hd).le
  have hdiv := Nat.mod_add_div N d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hremR : (Nat.count p (N % d) : ℝ) ≤ Nat.count p d := by exact_mod_cast hrem
  have hmodR : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have hdivR : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by exact_mod_cast hdiv
  have hcountR : (Nat.count p N : ℝ) =
      (N / d : ℕ) * (Nat.count p d : ℝ) + Nat.count p (N % d) := by exact_mod_cast hcount
  have hnonneg : (0 : ℝ) ≤ Nat.count p d := by positivity
  have hterm0 : 0 ≤ ((N % d : ℕ) : ℝ) * Nat.count p d / d := by positivity
  have hterm : ((N % d : ℕ) : ℝ) * Nat.count p d / d ≤ Nat.count p d := by
    apply (div_le_iff₀ hdR).2
    nlinarith [mul_le_mul_of_nonneg_right hmodR hnonneg]
  have heq : (Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d =
      Nat.count p (N % d) - ((N % d : ℕ) : ℝ) * Nat.count p d / d := by
    rw [hcountR, ← hdivR]
    field_simp
    ring
  rw [heq, abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ Nat.count p (N % d) by positivity]

/-- Shifting a periodic predicate does not change its mass over a full period. -/
theorem periodic_count_shift_period {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (a : ℕ) :
    Nat.count (fun n => p (a + n)) d = Nat.count p d := by
  have h₁ := Nat.count_add p a d
  have h₂ := Nat.count_add' p a d
  have hshift : (fun n => p (n + d)) = p := funext hp
  simp only [hshift] at h₂
  omega

/-- Counting a predicate on a shifted natural interval is the same as counting
its translate on a prefix. -/
theorem filter_Ico_card_eq_count_shift (p : ℕ → Prop) [DecidablePred p]
    (a N : ℕ) :
    ((Finset.Ico a (a + N)).filter p).card =
      Nat.count (fun n => p (a + n)) N := by
  rw [Nat.count_eq_card_filter_range, ← Nat.Ico_zero_eq_range]
  have hmap := Finset.map_add_left_Ico 0 N a
  rw [Nat.add_zero] at hmap
  rw [← hmap, Finset.filter_map, Finset.card_map]
  rfl

/-- Sharp periodic discrepancy on any shifted interval: the error is bounded
by one period's mass, independent of both endpoints. -/
theorem periodic_Ico_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter p).card : ℝ) -
      (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hshift : Function.Periodic (fun n => p (a + n)) d := by
    intro n
    simpa only [Nat.add_assoc] using hp (a + n)
  have h := periodic_count_discrepancy hd hshift N
  rw [periodic_count_shift_period hp a] at h
  simpa only [filter_Ico_card_eq_count_shift] using h

/-- The periodic mass of a predicate on residue classes is its finite cardinality. -/
theorem zmod_predicate_period_count (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod d)) d =
      (Finset.univ.filter P).card := by
  classical
  simpa [Nat.count_eq_card_filter_range, Nat.div_self (NeZero.pos d)] using
    (card_range_zmod_mem d (Finset.univ.filter P))

/-- Residue classes are equidistributed up to one copy of the allowed set on
any natural interval, without a primality or coprimality assumption. -/
theorem zmod_predicate_Ico_discrepancy (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter (fun n : ℕ => P (n : ZMod d))).card : ℝ) -
      (N : ℝ) * (Finset.univ.filter P).card / d| ≤ (Finset.univ.filter P).card := by
  have hp : Function.Periodic (fun n : ℕ => P (n : ZMod d)) d := by
    intro n
    simp
  have h := periodic_Ico_count_discrepancy (NeZero.pos d) hp a N
  simpa only [zmod_predicate_period_count d P] using h

end Problem337

end

end OAI
