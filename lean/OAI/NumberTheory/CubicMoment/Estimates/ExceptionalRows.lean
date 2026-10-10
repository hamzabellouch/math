import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorLargeValues
import OAI.NumberTheory.CubicMoment.Estimates.MomentRigidity
import OAI.NumberTheory.CubicMoment.Estimates.BalancedErrorMoment

namespace OAI

/-! Rigidity and contradiction for actual short-factor large-value rows. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- A bound by every arbitrarily enlarged power passes to the exact
logarithmic exponent. The constants are allowed to depend on the enlargement. -/
theorem HasPowerExponent.le_of_small_power {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hY : Tendsto Y atTop atTop)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j)
    (hbound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j in atTop, f j ≤ C*(g j)^(1+η)) : a ≤ b := by
  have hη (η : ℝ) (hη : 0 < η) : a ≤ η*b+b := by
    obtain ⟨C,hC,hCbound⟩ := hbound η hη
    have hr := (HasPowerExponent.const hY C).mul (hg.rpow hgp (1+η))
      (Eventually.of_forall (fun _ => hC))
      (by filter_upwards [hgp] with j hj using Real.rpow_pos_of_pos hj _)
    have h := hf.mono hr hY hfp hCbound
    simpa only [zero_add,add_zero,add_mul,one_mul,add_comm] using h
  by_contra hab
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  let η : ℝ := (a-b)/(2*(|b|+1))
  have hηpos : 0 < η := div_pos hgap (by positivity)
  have he : η*(2*(|b|+1)) = a-b := div_mul_cancel₀ _ (by positivity)
  have hb := mul_le_mul_of_nonneg_left (le_abs_self b) hηpos.le
  have h := hη η hηpos
  nlinarith [mul_nonneg hηpos.le (abs_nonneg b)]

theorem ShortFactorFamily.cubicValue_small_power {ι : Type*}
    (F : ShortFactorFamily ι) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (i : ι) (a : Eisenstein), primary a →
      ‖F.cubicValue j i a‖ ≤ C*(F.length j i)^(1+η) := by
  obtain ⟨C,hC,hbound⟩ := shortFactorPolynomial_norm_small_power hη
  refine ⟨C,hC,?_⟩
  intro j i a ha
  apply hbound (F.cutoff j) (F.length j i) (F.coefficient j i)
    (F.factor_spec j i) (F.length_ge_one j i)
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (F.twist_bound j i n hn) (norm_cubicSymbol_le_one ha n)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem ShortFactorFamily.mixedValue_small_power {ι : Type*}
    (F : ShortFactorFamily ι) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein),
      primary p.1 → primary p.2 →
      ‖F.mixedValue j i p‖ ≤ C*(F.length j i)^(1+η) := by
  obtain ⟨C,hC,hbound⟩ := shortFactorPolynomial_norm_small_power hη
  refine ⟨C,hC,?_⟩
  intro j i p h₁ h₂
  apply hbound (F.cutoff j) (F.length j i) (F.coefficient j i)
    (F.factor_spec j i) (F.length_ge_one j i)
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (F.twist_bound j i n hn) (norm_mixedCubic_le_one h₁ h₂ n)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem ShortFactorFamily.length_exponent_nonneg {ι : Type*}
    (F : ShortFactorFamily ι) {Y : ℕ → ℝ} {a : ι → ℝ}
    (hY : Tendsto Y atTop atTop)
    (hX : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i)) (i : ι) :
    0 ≤ a i :=
  (HasPowerExponent.const hY 1).mono (hX i) hY
    (Eventually.of_forall (fun _ => zero_lt_one))
    (Eventually.of_forall (fun j => F.length_ge_one j i))

theorem ShortFactorFamily.cubic_value_exponent_le {ι : Type*}
    (F : ShortFactorFamily ι) {Y : ℕ → ℝ} (P : ℕ → Finset Eisenstein)
    (B : ℕ → ι → ℝ) {a v : ι → ℝ}
    (hY : Tendsto Y atTop atTop) (hP : ∀ j, ∀ x ∈ P j, primary x)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i x‖)
    (hX : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hV : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) (i : ι) :
    v i ≤ a i := by
  apply (hV i).le_of_small_power (hX i) hY
    (Eventually.of_forall (fun j => hB j i))
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one j i)))
  intro η hη
  obtain ⟨C,hC,hbound⟩ := F.cubicValue_small_power hη
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  obtain ⟨x,hx⟩ := hPne j
  exact (hrow j x hx i).trans (hbound j i x (hP j x hx))

theorem ShortFactorFamily.mixed_value_exponent_le {ι : Type*}
    (F : ShortFactorFamily ι) {Y : ℕ → ℝ} (P : ℕ → Finset (Eisenstein × Eisenstein))
    (B : ℕ → ι → ℝ) {a v : ι → ℝ}
    (hY : Tendsto Y atTop atTop)
    (hP : ∀ j, ∀ p ∈ P j, primary p.1 ∧ primary p.2)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.mixedValue j i p‖)
    (hX : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hV : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) (i : ι) :
    v i ≤ a i := by
  apply (hV i).le_of_small_power (hX i) hY
    (Eventually.of_forall (fun j => hB j i))
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one j i)))
  intro η hη
  obtain ⟨C,hC,hbound⟩ := F.mixedValue_small_power hη
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  obtain ⟨p,hp⟩ := hPne j
  exact (hrow j p hp i).trans (hbound j i p (hP j p hp).1 (hP j p hp).2)

/-- The exponent `2/3` for balanced row cardinality is proved from the
actual two component norm cutoffs, rather than imposed on the row count. -/
theorem balanced_rows_exponent_le {Y L : ℕ → ℝ}
    (P : ℕ → Finset (Eisenstein × Eisenstein)) {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hL : ∀ j, 1 ≤ L j)
    (hP : ∀ j, ∀ p ∈ P j, primary p.1 ∧ primary p.2 ∧
      norm p.1 ≤ L j ∧ norm p.2 ≤ L j)
    (hPne : ∀ j, (P j).Nonempty)
    (hR : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hLexp : HasPowerExponent Y L (1/3)) : r ≤ 2/3 := by
  have hr := (HasPowerExponent.const hY 324).mul (hLexp.natPow 2)
    (Eventually.of_forall (fun _ => by norm_num))
    (Eventually.of_forall (fun j => sq_pos_of_pos (zero_lt_one.trans_le (hL j))))
  have h := hR.mono hr hY
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j))))
    (Eventually.of_forall (fun j => balanced_pair_card (P j)
      (zero_le_one.trans (hL j)) (hP j)))
  norm_num at h ⊢
  exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual first-configuration short factors and their sharp moments force
all values to have exponent `5/6` of their length and exactly `2/3` rows. -/
theorem ShortFactorFamily.cubic_rows_rigidity (F : ShortFactorFamily ι)
    {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein) (B : ℕ → ι → ℝ)
    {a v : ι → ℝ} {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ x ∈ P j, primary x ∧ Squarefree x ∧ norm x ≤ N j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i x‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i))
    (ha : ∀ i, a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r) :
    (∀ i, v i = 5*a i/6) ∧ r = 2/3 := by
  apply first_shape_multiplicity_rigidity a v r
    (fun i => ⟨F.length_exponent_nonneg hY hXexp i,ha i⟩) hsum hlarge
  intro k hk₀ hk₁
  calc
    _ ≤ (∑ i, (k i:ℝ)*a i)+max (max 1 (∑ i, (k i:ℝ)*a i))
        ((2/3:ℝ)*(1+∑ i, (k i:ℝ)*a i)) :=
      F.cubic_large_values_exponent k P B hY hN hP hPne hB hrow hRexp hNexp hXexp hBexp
    _ = _ := by
      convert cubicSieve_exponent hk₀ hk₁ using 1 <;> ring_nf

/-- No balanced sequence of actual short-factor large-value rows can
satisfy the unsaved moment lower bound when every factor is shorter than
one. The only published assumption here is Huxley's additive large sieve. -/
theorem ShortFactorFamily.balanced_rows_contradiction (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) {Y Q L : ℕ → ℝ}
    (P : ℕ → Finset (Eisenstein × Eisenstein)) (B : ℕ → ι → ℝ)
    {a v : ι → ℝ} {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hQ : ∀ j, 1 ≤ Q j) (hL : ∀ j, 1 ≤ L j)
    (hP : ∀ j, ∀ p ∈ P j, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q j)
    (hLP : ∀ j, ∀ p ∈ P j, norm p.1 ≤ L j ∧ norm p.2 ≤ L j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.mixedValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hQexp : HasPowerExponent Y Q (2/3)) (hLexp : HasPowerExponent Y L (1/3))
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i))
    (ha : ∀ i, a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r) : False := by
  have hprim : ∀ j, ∀ p ∈ P j, primary p.1 ∧ primary p.2 :=
    fun j p hp => ⟨(hP j p hp).1.1,(hP j p hp).1.2.1⟩
  have hcard := balanced_rows_exponent_le P hY hL
    (fun j p hp => ⟨(hprim j p hp).1,(hprim j p hp).2,
      (hLP j p hp).1,(hLP j p hp).2⟩) hPne hRexp hLexp
  apply balanced_multiplicity_contradiction a v r
    (fun i => ⟨F.length_exponent_nonneg hY hXexp i,ha i⟩)
    (F.mixed_value_exponent_le P B hY hprim hPne hB hrow hXexp hBexp)
    hsum hlarge hcard
  intro k
  have h := F.mixed_large_values_exponent hHuxley k P B hY hQ hP hPne hB hrow
    hRexp hQexp hXexp hBexp
  norm_num at h ⊢
  exact h

end CubicFirstMoment

end

end OAI
