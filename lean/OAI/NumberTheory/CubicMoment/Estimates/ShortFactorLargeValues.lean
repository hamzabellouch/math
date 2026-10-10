import OAI.NumberTheory.CubicMoment.Estimates.MomentExponents

namespace OAI

/-! Actual large-value rows for the short ideal factors. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_power_product_large_values {ι κ : Type*} [Fintype ι]
    (P : Finset κ) (k : ι → ℕ) (F : ι → κ → ℂ) (B : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hrow : ∀ p ∈ P, ∀ i, B i ≤ ‖F i p‖) :
    (P.card:ℝ)*(∏ i, (B i)^(k i))^2 ≤ ∑ p ∈ P, ‖∏ i, (F i p)^(k i)‖^2 := by
  have hprod : 0 ≤ ∏ i, (B i)^(k i) :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (hB i) _)
  calc
    _ = ∑ _p ∈ P, (∏ i, (B i)^(k i))^2 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_prod]
      simp only [norm_pow]
      apply pow_le_pow_left₀ hprod
      exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hB i) _)
        (fun i _ => pow_le_pow_left₀ (hB i) (hrow p hp i) _)

theorem HasPowerExponent.finset_prod {ι : Type*} (S : Finset ι)
    {Y : ℕ → ℝ} {f : ι → ℕ → ℝ} {a : ι → ℝ}
    (hf : ∀ i ∈ S, HasPowerExponent Y (f i) (a i))
    (hp : ∀ i ∈ S, ∀ᶠ j in atTop, 0 < f i j) :
    HasPowerExponent Y (fun j => ∏ i ∈ S, f i j) (∑ i ∈ S, a i) := by
  apply (tendsto_finsetSum S hf).congr'
  filter_upwards [(S.eventually_all).mpr hp] with j hj
  rw [Real.log_prod (fun i hi => (hj i hi).ne'),Finset.sum_div]

theorem HasPowerExponent.prod_natPowers {ι : Type*} [Fintype ι]
    (k : ι → ℕ) {Y : ℕ → ℝ} {f : ι → ℕ → ℝ} {a : ι → ℝ}
    (hf : ∀ i, HasPowerExponent Y (f i) (a i))
    (hp : ∀ i, ∀ᶠ j in atTop, 0 < f i j) :
    HasPowerExponent Y (fun j => ∏ i, (f i j)^(k i)) (∑ i, (k i:ℝ)*a i) := by
  apply HasPowerExponent.finset_prod Finset.univ (fun i _ => (hf i).natPow (k i))
  intro i _
  filter_upwards [hp i] with j hj using pow_pos hj _

/-- The arithmetic data of the actual short factors, before choosing a
set of characters on which their values are large. -/
structure ShortFactorFamily (ι : Type*) where
  cutoff : ℕ → ℝ
  length : ℕ → ι → ℝ
  coefficient : ℕ → ι → EisensteinArithmeticFunction
  twist : ℕ → ι → Eisenstein → ℂ
  factor_spec : ∀ j i, ShortArithmeticFactor (cutoff j) (coefficient j i)
  length_ge_one : ∀ j i, 1 ≤ length j i
  twist_bound : ∀ j i, ∀ a ∈ primaryElementBall (length j i), ‖twist j i a‖ ≤ 1

def ShortFactorFamily.cubicValue {ι : Type*} (F : ShortFactorFamily ι)
    (j : ℕ) (i : ι) (a : Eisenstein) : ℂ :=
  primaryIdealPolynomial (F.length j i) (F.coefficient j i)
    (fun n => F.twist j i n*cubicSymbol a n)

def ShortFactorFamily.mixedValue {ι : Type*} (F : ShortFactorFamily ι)
    (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) : ℂ :=
  primaryIdealPolynomial (F.length j i) (F.coefficient j i)
    (fun n => F.twist j i n*mixedCubic p.1 p.2 n)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first limiting moment inequality follows from the actual
short-factor moment and the actual large-value rows. -/
theorem ShortFactorFamily.cubic_large_values_exponent (F : ShortFactorFamily ι)
    (k : ι → ℕ) {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein)
    (B : ℕ → ι → ℝ) {a v : ι → ℝ} {r n : ℝ}
    (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ x ∈ P j, primary x ∧ Squarefree x ∧ norm x ≤ N j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i x‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N n)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) :
    r+2*(∑ i, (k i:ℝ)*v i) ≤ (∑ i, (k i:ℝ)*a i)+
      max (max n (∑ i, (k i:ℝ)*a i)) ((2/3:ℝ)*(n+∑ i, (k i:ℝ)*a i)) := by
  let L : ℕ → ℝ := fun j => ∏ i, (F.length j i)^(k i)
  let V : ℕ → ℝ := fun j => ∏ i, (B j i)^(k i)
  have hLp : ∀ᶠ j in atTop, 0 < L j := Eventually.of_forall (fun j =>
    Finset.prod_pos (fun i _ => pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) _))
  have hVp : ∀ᶠ j in atTop, 0 < V j := Eventually.of_forall (fun j =>
    Finset.prod_pos (fun i _ => pow_pos (hB j i) _))
  have hLexp := HasPowerExponent.prod_natPowers k hXexp (fun i =>
    Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one j i)))
  have hVexp := HasPowerExponent.prod_natPowers k hBexp (fun i =>
    Eventually.of_forall (fun j => hB j i))
  apply cubic_moment_exponent hY
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j)))) hVp
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (hN j))) hLp
    hRexp hVexp hNexp hLexp
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := shortFactor_multiplicity_power k hε
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  exact (finite_power_product_large_values (P j) k (F.cubicValue j) (B j)
    (fun i => (hB j i).le) (hrow j)).trans
    (hbound (F.cutoff j) (F.length j) (F.coefficient j) (F.twist j)
      (F.factor_spec j) (F.length_ge_one j) (F.twist_bound j) (P j) (N j) (hN j) (hP j))

/-- The second limiting moment inequality retains the genuine ordinary
mixed-character input and the same actual short factors. -/
theorem ShortFactorFamily.mixed_large_values_exponent (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ)
    {Y Q : ℕ → ℝ} (P : ℕ → Finset (Eisenstein × Eisenstein))
    (B : ℕ → ι → ℝ) {a v : ι → ℝ} {r q : ℝ}
    (hY : Tendsto Y atTop atTop) (hQ : ∀ j, 1 ≤ Q j)
    (hP : ∀ j, ∀ p ∈ P j, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.mixedValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hQexp : HasPowerExponent Y Q q)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) :
    r+2*(∑ i, (k i:ℝ)*v i) ≤ (∑ i, (k i:ℝ)*a i)+
      max (2*q) (∑ i, (k i:ℝ)*a i) := by
  let L : ℕ → ℝ := fun j => ∏ i, (F.length j i)^(k i)
  let V : ℕ → ℝ := fun j => ∏ i, (B j i)^(k i)
  have hLp : ∀ᶠ j in atTop, 0 < L j := Eventually.of_forall (fun j =>
    Finset.prod_pos (fun i _ => pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) _))
  have hVp : ∀ᶠ j in atTop, 0 < V j := Eventually.of_forall (fun j =>
    Finset.prod_pos (fun i _ => pow_pos (hB j i) _))
  have hLexp := HasPowerExponent.prod_natPowers k hXexp (fun i =>
    Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one j i)))
  have hVexp := HasPowerExponent.prod_natPowers k hBexp (fun i =>
    Eventually.of_forall (fun j => hB j i))
  apply ordinary_moment_exponent hY
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j)))) hVp
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (hQ j))) hLp
    hRexp hVexp hQexp hLexp
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := shortFactor_mixed_multiplicity_power hHuxley k hε
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  exact (finite_power_product_large_values (P j) k (F.mixedValue j) (B j)
    (fun i => (hB j i).le) (hrow j)).trans
    (hbound (F.cutoff j) (F.length j) (F.coefficient j) (F.twist j)
      (F.factor_spec j) (F.length_ge_one j) (F.twist_bound j) (P j) (Q j) (hQ j) (hP j))

end CubicFirstMoment

end

end OAI
