import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeLogDensity

namespace OAI

/-! # Precisely stated published inputs for primes in progressions

Reference: H. L. Montgomery and R. C. Vaughan, *Multiplicative Number
Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97,
Chapter 11, DOI 10.1017/CBO9780511618314.013.

`PublishedProgressionInput.theta` is Corollary 11.20, equations (11.32) and
(11.34), p. 381. `complete` specifies the exceptional zero in Theorem 11.3,
p. 360. `unique` is the real-zero specialization of Corollary 11.10 (Page),
p. 369. The positive zero-free constant can be decreased so these use one
constant and the harmless denominator `log (4*q)` throughout.

These are explicit conditional inputs. In particular, no logarithmic
interval estimate or arithmetic comparison is assumed here.
-/

namespace Ostmann

/-- An actual primitive real character and an actual zero of its continued
Dirichlet L-function, rather than an unrestricted correction coefficient. -/
structure PrimitiveRealZero where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℝ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1
  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_one : beta < 1
  zero : @DirichletCharacter.LFunction modulus ⟨Nat.ne_of_gt positive⟩
    (character.ringHomComp Complex.ofRealHom) (beta : ℂ) = 0

noncomputable def pageCoefficient (z : Option PrimitiveRealZero) (a : ℕ) : ℝ :=
  match z with
  | none => 0
  | some e => e.character (a : ZMod e.modulus)

noncomputable def pageBeta (z : Option PrimitiveRealZero) : ℝ :=
  match z with
  | none => 1
  | some e => e.beta

theorem pageCoefficient_abs_le_one (z : Option PrimitiveRealZero) (a : ℕ) :
    |pageCoefficient z a| ≤ 1 := by
  cases z with
  | none => simp [pageCoefficient]
  | some e => exact (Real.norm_eq_abs _).symm ▸ e.character.norm_le_one _

theorem pageBeta_pos (z : Option PrimitiveRealZero) : 0 < pageBeta z := by
  cases z with
  | none => norm_num [pageBeta]
  | some e => exact e.beta_pos

theorem pageBeta_le_one (z : Option PrimitiveRealZero) : pageBeta z ≤ 1 := by
  cases z with
  | none => exact le_rfl
  | some e => exact e.beta_lt_one.le

/-- The restricted classical analytic input. The family chooses the local
exceptional primitive character, if one exists, for each modulus. -/
structure PublishedProgressionInput where
  kappa : ℝ
  decay : ℝ
  errorConstant : ℝ
  kappa_pos : 0 < kappa
  decay_pos : 0 < decay
  errorConstant_nonneg : 0 ≤ errorConstant
  localZero : ℕ → Option PrimitiveRealZero
  divides : ∀ q e, localZero q = some e → e.modulus ∣ q
  /-- Theorem 11.3: any zero in the stated exceptional region is retained. -/
  complete : ∀ q, 1 ≤ q → ∀ e : PrimitiveRealZero, e.modulus ∣ q →
    1 - kappa / Real.log (4 * (q : ℝ)) ≤ e.beta → localZero q = some e
  /-- Corollary 11.10, restricted to positive real zeros. -/
  unique : ∀ Q, 2 ≤ Q → ∀ e f : PrimitiveRealZero,
    e.modulus ≤ Q → f.modulus ≤ Q →
    1 - kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta →
    1 - kappa / Real.log (4 * (Q : ℝ)) ≤ f.beta → e = f
  /-- Corollary 11.20, with absolute constants uniform in the modulus. -/
  theta : ∀ q, 1 ≤ q → ∀ a, a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |primeProgressionTheta q a x -
      thetaMainTerm (Nat.totient q) (pageCoefficient (localZero q) a)
        (pageBeta (localZero q)) x| ≤
      errorConstant * x * Real.exp (-decay * Real.sqrt (Real.log x))

/-- The logarithmic prime estimate is derived by partial summation; it is
not included among the published assumptions. -/
theorem PublishedProgressionInput.local_log_interval (P : PublishedProgressionInput)
    (q a : ℕ) (hq : 1 ≤ q) (ha : a.Coprime q) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (P.localZero q) a) (pageBeta (P.localZero q)) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  apply prime_log_interval_error q a _ _ _ _ _ (ne_of_gt (pageBeta_pos _))
    P.decay_pos.le P.errorConstant_nonneg hs hst hshort
  intro x hx
  apply P.theta q hq a ha x
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have htwo : (2 : ℝ) ≤ Real.exp s := by
    have h := Real.add_one_le_exp s
    linarith
  exact htwo.trans hx.1

end Ostmann

end OAI
