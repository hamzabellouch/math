import OAI.NumberTheory.JointDickman.Analysis.CharacterEulerRemainder
import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceInput
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge

namespace OAI

/-! # Comparing finite character distances with damped prime sums -/
namespace JointDickman
open Complex Finset
open scoped BigOperators

/-- A finite distance dominates the absolutely convergent damped distance,
with the missing mass accounted for explicitly. -/
theorem finite_distance_lower {ι : Type*} (S : Finset ι) (a b v : ι → ℝ)
    (hb : Summable b) (hb0 : ∀ i, 0 ≤ b i)
    (hv : ∀ i, |v i| ≤ 1) (hba : ∀ i ∈ S, b i ≤ a i) :
    2*(∑ i ∈ S, b i) - ∑' i, b i - ∑' i, v i*b i ≤
      ∑ i ∈ S, (1-v i)*a i := by
  have hprod : Summable (fun i => v i*b i) := hb.of_norm_bounded
    (fun i => by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hb0 i)]
                 exact mul_le_of_le_one_left (hb0 i) (hv i))
  have hp : ∀ i, 0 ≤ b i+v i*b i := by
    intro i
    have h := (abs_le.mp (hv i)).1
    nlinarith [hb0 i]
  have hsum := (hb.add hprod).sum_le_tsum S (fun i _ => hp i)
  rw [Summable.tsum_add hb hprod, sum_add_distrib] at hsum
  have hlocal : (∑ i ∈ S, b i) - (∑ i ∈ S, v i*b i) ≤
      ∑ i ∈ S, (1-v i)*a i := by
    rw [←sum_sub_distrib]
    apply sum_le_sum
    intro i hi
    have h := (abs_le.mp (hv i)).2
    nlinarith [hba i hi]
  linarith

noncomputable def characterPrimePhase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (p : Nat.Primes) : ℂ :=
  χ (p.val : ZMod q)*Complex.exp (-((t*Real.log p.val:ℝ):ℂ)*Complex.I)

theorem characterPrimePhase_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (p : Nat.Primes) : ‖characterPrimePhase χ t p‖ ≤ 1 := by
  rw [characterPrimePhase, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_im,Complex.ofReal_im,
    Complex.I_re,Complex.I_im, mul_zero, zero_sub, neg_zero, Real.exp_zero, mul_one]
  exact χ.norm_le_one (p.val:ZMod q)

theorem characterPrimePower_eq_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (p : Nat.Primes) :
    characterPrimePower χ ((σ:ℂ)+(t:ℂ)*I) p =
      characterPrimePhase χ t p*((p.val:ℝ)^(-σ):ℝ) := by
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  have hpC : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [characterPrimePower, Complex.cpow_def_of_ne_zero hpC]
  rw [show (p.val:ℂ) = ((p.val:ℝ):ℂ) by simp,
    ←Complex.ofReal_log hp.le]
  have he : (Real.log (p.val:ℝ):ℂ)*(-((σ:ℂ)+(t:ℂ)*I)) =
      -((t*Real.log p.val:ℝ):ℂ)*I + ((Real.log p.val*(-σ):ℝ):ℂ) := by
    push_cast; ring
  rw [he,Complex.exp_add,←Complex.ofReal_exp,←Real.rpow_def_of_pos hp]
  simp only [characterPrimePhase]
  ring

noncomputable def primeCutoff (X : ℝ) : Finset Nat.Primes :=
  (Icc 2 ⌊X⌋₊).subtype Nat.Prime

theorem primeCutoff_sum (f : ℕ → ℝ) (X : ℝ) :
    (∑ p ∈ primeCutoff X, f p.val) = ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime, f p := by
  exact sum_subtype_eq_sum_filter f

theorem characterDistance_primeCutoff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X t : ℝ) :
    PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t =
      ∑ p ∈ primeCutoff X, (1-(characterPrimePhase χ t p).re)/(p.val:ℝ) := by
  unfold PublishedInputs.primeDistanceSquared
  rw [←primeCutoff_sum]
  apply sum_congr rfl
  intro p _
  rw [characterArithmetic_prime χ p.property]
  rfl

/-- The prime cutoff can be replaced by the Euler half-plane without hiding
any arithmetic cancellation in an assumption. -/
theorem characterDistance_damped_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    2*(∑ p ∈ primeCutoff X, (p.val:ℝ)^(-σ)) -
      (∑' p : Nat.Primes, (p.val:ℝ)^(-σ)) -
      (primeCharacterLinearSum χ ((σ:ℂ)+(t:ℂ)*I)).re ≤
      PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t := by
  have hs : 1 < ((σ:ℂ)+(t:ℂ)*I).re := by simpa using hσ
  have hb : Summable (fun p : Nat.Primes => (p.val:ℝ)^(-σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype Nat.Prime
  have hlin : (∑' p : Nat.Primes, (characterPrimePhase χ t p).re*(p.val:ℝ)^(-σ)) =
      (primeCharacterLinearSum χ ((σ:ℂ)+(t:ℂ)*I)).re := by
    rw [primeCharacterLinearSum,Complex.re_tsum (primeCharacterLinearSum_summable χ hs)]
    apply tsum_congr
    intro p
    rw [characterPrimePower_eq_phase,Complex.mul_re]
    simp
  rw [characterDistance_primeCutoff]
  simp_rw [div_eq_mul_inv]
  rw [←hlin]
  apply finite_distance_lower (primeCutoff X)
    (fun p => (p.val:ℝ)⁻¹) (fun p => (p.val:ℝ)^(-σ))
    (fun p => (characterPrimePhase χ t p).re) hb
    (fun _ => by positivity)
    (fun p => (Complex.abs_re_le_norm _).trans (characterPrimePhase_norm_le χ t p))
  intro p _
  rw [←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast p.property.one_le) (by linarith)

end JointDickman

end OAI
