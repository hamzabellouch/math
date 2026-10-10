import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceTransfer
import OAI.NumberTheory.JointDickman.Arithmetic.FinitePrimeWeight

namespace OAI

/-! # The actual nonprincipal multiplicative interpolants -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def twistedWeightedBinInterpolant {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) {m : ℕ} (a : ι → Fin m)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => (weightedBinInterpolant E w a n : ℂ)*characterArithmetic χ n,by simp⟩

theorem twistedWeightedBinInterpolant_multiplicative {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : w.IsMultiplicative)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (twistedWeightedBinInterpolant E w a χ).IsMultiplicative := by
  have hf := weightedBinInterpolant_isMultiplicative E w hw a
  have hg := characterArithmetic_multiplicative χ
  refine ⟨?_,?_⟩
  · simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,hf.1,hg.1,
      Complex.ofReal_one,mul_one]
  · intro n k hnk
    simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,
      hf.2 hnk,hg.2 hnk,Complex.ofReal_mul]
    ring

theorem twistedWeightedBinInterpolant_norm_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : ∀ n, |w n| ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖twistedWeightedBinInterpolant E w a χ n‖ ≤ 1 := by
  change ‖(weightedBinInterpolant E w a n : ℂ)*characterArithmetic χ n‖ ≤ 1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (abs_weightedBinInterpolant_le_one E w hw a n)
    (characterArithmetic_norm_le_one χ n) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem small_prime_binLabel_eq_one {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]
    {J : ℕ} (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → R) {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime)
    (hpx : (p : ℝ) ≤ x^(1/(J : ℝ))) :
    binLabel (fun i => primeBin x J (k i)) z p = 1 := by
  apply binLabel_eq_one_of_no_factor _ z hp.ne_zero
  intro i r hr hrdvd
  have hrprime : r.Prime := (mem_filter.mp hr).2
  have hrp : r = p := ((Nat.dvd_prime hp).mp hrdvd).resolve_left hrprime.ne_one
  have hrlower : x^((k i : ℝ)/J) < (r : ℝ) :=
    Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hr).1).1
  have hmono : x^(1/(J : ℝ)) ≤ x^((k i : ℝ)/J) :=
    Real.rpow_le_rpow_of_exponent_le hx
      (div_le_div_of_nonneg_right (by exact_mod_cast hk i)
        (by exact_mod_cast hJ.le : (0 : ℝ) ≤ J))
  subst r
  linarith

theorem finitePrimeWeight_prime_eq_one {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime)
    (t : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) : finitePrimeWeight P t p = 1 := by
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false]
  apply prod_eq_one
  intro r hr
  apply ite_eq_right
  intro hd
  have hrp : r = p := ((Nat.dvd_prime hp).mp hd).resolve_left (hP r hr).ne_one
  exact hpP (hrp ▸ hr)

theorem twistedWeightedBinInterpolant_small_prime {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) (t : ℕ → ℝ)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    (hpx : (p : ℝ) ≤ x^(1/(J : ℝ))) :
    twistedWeightedBinInterpolant (fun i => primeBin x J (k i)) (finitePrimeWeight P t) a χ p =
      χ (p : ZMod q) := by
  simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,weightedBinInterpolant,
    ArithmeticFunction.pmul_apply,small_prime_binLabel_eq_one hJ k hk _ hx hp hpx,
    finitePrimeWeight_prime_eq_one hP t hp hpP,one_mul,Complex.ofReal_one,
    characterArithmetic_prime χ hp]

end JointDickman

end OAI
