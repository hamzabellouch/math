import OAI.NumberTheory.JointDickman.Amplification.PublishedInputs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace OAI

/-!
# Multiplicative bin labels and real interpolation

The count in a finite prime bin includes multiplicity. Its additivity gives
complete multiplicativity of the uncentered labels. Centering is performed
only after evaluating a label; no multiplicativity is claimed for it.

A tensor product of finite Vandermonde inverses expresses every function of
bounded count vectors as a fixed finite linear combination of real,
nonnegative, 1-bounded multiplicative interpolants.
-/

namespace JointDickman

open Finset

/-- The prime bin `(x^(k/J), x^((k+1)/J)]`. -/
noncomputable def primeBin (x : ℝ) (J k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc ⌊x ^ ((k : ℝ) / J)⌋₊ ⌊x ^ (((k : ℝ) + 1) / J)⌋₊).filter Nat.Prime

/-- The number of factors in a finite bin, with multiplicity. -/
def binCount (E : Finset ℕ) (n : ℕ) : ℕ := ∑ p ∈ E, n.factorization p

@[simp] theorem binCount_one (E : Finset ℕ) : binCount E 1 = 0 := by
  simp [binCount]

@[simp] theorem binCount_zero (E : Finset ℕ) : binCount E 0 = 0 := by
  simp [binCount]

theorem binCount_mul (E : Finset ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    binCount E (m * n) = binCount E m + binCount E n := by
  simp [binCount, Nat.factorization_mul hm hn, Finset.sum_add_distrib]

theorem binCount_eq_zero_of_no_factor (E : Finset ℕ) (n : ℕ)
    (h : ∀ p ∈ E, ¬p ∣ n) : binCount E n = 0 := by
  exact Finset.sum_eq_zero fun p hp => Nat.factorization_eq_zero_of_not_dvd (h p hp)

section Labels

variable {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]

/-- A bin label, viewed as an arithmetic function (so its value at zero is zero). -/
noncomputable def binLabel (E : ι → Finset ℕ) (z : ι → R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else ∏ i, z i ^ binCount (E i) n, by simp⟩

@[simp] theorem binLabel_apply_zero (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z 0 = 0 := by simp [binLabel]

theorem binLabel_apply {n : ℕ} (hn : n ≠ 0) (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z n = ∏ i, z i ^ binCount (E i) n := by simp [binLabel, hn]

@[simp] theorem binLabel_apply_one (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z 1 = 1 := by simp [binLabel]

/-- Complete multiplicativity, without a coprimality requirement. -/
theorem binLabel_mul (E : ι → Finset ℕ) (z : ι → R) (m n : ℕ) :
    binLabel E z (m * n) = binLabel E z m * binLabel E z n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [binLabel_apply (mul_ne_zero hm hn), binLabel_apply hm,
    binLabel_apply hn, binCount_mul _ hm hn, pow_add, Finset.prod_mul_distrib]

theorem binLabel_isMultiplicative (E : ι → Finset ℕ) (z : ι → R) :
    (binLabel E z).IsMultiplicative :=
  ⟨binLabel_apply_one E z, fun {_ _} _ => binLabel_mul E z _ _⟩

theorem binLabel_eq_one_of_no_factor (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) :
    binLabel E z u = 1 := by
  simp only [binLabel_apply hu]
  apply Finset.prod_eq_one
  intro i _
  rw [binCount_eq_zero_of_no_factor _ _ (h i), pow_zero]

theorem binLabel_mul_invariant (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) (n : ℕ) :
    binLabel E z (u * n) = binLabel E z n := by
  rw [binLabel_mul, binLabel_eq_one_of_no_factor E z hu h, one_mul]

end Labels

section Bounds

variable {ι : Type*} [Fintype ι] (E : ι → Finset ℕ)

theorem binLabel_nonneg (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (n : ℕ) :
    0 ≤ binLabel E z n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [binLabel_apply hn]
  exact Finset.prod_nonneg fun i _ => pow_nonneg (hz i) _

theorem binLabel_le_one (z : ι → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    binLabel E z n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [binLabel_apply hn]
  exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (hz i).1 _)
    (fun i _ => pow_le_one₀ (hz i).1 (hz i).2)

theorem abs_binLabel_le_one (z : ι → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) : |binLabel E z n| ≤ 1 := by
  rw [abs_of_nonneg (binLabel_nonneg E z (fun i => (hz i).1) n)]
  exact binLabel_le_one E z hz n

theorem norm_binLabel_eq_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {n : ℕ} (hn : n ≠ 0) : ‖binLabel E z n‖ = 1 := by
  simp [binLabel_apply hn, norm_prod, norm_pow, hz]

theorem norm_binLabel_le_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  exact (norm_binLabel_eq_one E z hz hn).le

theorem norm_centered_binLabel_le_two (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (n : ℕ) : ‖binLabel E z n - μ‖ ≤ 2 := by
  calc
    _ ≤ ‖binLabel E z n‖ + ‖μ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_binLabel_le_one E z hz n) hμ
    _ = 2 := by norm_num

theorem centered_binLabel_mul_invariant (z : ι → ℂ) (μ : ℂ)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) (n : ℕ) :
    binLabel E z (u * n) - μ = binLabel E z n - μ := by
  rw [binLabel_mul_invariant E z hu h]

end Bounds

/-- A fixed nonzero integer eventually has no factor in any of the large-prime
bins. The first bin index is at least one, as in the manuscript. -/
theorem primeBin_eventually_no_factor {ι : Type*} (J : ℕ) (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i p, p ∈ primeBin x J (k i) → ¬p ∣ u := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hlarge := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (Filter.eventually_ge_atTop (u : ℝ))
  filter_upwards [hlarge, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxone
  intro i p hp hpdiv
  have hplower : x ^ ((k i : ℝ) / J) < (p : ℝ) :=
    Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hexp : (1 : ℝ) / J ≤ (k i : ℝ) / J :=
    div_le_div_of_nonneg_right (by exact_mod_cast hk i) hJreal.le
  have hpower := Real.rpow_le_rpow_of_exponent_le hxone hexp
  have hpupper : (p : ℝ) ≤ u := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hpdiv
  linarith

/-- The exact eventual multiplier invariance used for uncentered labels. -/
theorem binLabel_eventually_mul_invariant {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → R) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ n : ℕ,
      binLabel (fun i => primeBin x J (k i)) z (u * n) =
        binLabel (fun i => primeBin x J (k i)) z n := by
  filter_upwards [primeBin_eventually_no_factor J hJ k hk hu] with x hx n
  exact binLabel_mul_invariant _ z hu hx n


section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct real interpolation nodes strictly between zero and one. -/
noncomputable def interpolationNode {m : ℕ} (j : Fin m) : ℝ := ((j : ℝ) + 1) / ((m : ℝ) + 1)

theorem interpolationNode_pos {m : ℕ} (j : Fin m) : 0 < interpolationNode j := by
  unfold interpolationNode
  positivity

theorem interpolationNode_mem {m : ℕ} (j : Fin m) :
    interpolationNode j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold interpolationNode
    positivity
  · unfold interpolationNode
    apply (div_le_one (by positivity : 0 < (m : ℝ) + 1)).mpr
    exact_mod_cast Nat.succ_le_succ j.isLt.le

theorem interpolationNode_injective (m : ℕ) :
    Function.Injective (@interpolationNode m) := by
  intro a b h
  apply Fin.ext
  have hden : (m : ℝ) + 1 ≠ 0 := by positivity
  have heq : (a : ℝ) + 1 = (b : ℝ) + 1 := (div_left_inj' hden).mp h
  exact_mod_cast add_right_cancel heq

private theorem tensor_inverse_identity {m : ℕ} (v : Fin m → ℂ)
    (hv : Function.Injective v) (b t : ι → Fin m) :
    (∑ a : ι → Fin m,
      (∏ i, (Matrix.vandermonde v)⁻¹ (b i) (a i)) *
        ∏ i, v (a i) ^ ((t i : Fin m) : ℕ)) = if b = t then 1 else 0 := by
  classical
  have hinv := Matrix.nonsing_inv_mul (Matrix.vandermonde v)
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv))
  calc
    _ = ∑ a : ι → Fin m,
        ∏ i, (Matrix.vandermonde v)⁻¹ (b i) (a i) * v (a i) ^ ((t i : Fin m) : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a : Fin m,
        (Matrix.vandermonde v)⁻¹ (b i) a * v a ^ ((t i : Fin m) : ℕ) :=
      (Fintype.prod_sum (fun (i : ι) (a : Fin m) =>
        (Matrix.vandermonde v)⁻¹ (b i) a * v a ^ ((t i : Fin m) : ℕ))).symm
    _ = ∏ i, if b i = t i then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using
        congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A (b i) (t i)) hinv
    _ = _ := by
      by_cases h : b = t
      · simp [h]
      · rw [ite_eq_right h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Finite tensor interpolation for arbitrary tables on bounded count vectors. -/
theorem exists_bounded_count_interpolation {m : ℕ} (v : Fin m → ℝ)
    (hv : Function.Injective v) (F : (ι → Fin m) → ℂ) :
    ∃ c : (ι → Fin m) → ℂ, ∀ t : ι → Fin m,
      F t = ∑ a : ι → Fin m, c a * ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ) := by
  classical
  let V := Matrix.vandermonde (fun j => (v j : ℂ))
  let c : (ι → Fin m) → ℂ := fun a => ∑ b : ι → Fin m,
    F b * ∏ i, V⁻¹ (b i) (a i)
  refine ⟨c, fun t => ?_⟩
  symm
  calc
    _ = ∑ b : ι → Fin m, F b *
        ∑ a : ι → Fin m, (∏ i, V⁻¹ (b i) (a i)) *
          ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ) := by
      simp only [c, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ι → Fin m, F b * (if b = t then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [show (∑ a : ι → Fin m, (∏ i, V⁻¹ (b i) (a i)) *
          ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ)) = if b = t then 1 else 0 from
        tensor_inverse_identity (fun j => (v j : ℂ)) (Complex.ofReal_injective.comp hv) b t]
    _ = F t := by simp

/-- A centered phase label on bounded count vectors is a fixed finite linear
combination of real multiplicative interpolants with nodes in `[0,1]`. -/
theorem centered_binLabel_interpolation (ζ : ι → ℂ) (μ : ℂ) (J : ℕ) :
    ∃ c : (ι → Fin (J + 1)) → ℂ, ∀ E : ι → Finset ℕ, ∀ n : ℕ, n ≠ 0 →
      (∀ i, binCount (E i) n ≤ J) →
      binLabel E ζ n - μ = ∑ a : ι → Fin (J + 1),
        c a * (binLabel E (fun i => interpolationNode (a i)) n : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_bounded_count_interpolation (@interpolationNode (J + 1))
    (interpolationNode_injective _) (fun b : ι → Fin (J + 1) =>
      (∏ i, ζ i ^ ((b i : Fin (J + 1)) : ℕ)) - μ)
  refine ⟨c, fun E n hn hb => ?_⟩
  let t : ι → Fin (J + 1) := fun i => ⟨binCount (E i) n, Nat.lt_succ_of_le (hb i)⟩
  simpa only [t, binLabel_apply hn, Complex.ofReal_prod, Complex.ofReal_pow] using hc t

end Interpolation

end JointDickman

end OAI
