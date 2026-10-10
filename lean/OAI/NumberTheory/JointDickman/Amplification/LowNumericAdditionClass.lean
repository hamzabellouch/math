import OAI.NumberTheory.JointDickman.Arithmetic.LowAdditionSieve
import OAI.NumberTheory.JointDickman.Amplification.NumericAdditionClass

namespace OAI

/-! # Squarefree low-endpoint additions on a decreasing quotient progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def lowNumericAdditionClass (B L : ℕ) (τ C : ℝ)
    (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (auxiliaryPrimes B).powerset.filter (fun Z => Z.card = d ∧
    W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
    ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p)+j*c = b ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c))

theorem mem_lowNumericAdditionClass {B L e j b d : ℕ} {τ C W : ℝ} {Z : Finset ℕ} :
    Z ∈ lowNumericAdditionClass B L τ C e j b d W ↔
      Z ⊆ auxiliaryPrimes B ∧ Z.card = d ∧
        W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
        ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p)+j*c = b ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
  simp only [lowNumericAdditionClass,mem_filter,mem_powerset]

/-- The progression parametrization is injective on the squarefree prime
products in a class.  The remaining quotient's regularity supplies exactly
one half-weight factor, before the numeric interval is enlarged. -/
theorem low_numeric_addition_class_progression_bound {B L k e j b d z₀ : ℕ}
    {τ C W g q : ℝ} {c₀ : ℤ}
    (hB : 1 ≤ B) (hk : k ∈ Icc 1 L) (hg : g ≤ (k : ℝ)/L)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hprogress : ∀ z c : ℕ, e*z+j*c = b →
      z = z₀+j*(z/j) ∧ (c : ℤ) = c₀-(e : ℤ)*((z/j : ℕ) : ℤ)) :
    (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
      (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
      (((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2))*
        ∑ n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j),
          lowAdditionProgressionWeight B g e j b z₀ c₀ q n := by
  let A := lowNumericAdditionClass B L τ C e j b d W
  let f : Finset ℕ → ℕ := fun Z => (∏ p ∈ Z, p)/j
  let F := lowAdditionProgressionWeight B g e j b z₀ c₀ q
  let a := ((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hf (Z : Finset ℕ) (hZ : Z ∈ A) : f Z ∈
      Ico (additionIntervalLower W j) (additionIntervalUpper W j) := by
    obtain ⟨_,_,hlo,hhi,_⟩ := mem_lowNumericAdditionClass.mp hZ
    exact additionInterval_contains hlo hhi
  have hinj : Set.InjOn f (↑A : Set (Finset ℕ)) := by
    intro Z hZ V hV heq
    obtain ⟨hZ,_,_,_,c,_,hc,_⟩ := mem_lowNumericAdditionClass.mp hZ
    obtain ⟨hV,_,_,_,a',_,ha',_⟩ := mem_lowNumericAdditionClass.mp hV
    have hz := (hprogress _ _ hc).1
    have hv := (hprogress _ _ ha').1
    apply primeProduct_injective (auxiliaryPrimes_prime B) hZ hV
    calc
      _ = z₀+j*f Z := hz
      _ = z₀+j*f V := by rw [heq]
      _ = _ := hv.symm
  have hpoint (Z : Finset ℕ) (hZ : Z ∈ A) :
      (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ) ≤ a*F (f Z) := by
    obtain ⟨hZ,hd,_,_,c,hc0,hc,hreg⟩ := mem_lowNumericAdditionClass.mp hZ
    obtain ⟨hz,hcq⟩ := hprogress _ _ hc
    let P := primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b
    have hP : P ⊆ primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B) :=
      sdiff_subset.trans (primePrefix_exponent_mono hB hg _)
    have hmajor := regular_numeric_addition_majorant Z P hc0.ne' hk hreg hP
      (fun p hp => auxiliaryPrimes_prime B p (hZ hp)) hq.le hq1
    rw [hd] at hmajor
    have hprod (p : ℕ) : ((∏ r ∈ Z, r : ℕ) : ZMod p) =
        (z₀ : ZMod p)+j*(f Z : ℕ) := by
      have ht := congrArg (fun n : ℕ => (n : ZMod p)) hz
      simpa only [Nat.cast_add,Nat.cast_mul] using ht
    have hquot (p : ℕ) : (c : ZMod p) = (c₀ : ZMod p)-e*(f Z : ℕ) := by
      have ht := congrArg (fun x : ℤ => (x : ZMod p)) hcq
      simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using ht
    have hden : ((∏ p ∈ Z, p : ℕ) : ℝ) = (z₀ : ℝ)+(j : ℝ)*(f Z : ℕ) := by
      exact_mod_cast hz
    have heq : (1/2 : ℝ)^d = ((1/2 : ℝ)/q)^d*q^d := by
      rw [← mul_pow,div_mul_cancel₀ _ hq.ne']
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_left hmajor (show 0 ≤ ((1/2 : ℝ)/q)^d by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ ((∏ p ∈ Z, p : ℕ) : ℝ) by positivity)
    refine hdiv.trans_eq ?_
    dsimp only [a,F,lowAdditionProgressionWeight]
    simp_rw [hprod,hquot]
    rw [hden]
    dsimp only [P]
    ring
  calc
    _ ≤ ∑ Z ∈ A, a*F (f Z) := sum_le_sum hpoint
    _ = a*∑ Z ∈ A, F (f Z) := (mul_sum _ _ _).symm
    _ = a*∑ n ∈ A.image f, F n := by rw [sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (by
        intro n hn
        obtain ⟨Z,hZ,rfl⟩ := mem_image.mp hn
        exact hf Z hZ) (fun _ _ _ => lowAdditionProgressionWeight_nonneg hq.le)) ha

end JointDickman

end OAI
