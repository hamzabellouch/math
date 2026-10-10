import OAI.NumberTheory.JointDickman.Arithmetic.AdditionWindowSieve
import OAI.NumberTheory.JointDickman.Amplification.NumericAdditionWeights
import OAI.NumberTheory.JointDickman.Amplification.PrefixOmissions

namespace OAI

/-! # Summing a class of actual numeric additions

A class fixes the retained coefficient, the opposite coefficient, the lag,
the number of added primes, and a factor-four product window.  The alternative
quotient remains regular.  Its weighted sum is reduced to one progression.
-/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem primePrefix_exponent_mono {B : ℕ} (hB : 1 ≤ B) {g h : ℝ}
    (hgh : g ≤ h) (P : Finset ℕ) : primePrefix B g P ⊆ primePrefix B h P := by
  by_cases hh : h < 1
  · have hg : g < 1 := hgh.trans_lt hh
    simp only [primePrefix,ite_eq_left hg,ite_eq_left hh]
    intro p hp
    obtain ⟨hp,hlog⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp,hlog.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hB) hgh)⟩
  · simp only [primePrefix,ite_eq_right hh]
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl

noncomputable def numericAdditionClass (B L : ℕ) (τ C : ℝ)
    (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (auxiliaryPrimes B).powerset.filter (fun Z => Z.card = d ∧
    W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
    ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p) = b+j*c ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c))

theorem mem_numericAdditionClass {B L e j b d : ℕ} {τ C W : ℝ} {Z : Finset ℕ} :
    Z ∈ numericAdditionClass B L τ C e j b d W ↔
      Z ⊆ auxiliaryPrimes B ∧ Z.card = d ∧
        W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
        ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p) = b+j*c ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
  simp only [numericAdditionClass,mem_filter,mem_powerset]

noncomputable def additionProgressionWeight (B : ℕ) (g : ℝ)
    (e j b z₀ : ℕ) (c₀ : ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
    residueWeight q 0 ((z₀ : ZMod p)+j*n)*residueWeight (1/2) 0 ((c₀ : ZMod p)+e*n))/
      ((z₀ : ℝ)+(j : ℝ)*n)

theorem additionProgressionWeight_nonneg {B e j b z₀ n : ℕ} {g q : ℝ} {c₀ : ℤ}
    (hq : 0 ≤ q) : 0 ≤ additionProgressionWeight B g e j b z₀ c₀ q n := by
  apply div_nonneg _ (by positivity)
  exact prod_nonneg (fun _ _ => mul_nonneg (residueWeight_nonneg _ _ hq)
    (residueWeight_nonneg _ _ (by norm_num)))

/-- The progression parametrization is injective on the squarefree prime
products in a class.  The remaining quotient's regularity supplies exactly
one half-weight factor, before the numeric interval is enlarged. -/
theorem numeric_addition_class_progression_bound {B L k e j b d z₀ : ℕ}
    {τ C W g q : ℝ} {c₀ : ℤ}
    (hB : 1 ≤ B) (hk : k ∈ Icc 1 L) (hg : g ≤ (k : ℝ)/L)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hprogress : ∀ z c : ℕ, e*z = b+j*c →
      z = z₀+j*(z/j) ∧ (c : ℤ) = c₀+(e : ℤ)*((z/j : ℕ) : ℤ)) :
    (∑ Z ∈ numericAdditionClass B L τ C e j b d W,
      (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
      (((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2))*
        ∑ n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j),
          additionProgressionWeight B g e j b z₀ c₀ q n := by
  let A := numericAdditionClass B L τ C e j b d W
  let f : Finset ℕ → ℕ := fun Z => (∏ p ∈ Z, p)/j
  let F := additionProgressionWeight B g e j b z₀ c₀ q
  let a := ((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hf (Z : Finset ℕ) (hZ : Z ∈ A) : f Z ∈
      Ico (additionIntervalLower W j) (additionIntervalUpper W j) := by
    obtain ⟨_,_,hlo,hhi,_⟩ := mem_numericAdditionClass.mp hZ
    exact additionInterval_contains hlo hhi
  have hinj : Set.InjOn f (↑A : Set (Finset ℕ)) := by
    intro Z hZ V hV heq
    obtain ⟨hZ,_,_,_,c,_,hc,_⟩ := mem_numericAdditionClass.mp hZ
    obtain ⟨hV,_,_,_,a',_,ha',_⟩ := mem_numericAdditionClass.mp hV
    have hz := (hprogress _ _ hc).1
    have hv := (hprogress _ _ ha').1
    apply primeProduct_injective (auxiliaryPrimes_prime B) hZ hV
    calc
      _ = z₀+j*f Z := hz
      _ = z₀+j*f V := by rw [heq]
      _ = _ := hv.symm
  have hpoint (Z : Finset ℕ) (hZ : Z ∈ A) :
      (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ) ≤ a*F (f Z) := by
    obtain ⟨hZ,hd,_,_,c,hc0,hc,hreg⟩ := mem_numericAdditionClass.mp hZ
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
    have hquot (p : ℕ) : (c : ZMod p) = (c₀ : ZMod p)+e*(f Z : ℕ) := by
      have ht := congrArg (fun x : ℤ => (x : ZMod p)) hcq
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using ht
    have hden : ((∏ p ∈ Z, p : ℕ) : ℝ) = (z₀ : ℝ)+(j : ℝ)*(f Z : ℕ) := by
      exact_mod_cast hz
    have heq : (1/2 : ℝ)^d = ((1/2 : ℝ)/q)^d*q^d := by
      rw [← mul_pow,div_mul_cancel₀ _ hq.ne']
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_left hmajor (show 0 ≤ ((1/2 : ℝ)/q)^d by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ ((∏ p ∈ Z, p : ℕ) : ℝ) by positivity)
    refine hdiv.trans_eq ?_
    dsimp only [a,F,additionProgressionWeight]
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
        exact hf Z hZ) (fun _ _ _ => additionProgressionWeight_nonneg hq.le)) ha

end JointDickman

end OAI
