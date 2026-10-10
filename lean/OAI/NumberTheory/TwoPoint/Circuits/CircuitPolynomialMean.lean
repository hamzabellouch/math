import OAI.NumberTheory.TwoPoint.Circuits.CircuitClauseIndependence

namespace OAI

/-! The polynomial-expectation step in Braverman's proof (Proposition 6,
author version https://www.cs.toronto.edu/~mbraverm/FoolAC0v7.pdf).
On the Boolean cube, multilinear degree is represented by Walsh support.
Preservation of low-degree expectations gives a sandwich criterion for
bounded-independence comparison. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {n : ℕ}

def cubeRestrict (S : Finset (Fin n)) (x : BooleanCube n) : S → Bool := fun i => x i

noncomputable def cubeExtend (S : Finset (Fin n)) (z : S → Bool) : BooleanCube n :=
  fun i => if hi : i ∈ S then z ⟨i, hi⟩ else false

lemma cubePattern_extend (S : Finset (Fin n)) (z : S → Bool) (x : BooleanCube n) :
    cubePattern S (cubeExtend S z) x = if cubeRestrict S x = z then 1 else 0 := by
  have heq : (∀ i ∈ S, x i = cubeExtend S z i) ↔ cubeRestrict S x = z := by
    constructor
    · intro h
      funext i
      simpa only [cubeRestrict, cubeExtend, dite_eq_left i.property] using h i i.property
    · intro h i hi
      have hh := congrFun h ⟨i, hi⟩
      simpa only [cubeRestrict, cubeExtend, dite_eq_left hi] using hh
  simp only [cubePattern, heq]

lemma cube_function_partition (S : Finset (Fin n)) (φ : (S → Bool) → ℝ)
    (x : BooleanCube n) :
    φ (cubeRestrict S x) = ∑ z : S → Bool, φ z * cubePattern S (cubeExtend S z) x := by
  simp only [cubePattern_extend]
  simp

lemma TWiseUniformDensity.restricted_mean {t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (S : Finset (Fin n)) (hS : S.card ≤ t)
    (φ : (S → Bool) → ℝ) :
    cubeAverage (fun x => g x * φ (cubeRestrict S x)) =
      (∑ z : S → Bool, φ z) / (2 : ℝ) ^ S.card := by
  have heq : (fun x => g x * φ (cubeRestrict S x)) =
      fun x => ∑ z : S → Bool, φ z * (g x * cubePattern S (cubeExtend S z) x) := by
    funext x
    rw [cube_function_partition S φ x, mul_sum]
    apply sum_congr rfl
    intro z _
    ring
  rw [heq, cubeAverage_sum]
  simp_rw [cubeAverage_mul_const, hg S hS]
  simp only [div_eq_mul_inv, sum_mul, one_mul]

lemma uniformDensity_tWise (t : ℕ) :
    TWiseUniformDensity (fun _ : BooleanCube n => (1 : ℝ)) t := by
  intro S _ z
  simpa only [one_mul] using cubeAverage_pattern S z

lemma TWiseUniformDensity.restricted_expectation {t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (S : Finset (Fin n)) (hS : S.card ≤ t)
    (φ : (S → Bool) → ℝ) :
    cubeAverage (fun x => g x * φ (cubeRestrict S x)) =
      cubeAverage (fun x => φ (cubeRestrict S x)) := by
  rw [hg.restricted_mean S hS φ]
  simpa only [one_mul] using ((uniformDensity_tWise t).restricted_mean S hS φ).symm

lemma TWiseUniformDensity.walsh_expectation {t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (S : Finset (Fin n)) (hS : S.card ≤ t) :
    cubeAverage (fun x => g x * walsh S x) = cubeAverage (walsh S) := by
  have heq (x : BooleanCube n) :
      walsh S x = ∏ i : S, booleanSign (cubeRestrict S x i) := by
    simp only [walsh, cubeRestrict]
    exact (Finset.prod_attach S (fun i => booleanSign (x i))).symm
  have hfun : walsh S = fun x => ∏ i : S, booleanSign (cubeRestrict S x i) := funext heq
  rw [hfun]
  exact hg.restricted_expectation S hS (fun z => ∏ i : S, booleanSign (z i))

/-- A concrete finite representation of a real multilinear polynomial of
degree at most t, restricted to the Boolean cube. -/
def WalshDegreeLE (F : BooleanCube n → ℝ) (t : ℕ) : Prop :=
  ∃ a : Finset (Fin n) → ℝ, ∀ x,
    F x = ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ t),
      a S * walsh S x

lemma TWiseUniformDensity.polynomial_expectation {t : ℕ} {g F : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hF : WalshDegreeLE F t) :
    cubeAverage (fun x => g x * F x) = cubeAverage F := by
  obtain ⟨a, ha⟩ := hF
  have hfun : F = fun x => ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
      (fun S => S.card ≤ t), a S * walsh S x := funext ha
  rw [hfun]
  simp_rw [mul_sum]
  rw [cubeAverage_sum, cubeAverage_sum]
  apply sum_congr rfl
  intro S hS
  have hs : S.card ≤ t := (mem_filter.mp hS).2
  have heq : (fun x => g x * (a S * walsh S x)) =
      fun x => a S * (g x * walsh S x) := by funext x; ring
  rw [heq, cubeAverage_mul_const, cubeAverage_mul_const, hg.walsh_expectation S hs]

/-- Two low-degree pointwise bounds with small uniform gap also bound every
t-wise independent law. This criterion supplies the finite probability
interface for the analytic polynomial construction. -/
theorem TWiseUniformDensity.sandwich_error {t : ℕ} {g F P Q : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hn : ∀ x, 0 ≤ g x)
    (hP : WalshDegreeLE P t) (hQ : WalshDegreeLE Q t)
    (hPF : ∀ x, P x ≤ F x) (hFQ : ∀ x, F x ≤ Q x)
    {ε : ℝ} (hgap : cubeAverage (fun x => Q x - P x) ≤ ε) :
    |cubeAverage (fun x => g x * F x) - cubeAverage F| ≤ ε := by
  have hp := cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left (hPF x) (hn x))
  have hq := cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left (hFQ x) (hn x))
  rw [hg.polynomial_expectation hP] at hp
  rw [hg.polynomial_expectation hQ] at hq
  have hp' := cubeAverage_mono hPF
  have hq' := cubeAverage_mono hFQ
  rw [cubeAverage_sub] at hgap
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TwoPointCorrelations

end OAI
