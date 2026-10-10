import Mathlib.Data.Nat.PrimeFin
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTransfer
import OAI.NumberTheory.Ostmann.Construction.PrimeProductMatching

namespace OAI

/-! # The common Fourier multiplier on equal-product diagonal fibres -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The cofactor formula written in terms of the integer product, so that
the order of the current prime list is absent. -/
noncomputable def primeProductTransform (g : ∀ p : ℕ, ZMod p → ℂ)
    (D H : ℕ) (s : ℤ) : ℂ :=
  ∏ p ∈ H.primeFactors, g p ((s : ZMod p) * ((D * (H / p) : ℕ) : ZMod p)⁻¹)

theorem primeTuple_image_factors {J : Type*} [Fintype J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) :
    Finset.univ.image p = (∏ j, p j).primeFactors := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · intro hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hp j, Finset.dvd_prod_of_mem p (Finset.mem_univ j),
      (Finset.prod_pos (fun j _ => (hp j).pos)).ne'⟩
  · rintro ⟨hq, hd, _⟩
    obtain ⟨j, rfl⟩ := prime_dvd_prime_product p hp q hq hd
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- Every distinct-prime arrangement has exactly the same transform on a
fixed product/frequency fibre. This justifies extracting it before taking
the squared modulus of the sum over arrangements. -/
theorem movingRegularTransform_eq_primeProduct {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hinj : Function.Injective p)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D : ℕ) (s : ℤ) :
    movingRegularTransform p (fun j => g (p j)) D s =
      primeProductTransform g D (∏ j, p j) s := by
  have hc (j : J) : tupleCofactor p j = (∏ i, p i) / p j := by
    rw [← tupleCofactor_mul p j]
    exact (Nat.mul_div_cancel_left _ (Fact.out : (p j).Prime).pos).symm
  unfold movingRegularTransform primeProductTransform
  rw [← primeTuple_image_factors p (fun j => Fact.out), Finset.prod_image]
  · exact Finset.prod_congr rfl (fun j _ => by rw [hc j])
  · intro i _ j _ hij
    exact hinj hij

theorem movingRegularTransform_order_independent {J K : Type*} [Fintype J] [Fintype K]
    (p : J → ℕ) (q : K → ℕ) [∀ j, Fact (p j).Prime] [∀ k, Fact (q k).Prime]
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hprod : (∏ j, p j) = ∏ k, q k)
    (g : ∀ r : ℕ, ZMod r → ℂ) (D : ℕ) (s : ℤ) :
    movingRegularTransform p (fun j => g (p j)) D s =
      movingRegularTransform q (fun k => g (q k)) D s := by
  rw [movingRegularTransform_eq_primeProduct p hp,
    movingRegularTransform_eq_primeProduct q hq, hprod]

/-- Grouping precedes the absolute value. The transform is constant on
each fibre, so its squared modulus is a nonnegative common multiplier. -/
theorem diagonal_common_transform {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (W : A → ℂ) (G : K → ℂ) :
    (∑ a, ∑ b, if key a = key b then
      (W a * G (key a)) * conj (W b * G (key b)) else 0).re =
      ∑ k, ‖G k‖ ^ 2 * ‖groupedCoefficient key W k‖ ^ 2 := by
  rw [← diagonal_real_eq_sum_sq key W (fun k => ‖G k‖ ^ 2)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : key a = key b
  · rw [ite_eq_left h, ite_eq_left h, ← h, map_mul]
    have hn : G (key a) * conj (G (key a)) = (‖G (key a)‖ ^ 2 : ℝ) := by
      rw [Complex.mul_conj']
      norm_cast
    calc
      _ = (G (key a) * conj (G (key a))) * W a * conj (W b) := by ring
      _ = _ := by rw [hn]; rfl
  · rw [ite_eq_right h, ite_eq_right h]

/-- The giant factor can be discarded after fibre grouping. The remaining
regular multiplier is retained exactly as required in the diagonal norm. -/
theorem diagonal_common_transform_drop_giant {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (W : A → ℂ) (giant regular : K → ℂ)
    (hgiant : ∀ k, ‖giant k‖ ≤ 1) :
    (∑ a, ∑ b, if key a = key b then
      (W a * (giant (key a) * regular (key a))) *
        conj (W b * (giant (key b) * regular (key b))) else 0).re ≤
      ∑ k, ‖regular k‖ ^ 2 * ‖groupedCoefficient key W k‖ ^ 2 := by
  rw [diagonal_common_transform key W (fun k => giant k * regular k)]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [norm_mul, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (hgiant k))

end Ostmann

end OAI
