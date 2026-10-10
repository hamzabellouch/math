import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularDiagonal
import OAI.NumberTheory.Ostmann.Preliminaries.WeightedNormTriangle

namespace OAI

/-! # The original diagonal with its common transform and original prior -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Only the finitely many attained keys are used; products and frequencies
need not have finite ambient types. -/
theorem finite_diagonal_common_transform {A K : Type*} [Fintype A] [DecidableEq K]
    (key : A → K) (W : A → ℂ) (G : K → ℂ) :
    (∑ a, ∑ b, if key a = key b then
      (W a * G (key a)) * conj (W b * G (key b)) else 0).re =
      ∑ k ∈ Finset.univ.image key, ‖G k‖ ^ 2 * ‖groupedCoefficient key W k‖ ^ 2 := by
  let T := Finset.univ.image key
  let k : A → T := fun a => ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have h := diagonal_common_transform k W (fun x => G x.val)
  have hgroup (x : T) : groupedCoefficient k W x = groupedCoefficient key W x.val := by
    unfold groupedCoefficient
    apply Finset.sum_congr rfl
    intro a _
    rw [show k a = x ↔ key a = x.val from Subtype.ext_iff]
  calc
    _ = ∑ x : T, ‖G x.val‖ ^ 2 * ‖groupedCoefficient key W x.val‖ ^ 2 := by
      simpa only [hgroup, k, Subtype.mk.injEq] using h
    _ = _ := by
      simpa only [T] using Finset.sum_coe_sort T
        (fun x : K => ‖G x‖ ^ 2 * ‖groupedCoefficient key W x‖ ^ 2)

/-- The actual regular diagonal groups every ordered arrangement on the
same product/frequency fibre before taking its squared modulus. -/
theorem moving_regular_pivot_diagonal {A H : Type*} [Fintype A] [Fintype H]
    (p : A → H → ℕ) [∀ a i, Fact (p a i).Prime]
    (g : ∀ q : ℕ, ZMod q → ℂ) (M : ℕ) (v : A → ℤ) (W : A → ℂ)
    (hinj : ∀ a, W a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, W a ≠ 0 → v a ≠ 0)
    (hsmall : ∀ a, W a ≠ 0 → ∀ i, (v a).natAbs < p a i) :
    (pivotDiagonal (fun a => ∏ i, p a i) v
      (fun a => W a * movingRegularTransform (p a) (fun i => g (p a i)) M (v a))).re =
      ∑ k ∈ Finset.univ.image (fun a => ((∏ i, p a i), v a)),
        ‖primeProductTransform g M k.1 k.2‖ ^ 2 *
          ‖groupedCoefficient (fun a => ((∏ i, p a i), v a)) W k‖ ^ 2 := by
  let key := fun a => ((∏ i, p a i), v a)
  let T := fun k : ℕ × ℤ => primeProductTransform g M k.1 k.2
  have he : pivotDiagonal (fun a => ∏ i, p a i) v
      (fun a => W a * movingRegularTransform (p a) (fun i => g (p a i)) M (v a)) =
      ∑ a, ∑ b, if key a = key b then (W a * T (key a)) * conj (W b * T (key b)) else 0 := by
    unfold pivotDiagonal
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases ha : W a = 0
    · simp only [ha, zero_mul, ite_self]
    by_cases hb : W b = 0
    · simp only [hb, zero_mul, map_zero, mul_zero, ite_self]
    have hiff := pivot_zero_numerator_iff (∏ i, p a i) (∏ i, p b i)
      (Finset.prod_pos (fun i _ => (Fact.out : (p a i).Prime).pos)) (v a) (v b)
      (hv a ha) (hv b hb)
      (fun q hq hd => by
        obtain ⟨i, rfl⟩ := prime_dvd_prime_product (p a) (fun i => Fact.out) q hq hd
        exact hsmall a ha i)
      (fun q hq hd => by
        obtain ⟨i, rfl⟩ := prime_dvd_prime_product (p b) (fun i => Fact.out) q hq hd
        exact hsmall b hb i)
    have hk : (v a * (∏ i, p b i) - v b * (∏ i, p a i) = 0) ↔ key a = key b := by
      simpa only [key, Prod.mk.injEq] using hiff
    simp only [hk]
    rw [movingRegularTransform_eq_primeProduct (p a) (hinj a ha),
      movingRegularTransform_eq_primeProduct (p b) (hinj b hb)]
  rw [he]
  simpa only [key, T] using finite_diagonal_common_transform key W T

/-- Cauchy on one fibre retains its original prior and charges the other
branch only through that fibre's original mass. -/
theorem grouped_weighted_norm_sq_le {A K : Type*} [Fintype A]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (k : K) (θ : ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : (∑ a, if key a = k then μ a else 0) ≤ θ) :
    ‖groupedCoefficient key (fun a => (μ a : ℂ) * W a) k‖ ^ 2 ≤
      θ * ∑ a, if key a = k then μ a * ‖W a‖ ^ 2 else 0 := by
  let S := Finset.univ.filter (fun a => key a = k)
  have h := weighted_correlation_le_sqrt_energy S μ W (fun _ => 1)
    (fun a _ => hμ a)
  simp only [map_one, mul_one, norm_one, one_pow] at h
  have hE : 0 ≤ ∑ a ∈ S, μ a * ‖W a‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hμ a) (sq_nonneg _)
  have hM : 0 ≤ ∑ a ∈ S, μ a := Finset.sum_nonneg fun a _ => hμ a
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hM] at hsq
  have hmass' : (∑ a ∈ S, μ a) ≤ θ := by simpa only [S, Finset.sum_filter] using hmass
  have hb := hsq.trans (mul_le_mul_of_nonneg_left hmass' hE)
  simpa only [S, Finset.sum_filter, groupedCoefficient, mul_comm] using hb

/-- The diagonal energy after grouping, suitable for the prior atom bound
and the subsequent regular-prime cancellation. -/
theorem weighted_diagonal_common_transform_le {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (G : K → ℂ) (θ : K → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∀ k, (∑ a, if key a = k then μ a else 0) ≤ θ k) :
    (∑ a, ∑ b, if key a = key b then
      ((μ a : ℂ) * W a * G (key a)) * conj ((μ b : ℂ) * W b * G (key b)) else 0).re ≤
      ∑ a, μ a * θ (key a) * ‖W a * G (key a)‖ ^ 2 := by
  rw [diagonal_common_transform key (fun a => (μ a : ℂ) * W a) G]
  calc
    _ ≤ ∑ k, ‖G k‖ ^ 2 * (θ k * ∑ a, if key a = k then μ a * ‖W a‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (grouped_weighted_norm_sq_le key μ W k (θ k) hμ (hmass k))
        (sq_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (key a)]
      · simp only [ite_true, norm_mul, mul_pow]
        ring
      · intro k _ hk
        rw [ite_eq_right (Ne.symm hk), mul_zero, mul_zero]
      · simp

/-- The same fibre estimate for unbounded integer product/frequency keys.
Only the finite image of the sample space is introduced as a finite type. -/
theorem finite_weighted_diagonal_common_transform_le {A K : Type*}
    [Fintype A] [DecidableEq K]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (G : K → ℂ) (θ : K → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∀ k, (∑ a, if key a = k then μ a else 0) ≤ θ k) :
    (∑ a, ∑ b, if key a = key b then
      ((μ a : ℂ) * W a * G (key a)) * conj ((μ b : ℂ) * W b * G (key b)) else 0).re ≤
      ∑ a, μ a * θ (key a) * ‖W a * G (key a)‖ ^ 2 := by
  let T := Finset.univ.image key
  let k : A → T := fun a => ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have h := weighted_diagonal_common_transform_le
    k μ W (fun x => G x.val) (fun x => θ x.val) hμ (fun x => by
      simpa only [Subtype.ext_iff, k] using hmass x.val)
  simpa only [k, Subtype.mk.injEq] using h

theorem finite_grouped_weighted_energy_le {A K : Type*}
    [Fintype A] [DecidableEq K]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (G : K → ℂ) (θ : K → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∀ k, (∑ a, if key a = k then μ a else 0) ≤ θ k) :
    (∑ k ∈ Finset.univ.image key, ‖G k‖ ^ 2 *
      ‖groupedCoefficient key (fun a => (μ a : ℂ) * W a) k‖ ^ 2) ≤
      ∑ a, μ a * θ (key a) * ‖W a * G (key a)‖ ^ 2 := by
  rw [← finite_diagonal_common_transform]
  exact finite_weighted_diagonal_common_transform_le key μ W G θ hμ hmass

/-- The actual giant-transfer diagonal is bounded using one original
prior and one matching-fibre mass, with no frequency-count loss. -/
theorem moving_regular_pivot_diagonal_le {A H : Type*} [Fintype A] [Fintype H]
    (p : A → H → ℕ) [∀ a i, Fact (p a i).Prime]
    (g : ∀ q : ℕ, ZMod q → ℂ) (M : ℕ) (v : A → ℤ)
    (μ : A → ℝ) (W : A → ℂ) (θ : ℕ × ℤ → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hinj : ∀ a, (μ a : ℂ) * W a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, (μ a : ℂ) * W a ≠ 0 → v a ≠ 0)
    (hsmall : ∀ a, (μ a : ℂ) * W a ≠ 0 → ∀ i, (v a).natAbs < p a i)
    (hmass : ∀ k, (∑ a, if ((∏ i, p a i), v a) = k then μ a else 0) ≤ θ k) :
    (pivotDiagonal (fun a => ∏ i, p a i) v
      (fun a => (μ a : ℂ) * W a *
        movingRegularTransform (p a) (fun i => g (p a i)) M (v a))).re ≤
      ∑ a, μ a * θ ((∏ i, p a i), v a) *
        ‖W a * primeProductTransform g M (∏ i, p a i) (v a)‖ ^ 2 := by
  rw [moving_regular_pivot_diagonal p g M v (fun a => (μ a : ℂ) * W a) hinj hv hsmall]
  exact finite_grouped_weighted_energy_le (fun a => ((∏ i, p a i), v a)) μ W
    (fun k => primeProductTransform g M k.1 k.2) θ hμ hmass

end Ostmann

end OAI
