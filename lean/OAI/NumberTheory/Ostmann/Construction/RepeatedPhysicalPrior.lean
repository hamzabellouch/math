import OAI.NumberTheory.Ostmann.Construction.RepeatedPhysicalTests
import OAI.NumberTheory.Ostmann.Construction.PrimeTupleFiber
import OAI.NumberTheory.Ostmann.Construction.HarmonicRepeatedMass

namespace OAI

/-! # Removing repetitions under the original mixed prime priors -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- Summing the reciprocal weight of the distinct values costs at most
`n^n`, even for tuples which have singleton values. -/
theorem tuple_distinct_weight_exp {A : Type*} [Fintype A] (n : ℕ)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ x : Fin n → A, ∏ a ∈ Finset.univ.image x, w a) ≤
      (n : ℝ) ^ n * Real.exp (∑ a, w a) := by
  have hmaps (x : Fin n → A) (_hx : x ∈ Finset.univ) :
      Finset.univ.image x ∈ (Finset.univ : Finset A).powerset := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber (S : Finset A) :
      (∑ x ∈ (Finset.univ : Finset (Fin n → A)).filter
        (fun x => Finset.univ.image x = S), ∏ a ∈ Finset.univ.image x, w a) ≤
      (n : ℝ) ^ n * ∏ a ∈ S, w a := by
    let T := (Finset.univ : Finset (Fin n → A)).filter (fun x => Finset.univ.image x = S)
    have hc : T.card ≤ n ^ n := tuple_range_fiber_card_le n S
    calc
      _ = ∑ _x ∈ T, ∏ a ∈ S, w a := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = (T.card : ℝ) * ∏ a ∈ S, w a := by simp
      _ ≤ _ := by
        simpa only [Nat.cast_pow] using mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr hc : (T.card : ℝ) ≤ (n ^ n : ℕ))
          (Finset.prod_nonneg (fun a _ => hw a))
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset A).powerset, (n : ℝ) ^ n * ∏ a ∈ S, w a :=
      Finset.sum_le_sum (fun S _ => hfiber S)
    _ = (n : ℝ) ^ n * ∏ a, (1 + w a) := by
      rw [← Finset.mul_sum, ← Finset.prod_one_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.prod_one_add_le_exp_sum Finset.univ hw) (by positivity)

/-- The original smooth/harmonic marginal bounds and the physical repeated-
test estimate imply the error in (7.3), retaining every normalizer. -/
theorem repeated_physical_prior_bound_at {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i q, ∑ x, F i q x = 0)
    (henergy : ∀ i (q : P), ∑ x, ‖F i q x‖ ^ 2 ≤ (q : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (E : Finset (Fin n → P)) (hE : ∀ x ∈ E, ¬ Function.Injective x)
    (hsmall : ∀ x ∈ E, ∀ i, H * R < (x i : ℝ))
    (hprod : ∀ x ∈ E, X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x ∈ E, (∏ i, (x i : ℝ)) ≤ X * R)
    (w : (Fin n → P) → ℂ) (hw : ∀ x ∈ E, ‖w x‖ ≤ 1) :
    ‖∑ x ∈ E, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) := by
  classical
  have hCprod : 0 ≤ ∏ i, C i := Finset.prod_nonneg (fun i _ => hC i)
  let B := Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, C i) * Real.exp (-Δ / 2))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hterm (x : Fin n → P) (hx : x ∈ E) :
      ‖(productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
        B * ∏ p ∈ Finset.univ.image x, (p : ℝ)⁻¹ := by
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp (hE x hx)
    have hs := physicalTupleSum_repeated_bound_used P hP x F
      (fun i => hmean i (x i)) (fun i => henergy i (x i)) ψ X H R hX hR hsupp
      (hsmall x hx) (hupper x hx) i j hij heq
    let M : ℝ := ∏ i, (x i : ℝ)
    let Q : ℝ := ∏ p ∈ Finset.univ.image x, (p : ℝ)
    have hM : 0 < M := Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hP (x i) (x i).property).pos)
    have hQ : 0 < Q := Finset.prod_pos (fun p _ => Nat.cast_pos.mpr (hP p p.property).pos)
    have hroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    have hpoint := prime_tuple_prior_point_bound P hP μ C hμ hbound x
    have hnorm : ‖(productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
        ((∏ i, C i) * M⁻¹) * (X * ‖𝓕 ψ 0‖ * (Real.sqrt M / Q)) := by
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (productPrior_nonneg μ hμ x)]
      have hfirst : productPrior μ x * ‖w x‖ ≤ (∏ i, C i) * M⁻¹ := by
        simpa only [mul_one] using mul_le_mul hpoint (hw x hx) (norm_nonneg _)
          (mul_nonneg hCprod (inv_nonneg.mpr hM.le))
      exact mul_le_mul hfirst hs (norm_nonneg _) (by positivity)
    have hid : ((∏ i, C i) * M⁻¹) * (X * ‖𝓕 ψ 0‖ * (Real.sqrt M / Q)) =
        (X * (Real.sqrt M)⁻¹) * (‖𝓕 ψ 0‖ * (∏ i, C i)) * Q⁻¹ := by
      have hsq := Real.sq_sqrt hM.le
      field_simp [hM.ne', hQ.ne', hroot.ne']
      linear_combination (∏ i, C i) * ‖𝓕 ψ 0‖ * hsq
    have hi : (Real.sqrt M)⁻¹ ≤ (Real.sqrt (X * Real.exp Δ))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (mul_pos hX (Real.exp_pos _)))
        (Real.sqrt_le_sqrt (hprod x hx))
    calc
      _ ≤ (X * (Real.sqrt M)⁻¹) * (‖𝓕 ψ 0‖ * (∏ i, C i)) * Q⁻¹ := hnorm.trans_eq hid
      _ ≤ (X * (Real.sqrt (X * Real.exp Δ))⁻¹) * (‖𝓕 ψ 0‖ * (∏ i, C i)) * Q⁻¹ := by
        gcongr
      _ = _ := by
        rw [inverse_sqrt_exp_product X Δ hX, Finset.prod_inv_distrib]
        dsimp only [B, Q]
        rw [show -Δ / 2 = -(Δ / 2) by ring]
        ring
  calc
    _ ≤ ∑ x ∈ E, B * ∏ p ∈ Finset.univ.image x, (p : ℝ)⁻¹ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = B * ∑ x ∈ E, ∏ p ∈ Finset.univ.image x, (p : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ B * ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun x _ _ => Finset.prod_nonneg (fun p _ => by positivity))).trans
      convert tuple_distinct_weight_exp n (fun p : P => (p : ℝ)⁻¹) (fun _ => by positivity) using 1
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.prod_congr
      · ext p
        simp only [Finset.mem_image]
      · intro p _
        rfl
    _ = _ := by
      dsimp only [B]
      rw [show -Δ / 2 = -(Δ / 2) by ring]
      rw [Real.exp_sub, Real.exp_neg]
      ring

theorem repeated_physical_prior_bound {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (hmean : ∀ i q, ∑ x, F i q x = 0)
    (henergy : ∀ i (q : P), ∑ x, ‖F i q x‖ ^ 2 ≤ (q : ℝ))
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p : P, H * R < (p : ℝ))
    (E : Finset (Fin n → P)) (hE : ∀ x ∈ E, ¬ Function.Injective x)
    (hprod : ∀ x ∈ E, X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x ∈ E, (∏ i, (x i : ℝ)) ≤ X * R)
    (w : (Fin n → P) → ℂ) (hw : ∀ x ∈ E, ‖w x‖ ≤ 1) :
    ‖∑ x ∈ E, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) := by
  exact repeated_physical_prior_bound_at P hP μ C hμ hC hbound F hmean henergy
    ψ X H R Δ hX hR hsupp E hE (fun x _ i => hsmall (x i)) hprod hupper w hw

end Ostmann

end OAI
