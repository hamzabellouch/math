import OAI.NumberTheory.Ostmann.Tree.PartitionProducts
import OAI.NumberTheory.Ostmann.Tree.FiberProjection
import OAI.NumberTheory.Ostmann.Characters.CycleMovingPair

namespace OAI

/-! # Projection reduction for two different partitions of the leaves -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem card_pairedMaps {Ω₁ Ω₂ T : Type*}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq T]
    (τ₁ : Ω₁ → T) (τ₂ : Ω₂ → T) (N : ℕ)
    (hN : ∀ t, (Finset.univ.filter (fun y => τ₂ y = t)).card = N) :
    (Finset.univ.filter fun xy : Ω₁ × Ω₂ => τ₁ xy.1 = τ₂ xy.2).card =
      Fintype.card Ω₁ * N := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  have hy (x : Ω₁) : (∑ y : Ω₂, if τ₁ x = τ₂ y then 1 else 0) = N := by
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, eq_comm] using hN (τ₁ x)
  simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem pairedMaps_correlation_eq {Ω₁ Ω₂ T : Type*}
    [Fintype Ω₁] [Fintype Ω₂] [Fintype T] [DecidableEq T]
    (τ₁ : Ω₁ → T) (τ₂ : Ω₂ → T) (f : Ω₁ → ℂ) (g : Ω₂ → ℂ) :
    (∑ t : T, fiberSum τ₁ f t * conj (fiberSum τ₂ g t)) =
      ∑ x : Ω₁, ∑ y : Ω₂, if τ₁ x = τ₂ y then f x * conj (g y) else 0 := by
  unfold fiberSum
  simp only [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [map_sum, apply_ite, map_zero, Finset.mul_sum, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : τ₁ x = τ₂ y
  · simp [hxy]
  · simp [hxy, Ne.symm hxy]

theorem pairedMaps_correlation_sq_le {G Ω₁ Ω₂ T : Type*}
    [Group G] [Fintype G] [Fintype Ω₁] [Fintype Ω₂] [Fintype T]
    [DecidableEq T] [MulAction G Ω₁]
    (τ₁ : Ω₁ → T) (τ₂ : Ω₂ → T) (hτ : ∀ (z : G) x, τ₁ (z • x) = τ₁ x)
    (f : Ω₁ → ℂ) (g : Ω₂ → ℂ) (N : ℕ)
    (hN₁ : ∀ t, (Finset.univ.filter (fun x => τ₁ x = t)).card ≤ N)
    (hN₂ : ∀ t, (Finset.univ.filter (fun x => τ₂ x = t)).card ≤ N) :
    ‖∑ x : Ω₁, ∑ y : Ω₂, if τ₁ x = τ₂ y then f x * conj (g y) else 0‖ ^ 2 ≤
      (N : ℝ) ^ 2 * (∑ x : Ω₁, ‖finiteActionAverage (G := G) f x‖ ^ 2) *
        ∑ y : Ω₂, ‖g y‖ ^ 2 := by
  rw [← pairedMaps_correlation_eq]
  have hF := fiberSum_energy_le τ₁ (finiteActionAverage (G := G) f) N hN₁
  have hG := fiberSum_energy_le τ₂ g N hN₂
  have h := complex_correlation_sq_le
    (fiberSum τ₁ (finiteActionAverage (G := G) f)) (fiberSum τ₂ g)
  simp_rw [fiberSum_actionAverage τ₁ hτ f] at h hF
  apply h.trans
  have hb := mul_le_mul hF hG (by positivity) (by positivity)
  convert hb using 1
  ring

theorem partitionProduct_cycleMultiply {L C G : Type*}
    [Fintype L] [DecidableEq C] [CommGroup G]
    (component : L → C) (sign : L → ℤ)
    (hs : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => component i = c), sign i = 0)
    (z : G) (m : L → G) :
    partitionProduct component (cycleMultiply sign z m) = partitionProduct component m := by
  classical
  funext c
  unfold partitionProduct
  have hprod (f : L → G) : (∏ i : {i : L // component i = c}, f i.1) =
      ∏ i ∈ Finset.univ.filter (fun i => component i = c), f i :=
    (Finset.prod_subtype _ (by simp) f).symm
  rw [hprod, hprod]
  exact cycleMultiply_preserves_product _ sign (hs c) z m

/-- Exact counting normalization of the paired-component projection step. -/
theorem pairedPartitions_projection {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component₁ component₂ : L → C)
    (pivot₁ : ∀ c, {i : L // component₁ i = c})
    (pivot₂ : ∀ c, {i : L // component₂ i = c})
    (sign : L → ℤ)
    (hs : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => component₁ i = c), sign i = 0)
    (f g : (L → G) → ℂ) :
    ‖((Fintype.card (L → G) : ℂ) *
        (Fintype.card G ^ (Fintype.card L - Fintype.card C) : ℕ))⁻¹ *
      (∑ x : L → G, ∑ y : L → G,
        if partitionProduct component₁ x = partitionProduct component₂ y
        then f x * conj (g y) else 0)‖ ^ 2 ≤
      ((∑ x : L → G, ‖cycleAverage sign f x‖ ^ 2) / (Fintype.card (L → G) : ℝ)) *
        ((∑ y : L → G, ‖g y‖ ^ 2) / (Fintype.card (L → G) : ℝ)) := by
  let := leafCycleAction (G := G) sign
  let N := Fintype.card G ^ (Fintype.card L - Fintype.card C)
  have hN : 0 < N := pow_pos Fintype.card_pos _
  have hL : (Fintype.card (L → G) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have h := pairedMaps_correlation_sq_le (G := G)
    (partitionProduct component₁) (partitionProduct component₂)
    (partitionProduct_cycleMultiply component₁ sign hs) f g N
    (fun P => (card_partitionProduct_filter component₁ pivot₁ P).le)
    (fun P => (card_partitionProduct_filter component₂ pivot₂ P).le)
  change ‖((Fintype.card (L → G) : ℂ) * (N : ℂ))⁻¹ * _‖ ^ 2 ≤ _
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast, mul_pow]
  have hscaled := mul_le_mul_of_nonneg_left h
    (sq_nonneg (((Fintype.card (L → G) : ℝ) * (N : ℝ))⁻¹))
  change _ ≤ _ * ((↑N ^ 2 * ∑ x, ‖cycleAverage sign f x‖ ^ 2) * ∑ y, ‖g y‖ ^ 2) at hscaled
  convert hscaled using 1
  field_simp

end Ostmann

end OAI
