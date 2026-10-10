import OAI.NumberTheory.Ostmann.Tree.FiniteActionAverage

namespace OAI

/-!
# Correlation over paired finite fibers

The component totals determine equal-cardinality fibers. Cauchy--Schwarz
on their sums, together with invariance under a cycle action, gives the
finite projection reduction before the local quartet bounds are applied.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def fiberSum {Ω T : Type*} [Fintype Ω] [DecidableEq T]
    (τ : Ω → T) (f : Ω → ℂ) (t : T) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x => τ x = t), f x

theorem complex_correlation_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℂ) :
    ‖∑ x : Ω, f x * conj (g x)‖ ^ 2 ≤
      (∑ x : Ω, ‖f x‖ ^ 2) * ∑ x : Ω, ‖g x‖ ^ 2 := by
  have hn : ‖∑ x : Ω, f x * conj (g x)‖ ≤ ∑ x : Ω, ‖f x‖ * ‖g x‖ := by
    simpa only [norm_mul, Complex.norm_conj] using
      norm_sum_le (Finset.univ : Finset Ω) (fun x => f x * conj (g x))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x : Ω => ‖f x‖) (fun x => ‖g x‖)
  have hnn : 0 ≤ ∑ x : Ω, ‖f x‖ * ‖g x‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

/-- A common fiber-size bound controls the energy of the fiber sums. -/
theorem fiberSum_energy_le {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
    (τ : Ω → T) (f : Ω → ℂ) (N : ℕ)
    (hN : ∀ t, (Finset.univ.filter (fun x => τ x = t)).card ≤ N) :
    (∑ t : T, ‖fiberSum τ f t‖ ^ 2) ≤ (N : ℝ) * ∑ x : Ω, ‖f x‖ ^ 2 := by
  have ht (t : T) : ‖fiberSum τ f t‖ ^ 2 ≤
      (N : ℝ) * ∑ x ∈ Finset.univ.filter (fun x => τ x = t), ‖f x‖ ^ 2 := by
    have h := complex_weighted_sum_sq (Finset.univ.filter (fun x => τ x = t))
      (fun _ => 1) f
    simp only [Complex.ofReal_one, one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
      mul_one] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN t)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ t : T, (N : ℝ) *
        ∑ x ∈ Finset.univ.filter (fun x => τ x = t), ‖f x‖ ^ 2 := Finset.sum_le_sum fun t _ => ht t
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) (fun x => ‖f x‖ ^ 2)

/-- A fiber-preserving finite action does not change the fiber sums. -/
theorem fiberSum_actionAverage {G Ω T : Type*} [Group G] [Fintype G]
    [Fintype Ω] [DecidableEq T] [MulAction G Ω]
    (τ : Ω → T) (hτ : ∀ (g : G) x, τ (g • x) = τ x) (f : Ω → ℂ) (t : T) :
    fiberSum τ (finiteActionAverage (G := G) f) t = fiberSum τ f t := by
  have h := finiteActionAverage_correlation (G := G) f
    (fun x => if τ x = t then 1 else 0) (by intro g x; rw [hτ])
  simpa only [apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
    fiberSum, Finset.sum_filter] using h

/-- The squared projection reduction; normalization can be applied afterward. -/
theorem pairedFiber_correlation_sq_le {G Ω T : Type*} [Group G] [Fintype G]
    [Fintype Ω] [Fintype T] [DecidableEq T] [MulAction G Ω]
    (τ : Ω → T) (hτ : ∀ (g : G) x, τ (g • x) = τ x)
    (f g : Ω → ℂ) (N : ℕ)
    (hN : ∀ t, (Finset.univ.filter (fun x => τ x = t)).card ≤ N) :
    ‖∑ t : T, fiberSum τ f t * conj (fiberSum τ g t)‖ ^ 2 ≤
      (N : ℝ) ^ 2 * (∑ x : Ω, ‖finiteActionAverage (G := G) f x‖ ^ 2) *
        ∑ x : Ω, ‖g x‖ ^ 2 := by
  have hF := fiberSum_energy_le τ (finiteActionAverage (G := G) f) N hN
  have hG := fiberSum_energy_le τ g N hN
  have h := complex_correlation_sq_le
    (fiberSum τ (finiteActionAverage (G := G) f)) (fiberSum τ g)
  simp_rw [fiberSum_actionAverage τ hτ f] at h hF
  apply h.trans
  have hb := mul_le_mul hF hG (by positivity) (by positivity)
  convert hb using 1
  ring

/-- Expanding the two fiber sums gives the equal-total paired correlation. -/
theorem pairedFiber_correlation_eq {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
    (τ : Ω → T) (f g : Ω → ℂ) :
    (∑ t : T, fiberSum τ f t * conj (fiberSum τ g t)) =
      ∑ x : Ω, ∑ y : Ω, if τ x = τ y then f x * conj (g y) else 0 := by
  unfold fiberSum
  simp only [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [map_sum, apply_ite, map_zero, Finset.mul_sum, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : τ x = τ y
  · simp [hxy]
  · simp [hxy, Ne.symm hxy]

/-- Probability-normalized form of the finite cycle projection reduction. -/
theorem pairedFiber_normalized_projection {G Ω T : Type*} [Group G] [Fintype G]
    [Fintype Ω] [Nonempty Ω] [Fintype T] [DecidableEq T] [MulAction G Ω]
    (τ : Ω → T) (hτ : ∀ (g : G) x, τ (g • x) = τ x)
    (f g : Ω → ℂ) (N : ℕ) (hNpos : 0 < N)
    (hN : ∀ t, (Finset.univ.filter (fun x => τ x = t)).card ≤ N) :
    ‖((Fintype.card Ω : ℂ) * (N : ℂ))⁻¹ *
      (∑ x : Ω, ∑ y : Ω, if τ x = τ y then f x * conj (g y) else 0)‖ ^ 2 ≤
      ((∑ x : Ω, ‖finiteActionAverage (G := G) f x‖ ^ 2) / (Fintype.card Ω : ℝ)) *
        ((∑ x : Ω, ‖g x‖ ^ 2) / (Fintype.card Ω : ℝ)) := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
  rw [← pairedFiber_correlation_eq, norm_mul, norm_inv, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast, mul_pow]
  have h := mul_le_mul_of_nonneg_left (pairedFiber_correlation_sq_le τ hτ f g N hN)
    (sq_nonneg (((Fintype.card Ω : ℝ) * (N : ℝ))⁻¹))
  convert h using 1
  field_simp

end Ostmann

end OAI
