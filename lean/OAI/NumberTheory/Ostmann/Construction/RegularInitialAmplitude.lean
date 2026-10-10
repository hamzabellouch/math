import OAI.NumberTheory.Ostmann.Characters.RegularTuplePoisson
import OAI.NumberTheory.Ostmann.Construction.RepeatedPhysicalPrior
import OAI.NumberTheory.Ostmann.Construction.PrimePhysicalTest

namespace OAI

/-! # The original initial Fourier amplitude and repeated-prime error -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def primeTupleFourierCoefficient {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (x : Fin n → P) : ℂ :=
  ∑ v ∈ transferFrequencyRange N,
    normalizedFourierProfile (fun t => 𝓕 ψ t) v ((∏ i, (x i : ℕ)) / X) *
      movingRegularTransform (fun i => (x i : ℕ)) (fun i => densityFourier (F i (x i))) 1 v

noncomputable def regularInitialAmplitude {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (w : (Fin n → P) → ℂ) : ℂ :=
  ∑ x : Fin n → P, (productPrior μ x : ℂ) * w x *
    if Function.Injective x then primeTupleFourierCoefficient P F ψ X N x else 0

/-- Before estimating anything, the retained Fourier amplitude and the
discarded repeated tuples sum to the original physical statistic exactly. -/
theorem initial_physical_fourier_decomposition {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (w : (Fin n → P) → ℂ)
    (hcut : ∀ x, w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) :
    (∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X) =
      (Real.sqrt X : ℂ) * regularInitialAmplitude P μ F ψ X N w +
        ∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
          (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X := by
  unfold regularInitialAmplitude
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hw : w x = 0
  · simp only [hw, mul_zero, zero_mul, ite_self, add_zero]
  by_cases hx : Function.Injective x
  · have hc : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
      intro i j hij
      exact (Nat.coprime_primes (hP (x i) (x i).property)
        (hP (x j) (x j).property)).mpr (fun h => hij (hx (Subtype.ext h)))
    let : NeZero (∏ i, (x i : ℕ)) :=
      ⟨(Finset.prod_pos (fun i _ => (hP (x i) (x i).property).pos)).ne'⟩
    have hpoisson := tuple_regular_poisson_profile (fun i => (x i : ℕ)) hc
      (fun i => F i (x i)) ψ X H hX N (hcut x hw) hsupp
    change physicalTupleSum P x F ψ X / (Real.sqrt X : ℂ) =
      primeTupleFourierCoefficient P F ψ X N x at hpoisson
    have hroot : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
    have he := (div_eq_iff hroot).mp hpoisson
    simp only [hx, not_true_eq_false, ite_true, ite_false, add_zero]
    rw [he]
    ring
  · simp only [hx, not_false_eq_true, ite_false, ite_true, mul_zero, zero_add]

/-- The positive statistic lower bound survives repeated-prime removal and
becomes the lower bound on the actual finite initial Fourier amplitude. -/
theorem regularInitialAmplitude_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (w : (Fin n → P) → ℂ)
    (hcut : ∀ x, w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (δ ε : ℝ)
    (hpositive : Real.sqrt X * (δ + ε) ≤
      ‖∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖)
    (herror : ‖∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖ ≤ Real.sqrt X * ε) :
    δ ≤ ‖regularInitialAmplitude P μ F ψ X N w‖ := by
  rw [initial_physical_fourier_decomposition P hP μ F ψ X H hX N w hcut hsupp] at hpositive
  have hn := (norm_add_le ((Real.sqrt X : ℂ) * regularInitialAmplitude P μ F ψ X N w)
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X)).trans
    (add_le_add le_rfl herror)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg X)] at hn
  have hs := Real.sqrt_pos.mpr hX
  nlinarith

/-- Normalized local energies suffice for the full repeated-prime removal.
This form also applies directly to the two cons/append half-list families. -/
theorem regularInitialAmplitude_lower_of_energy {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (hzero : ∀ i q, (∑ a, F i q a) = 0)
    (henergy : ∀ i q, (∑ a, ‖F i q a‖ ^ 2) ≤ q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ δ : ℝ) (hX : 0 < X) (hR : 0 < R) (N : ℕ)
    (w : (Fin n → P) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hcut : ∀ x, w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hsmall : ∀ p : P, H * R < (p : ℝ))
    (hlower : ∀ x, w x ≠ 0 → X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x, w x ≠ 0 → (∏ i, (x i : ℝ)) ≤ X * R)
    (hpositive : Real.sqrt X * (δ +
      ‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
      ‖∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖) :
    δ ≤ ‖regularInitialAmplitude P μ F ψ X N w‖ := by
  let E := Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x ∧ w x ≠ 0)
  have he := repeated_physical_prior_bound P hP μ C hμ hC hbound F hzero henergy
    ψ X H R Δ hX hR hsupp hsmall E
    (fun x hx => (Finset.mem_filter.mp hx).2.1)
    (fun x hx => hlower x (Finset.mem_filter.mp hx).2.2)
    (fun x hx => hupper x (Finset.mem_filter.mp hx).2.2) w (fun x _ => hw x)
  have hsum : (∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X) =
      ∑ x ∈ E, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X := by
    simp only [E, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hzero : w x = 0
    · simp only [hzero, ne_eq, not_true_eq_false, and_false, mul_zero, zero_mul, ite_self]
    · simp only [hzero, ne_eq, not_false_eq_true, and_true]
  apply regularInitialAmplitude_lower P hP μ F ψ X H hX N w hcut hsupp δ _ hpositive
  rw [hsum]
  exact he

/-- For the actual residue and phase tests, the repeated-prime error is
derived from their energies and the original marginal bounds. The only
statistic lower bound here is the one supplied by the endpoint construction. -/
theorem regularInitialAmplitude_lower_of_prime_tests {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (giant : Fin n → Bool) (favorable : P → Bool)
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ δ : ℝ) (hX : 0 < X) (hR : 0 < R) (N : ℕ)
    (w : (Fin n → P) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hcut : ∀ x, w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hsmall : ∀ p : P, H * R < (p : ℝ))
    (hlower : ∀ x, w x ≠ 0 → X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x, w x ≠ 0 → (∏ i, (x i : ℝ)) ≤ X * R)
    (hpositive : Real.sqrt X * (δ +
      ‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
      ‖∑ x : Fin n → P, (productPrior μ x : ℂ) * w x *
        physicalTupleSum P x (fun i q => primePhysicalTest (S q) (giant i) (favorable q)) ψ X‖) :
    δ ≤ ‖regularInitialAmplitude P μ
      (fun i q => primePhysicalTest (S q) (giant i) (favorable q)) ψ X N w‖ := by
  exact regularInitialAmplitude_lower_of_energy P hP μ C hμ hC hbound
    (fun i q => primePhysicalTest (S q) (giant i) (favorable q))
    (fun i q => primePhysicalTest_sum (S q) (giant i) (favorable q))
    (fun i q => primePhysicalTest_energy (S q) (giant i) (favorable q))
    ψ X H R Δ δ hX hR N w hw hcut hsupp hsmall hlower hupper hpositive

end Ostmann

end OAI
