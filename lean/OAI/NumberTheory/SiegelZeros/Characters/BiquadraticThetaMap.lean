import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Determinants.IntegralDeterminantTransport
import OAI.NumberTheory.SiegelZeros.Selection.JetRowAutCongr

namespace OAI

namespace SiegelZeros


open scoped NumberField

namespace WeightedTorusJets

theorem biquadratic_theta_map
    {K L : Type*} [CommRing K] [CommRing L]
    (e : K →+* L) (a b : K) (n : Fin 4 → ℕ) :
    e (∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i) =
      ∑ i : Fin 4, (n i : L) * ![1, e a, e b, e a * e b] i := by
  simp [Fin.sum_univ_succ]

theorem source_existing_jet_witness_transport
    {K L ι : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Fintype ι] [DecidableEq ι]
    (e : K ≃ₐ[ℚ] L) (σ τ : K ≃ₐ[ℚ] K)
    (a b : K) (A B : L) (hea : e a = A) (heb : e b = B)
    (n : ι → Fin 4 → ℕ) (θ : ι → K)
    (hθ : ∀ j, θ j = ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i)
    (α : ι → Fin 3 → ℕ) (Δ : K)
    (hΔ : Δ = Matrix.det (Matrix.of fun i j =>
      θ j ^ α i 0 * σ (θ j) ^ α i 1 * (σ * τ) (θ j) ^ α i 2))
    (hΔne : Δ ≠ 0) :
    let θL := fun j => ∑ i : Fin 4, (n j i : L) * ![1, A, B, A * B] i
    (∀ j, e (θ j) = θL j) ∧
      (∀ (β : Fin 3 → ℕ) j,
        e (θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2) =
          θL j ^ β 0 * (AlgEquiv.autCongr e σ) (θL j) ^ β 1 *
            (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (θL j) ^ β 2) ∧
      e Δ = Matrix.det (Matrix.of fun i j =>
        θL j ^ α i 0 * (AlgEquiv.autCongr e σ) (θL j) ^ α i 1 *
          (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (θL j) ^ α i 2) ∧
      e Δ ≠ 0 := by
  let θL := fun j => ∑ i : Fin 4, (n j i : L) * ![1, A, B, A * B] i
  have hθe (j : ι) : e (θ j) = θL j := by
    rw [hθ]
    calc
      e (∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i) =
          ∑ i : Fin 4, (n j i : L) * ![1, e a, e b, e a * e b] i :=
        biquadratic_theta_map e.toRingHom a b (n j)
      _ = θL j := by rw [hea, heb]
  have hrow (β : Fin 3 → ℕ) (j : ι) :
      e (θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2) =
        θL j ^ β 0 * (AlgEquiv.autCongr e σ) (θL j) ^ β 1 *
          (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (θL j) ^ β 2 := by
    rw [← hθe]
    exact source_jet_row_autCongr e σ τ (θ j) β
  refine ⟨hθe, hrow, ?_, (map_ne_zero e).mpr hΔne⟩
  rw [hΔ]
  change e.toRingHom (Matrix.det (Matrix.of _)) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hrow (α i) j

theorem source_existing_integral_jet_witness_transport
    {K L ι : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Fintype ι] [DecidableEq ι]
    (e : K ≃ₐ[ℚ] L) (σ τ : K ≃ₐ[ℚ] K)
    (a b : K) (A B : L) (hea : e a = A) (heb : e b = B)
    (n : ι → Fin 4 → ℕ) (θ : ι → K)
    (hθ : ∀ j, θ j = ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i)
    (α : ι → Fin 3 → ℕ) (Δ : 𝓞 K)
    (hΔ : (Δ : K) = Matrix.det (Matrix.of fun i j =>
      θ j ^ α i 0 * σ (θ j) ^ α i 1 * (σ * τ) (θ j) ^ α i 2))
    (hΔne : Δ ≠ 0) :
    let θL := fun j => ∑ i : Fin 4, (n j i : L) * ![1, A, B, A * B] i
    let ΔL := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv Δ
    (∀ j, e (θ j) = θL j) ∧
      (∀ (β : Fin 3 → ℕ) j,
        e (θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2) =
          θL j ^ β 0 * (AlgEquiv.autCongr e σ) (θL j) ^ β 1 *
            (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (θL j) ^ β 2) ∧
      (ΔL : L) = Matrix.det (Matrix.of fun i j =>
        θL j ^ α i 0 * (AlgEquiv.autCongr e σ) (θL j) ^ α i 1 *
          (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (θL j) ^ α i 2) ∧
      ΔL ≠ 0 ∧
      Algebra.norm ℚ (ΔL : L) = Algebra.norm ℚ (Δ : K) ∧
      Algebra.norm ℤ ΔL = Algebra.norm ℤ Δ ∧
      ∀ p r : ℕ,
        ((p : 𝓞 L) ^ r ∣ ΔL ↔ (p : 𝓞 K) ^ r ∣ Δ) ∧
        (ΔL ∈ (Ideal.span {(p : 𝓞 L)}) ^ r ↔
          Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ r) := by
  have hΔK : (Δ : K) ≠ 0 := by
    intro h
    apply hΔne
    apply Subtype.ext
    exact h
  obtain ⟨hθe, hrow, hdet, _⟩ := source_existing_jet_witness_transport
    e σ τ a b A B hea heb n θ hθ α (Δ : K) hΔ hΔK
  obtain ⟨hcoe, hne, hnormQ, hnormZ, hdiv⟩ := integral_determinant_transport e Δ
  exact ⟨hθe, hrow, hcoe.trans hdet, hne.mpr hΔne, hnormQ, hnormZ, hdiv⟩

end WeightedTorusJets


end SiegelZeros

end OAI
