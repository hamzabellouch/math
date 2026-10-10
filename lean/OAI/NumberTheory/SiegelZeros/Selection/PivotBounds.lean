import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.CharacterGlobalGreedyDeterminantMasterBounds

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_pivot_bounds :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      ∀ H : ℕ, 0 < H → ∃ N₀ : ℕ,
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
          characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
            (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
              sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ) →
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N : ℕ, H ≤ N → N₀ ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                let P := (greedyPivots B (R ∘ e) s.card).image e
                P.card = N ^ 4 ∧
                  c₁ * (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ≤
                    (∑ α ∈ P, (α 0 : ℝ)) ∧
                  (∑ α ∈ P, ((α 1 : ℝ) + α 2)) ≤
                    C₁ * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
                  (∑ α ∈ P, ((α 1 : ℝ) + α 2)) / (∑ α ∈ P, (α 0 : ℝ)) ≤
                    (C₁ / c₁) / (H : ℝ) := by
  classical
  obtain ⟨_, _, _, _, hmaster⟩ := source_character_global_greedy_determinant_master_bounds
  refine ⟨1 / (4 * 97 ^ 2), 192, by norm_num, by norm_num, ?_⟩
  intro H hH
  refine ⟨18818, ?_⟩
  intro q _ χ hreal hprim hne hfield
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    hmaster q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N hHN hN n
  dsimp only
  intro e he
  obtain ⟨g, α, _, _, hrange, _, _, _, Δ, _, _, _, _, _, _, hweights⟩ :=
    hsource N H hH hHN n e he
  obtain ⟨hlower, hupper, _, _⟩ := hweights hN
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (hH.trans_le hHN)
  refine ⟨?_, ?_, hupper, ?_⟩
  · simpa only [hrange, Set.ncard_coe_finset, Nat.card_fin] using
      Set.ncard_range_of_injective α.injective
  · convert hlower using 1 ; ring
  · convert pivot_ratio_bound (M := (N : ℝ) ^ 4) (H := (H : ℝ))
      (t := (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ))
      (by positivity) hHpos (by positivity)
      (by convert hlower using 1 ; simp only [mul_assoc, pivot_primary_scale hHpos])
      (by convert hupper using 1 ; ring) using 1 ; norm_num

end WeightedTorusJets

end

end SiegelZeros

end OAI
