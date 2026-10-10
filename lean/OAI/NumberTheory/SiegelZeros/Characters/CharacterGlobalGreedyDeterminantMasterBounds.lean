import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.CharacterGlobalGreedyDeterminantFullLocalBounds
import OAI.NumberTheory.SiegelZeros.Determinants.NormalizedMasterBound
import OAI.NumberTheory.SiegelZeros.Selection.GlobalRectanglePivotBounds
import OAI.NumberTheory.SiegelZeros.Structure.InvariantJetLinearMap

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_master_bounds :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧ ∃ CH : ℕ → ℝ,
    ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)),
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
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    (∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ) ∧
                    (∀ β : ℝ, 0 < β → β < 1 →
                      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                    ∀ U : ℝ, 0 ≤ U →
                      (∑ i, (α i 0 : ℝ)) *
                          (Real.log U - C * Real.log q -
                            C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH H) -
                        C * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ) ∧
                    (18818 ≤ N →
                      let P := (greedyPivots B (R ∘ e) s.card).image e
                      let S₁ := ∑ a ∈ P, (a 0 : ℝ)
                      let S₂ := ∑ a ∈ P, ((a 1 : ℝ) + a 2)
                      let M := (N : ℝ) ^ 4
                      let U := (N : ℝ) ^ (4 / 3 : ℝ)
                      M * (H : ℝ) ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁ ∧
                      S₂ ≤ 192 * M * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U ∧
                      0 < S₁ ∧
                      ∀ β : ℝ, 0 < β → β < 1 →
                        DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                        1 ≤ 3 / 4 * (1 + S₂ / S₁) +
                          (C + 1 / 2 * (1 + S₂ / S₁)) * (Real.log q / Real.log U) +
                          C * ((1 - β) * Real.log q) * (Real.log U / Real.log q) +
                          (CH H + (1 + S₂ / S₁) * Real.log 8) / Real.log U +
                          (C * M * U + 1 / 2 * M * Real.log M) / (S₁ * Real.log U)) := by
  classical
  obtain ⟨C, hC, hC4, CH, hlocal⟩ :=
    source_character_global_greedy_determinant_full_local_bounds
  refine ⟨C, hC, hC4, CH, ?_⟩
  intro q _ χ hreal hprim hne hfield
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    hlocal q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
      harch, hdiv, hraw, hfinite⟩ := hsource N H hH hHN n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
    harch, hdiv, hraw, hfinite, ?_⟩
  intro hN
  let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let R := fun a : Fin 3 → ℕ => fun j =>
    θ j ^ a 0 * σ (θ j) ^ a 1 * (σ * τ) (θ j) ^ a 2
  let P := (greedyPivots B (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e
  let U := (N : ℝ) ^ (4 / 3 : ℝ)
  have hninj : Function.Injective (fun j i => (n j i : ℕ)) := by
    intro j k h
    apply n.injective
    funext i
    exact Fin.ext (congrFun h i)
  have hspan := actual_biquadratic_rectangle_span a' b' v hv σ τ
    hσa hσb hτa hτb H N hH hHN (fun j i => (n j i : ℕ)) hninj
    (fun j i => (n j i).isLt)
  have hpivots := global_source_rectangle_pivot_bounds H N hH hHN hN R e he α hrange hspan
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hH.trans_le hHN
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hS₁ : 0 < ∑ a ∈ P, (a 0 : ℝ) := lt_of_lt_of_le (by positivity) hpivots.1
  refine ⟨hpivots.1, hpivots.2, hS₁, ?_⟩
  intro β hβ0 hβ1 hzero
  have hUone : 1 < U := by
    exact Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α P hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α P hrange (fun a => ((a 1 : ℝ) + a 2))
  have hlower := hfinite β hβ0 hβ1 hzero U (le_of_lt (zero_lt_one.trans hUone))
  rw [hS₁eq, hS₂eq] at harch
  rw [hS₁eq] at hlower
  have hlogN : Real.log (N : ℝ) = 3 / 4 * Real.log U := by
    dsimp only [U]
    rw [Real.log_rpow hNpos]
    ring
  have hq : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q from lt_of_lt_of_le (by decide) (three_le_level_of_nonprincipal χ hne))
  exact FinalComparison.normalized_master_bound hS₁ (Real.log_pos hUone)
    (Real.log_pos hq) hlogN harch hlower

end WeightedTorusJets


end SiegelZeros

end OAI
