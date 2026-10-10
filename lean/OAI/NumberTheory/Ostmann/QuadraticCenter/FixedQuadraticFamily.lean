import OAI.NumberTheory.Ostmann.QuadraticCenter.FullCoefficientGrid

namespace OAI

/-! # A fixed finite family containing all discretized arithmetic arrays -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

abbrev QuadraticFamilyIndex := ℕ × (ℕ × (ℕ × (ℕ × ℕ)))

noncomputable def quadraticFamilyParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (Finset.range (4 * L)).product ((Finset.range L).product
    ((Finset.Icc 1 ⌊Real.exp (7 * T)⌋₊).product
      (quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)))))

noncomputable def fixedQuadraticCoefficient (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex) (s : ℕ) : ℂ :=
  arithmeticQuadraticCoefficient Q hQ D Φ
    (quadraticGridScale (Real.exp (-200 * T)) i.2.2.2) i.2.2.1 i.1 i.2.1
    (quadraticGridPhase (Real.exp (-200 * T)) i.2.2.2) s

theorem mem_quadraticFamilyParameters (T : ℝ) (L : ℕ) (i : QuadraticFamilyIndex) :
    i ∈ quadraticFamilyParameters T L ↔
      i.1 < 4 * L ∧ i.2.1 < L ∧
      (1 ≤ i.2.2.1 ∧ i.2.2.1 ≤ ⌊Real.exp (7 * T)⌋₊) ∧
      i.2.2.2 ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)) := by
  simp only [quadraticFamilyParameters, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_range, Finset.mem_Icc]

theorem quadraticFamilyParameters_card (T : ℝ) (L : ℕ) :
    (quadraticFamilyParameters T L).card =
      (4 * L) * (L * (⌊Real.exp (7 * T)⌋₊ *
        (quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T))).card)) := by
  simp only [quadraticFamilyParameters, Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    Nat.card_Icc, Nat.add_sub_cancel]

theorem eventual_quadraticFamilyParameters_card :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ, (L : ℝ) ≤ Real.exp (T / 25) →
      ((quadraticFamilyParameters T L).card : ℝ) ≤ Real.exp (425 * T) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT
  have hg := quadraticParameterGrid_exponential_card T (by linarith)
  intro L hL
  have hfour : (4 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  rw [quadraticFamilyParameters_card]
  push_cast
  calc
    _ ≤ (Real.exp T * Real.exp (T / 25)) * (Real.exp (T / 25) *
        (Real.exp (7 * T) * Real.exp (416 * T))) := by
      gcongr
      · exact Nat.floor_le (Real.exp_nonneg _)
    _ = Real.exp (T + T / 25 + T / 25 + 7 * T + 416 * T) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The index family is fixed before M and its translating residue are chosen.
The grid index works simultaneously for every kernel s in the full support. -/
theorem eventual_fixed_quadratic_family_covers (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ P : ℕ) (θ R : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      0 < P → (P : ℝ) ≤ Real.exp (7 * T) →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ i ∈ quadraticFamilyParameters T Q.toList.prod,
        i.2.2.1 = P ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) i.2.2.2| ≤ Real.exp (-200 * T) ∧
        ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
          ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s -
            fixedQuadraticCoefficient T Q hQ D Φ i s‖ ≤ Real.exp (-127 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_grid H Φ hH hΦ] with T hg
  intro Q hQ D M h₀ P θ R hcard hlarge hL hM hh₀ hP hPU hθ0 hθ1 hR hRU
  obtain ⟨j, hj, _, _, _, _, hjδ, he⟩ := hg θ R hθ0 hθ1 hR hRU
  let r := M % (4 * Q.toList.prod)
  let i : QuadraticFamilyIndex := (r, h₀, P, j)
  refine ⟨i, ?_, rfl, hjδ, ?_⟩
  · have hLpos : 0 < Q.toList.prod := prime_list_prod_pos _ (primeSet_list_prime Q hQ)
    have hr : r < 4 * Q.toList.prod := Nat.mod_lt _ (Nat.mul_pos (by decide) hLpos)
    have hpU : P ≤ ⌊Real.exp (7 * T)⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hPU
    simpa only [i, quadraticFamilyParameters, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] using And.intro hr (And.intro hh₀ (And.intro (And.intro (show 1 ≤ P from hP) hpU) hj))
  · intro s hs hsU
    change ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s -
      arithmeticQuadraticCoefficient Q hQ D Φ
        (quadraticGridScale (Real.exp (-200 * T)) j) P r h₀
        (quadraticGridPhase (Real.exp (-200 * T)) j) s‖ ≤ _
    rw [← arithmeticQuadraticCoefficient_mod Q hQ D Φ _ P M h₀ _ s hM]
    exact (he Q hQ D M h₀ P s hcard hlarge hL hP hPU hs hsU).1

end Ostmann

end OAI
