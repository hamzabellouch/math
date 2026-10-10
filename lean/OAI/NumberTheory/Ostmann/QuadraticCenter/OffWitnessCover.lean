import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessGridGap

namespace OAI

/-! # Actual failure of every small witness enters the fixed off-witness family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_off_witness_family_covers (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) (θ R : ℝ) (S : Finset ℕ),
      1 ≤ Q.card → (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      (∀ s ∈ S, 1 ≤ s ∧ (s : ℝ) ≤ Real.exp (14 * T)) →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R →
      (∀ s ∈ S, ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
        ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod U s‖ ≤
            Real.exp (-(Q.card : ℝ)) * (Real.sqrt 2) ^ U.card) →
      ∃ i ∈ offWitnessParameters T Q hQ D Φ S, ∀ s ∈ S,
        ‖arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ s -
          fixedQuadraticCoefficient T Q hQ D Φ i s‖ ≤ Real.exp (-127 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_grid H Φ hH hΦ,
    eventually_ge_atTop (1 : ℝ)] with T hg hT
  intro Q hQ D M h₀ θ R S hK hcard hlarge hL hM hh₀ hS hθ0 hθ1 hR hRU hmargin hfail
  obtain ⟨j, hj, _, _, _, _, hjδ, he⟩ := hg θ R hθ0 hθ1 hR hRU
  let r := M % (4 * Q.toList.prod)
  let i : QuadraticFamilyIndex := (r, h₀, 1, j)
  have hLpos : 0 < Q.toList.prod := prime_list_prod_pos _ (primeSet_list_prime Q hQ)
  have hr : r < 4 * Q.toList.prod := Nat.mod_lt _ (Nat.mul_pos (by decide) hLpos)
  have hP : (1 : ℝ) ≤ Real.exp (7 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have hP' : ((1 : ℕ) : ℝ) ≤ Real.exp (7 * T) := by simpa only [Nat.cast_one] using hP
  have hPf : (1 : ℕ) ≤ ⌊Real.exp (7 * T)⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hP'
  have hi : i ∈ quadraticFamilyParameters T Q.toList.prod := by
    apply (mem_quadraticFamilyParameters T Q.toList.prod i).mpr
    exact ⟨hr, hh₀, ⟨le_rfl, hPf⟩, hj⟩
  have hiSmall : i ∈ smallKernelParameters T Q.toList.prod := by
    apply Finset.mem_filter.mpr
    refine ⟨hi, rfl, ?_⟩
    have hh := (le_abs_self (R - quadraticGridScale (Real.exp (-200 * T)) j)).trans hjδ
    change (Q.toList.prod : ℝ) ^ 6 ≤ quadraticGridScale (Real.exp (-200 * T)) j
    linarith
  have he' (s : ℕ) (hs : s ∈ S) := he Q hQ D M h₀ 1 s hcard hlarge hL (by decide) hP'
    (hS s hs).1 (hS s hs).2
  refine ⟨i, Finset.mem_filter.mpr ⟨hiSmall, ?_⟩, ?_⟩
  · intro s hs V hV U hU
    have hclose := (he' s hs).2 V hV U hU
    simp only [primeDivisorMultiples, one_pow, mul_one, Nat.cast_one, inv_one, one_mul] at hclose
    have hgrid := small_witness_failure_survives_grid T Q.card U.card _ _ hT hK hcard
      (hfail s hs V hV U hU) hclose
    change ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue r) V)
      (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
      Φ (quadraticGridScale (Real.exp (-200 * T)) j) V.toList.prod U s‖ ≤ _
    have ha := quadraticInverseResidue_mod_multiple Q.toList.prod M U
      (primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU))
    rw [← primeDivisorPositive_congr_point Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
      (divisorQuadraticScalar (quadraticInverseResidue r) V) _ Φ _ V.toList.prod U s
      (divisorQuadraticScalar_congr_point (quadraticInverseResidue M) (quadraticInverseResidue r) V U ha)]
    exact hgrid
  · intro s hs
    change ‖arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ s -
      arithmeticQuadraticCoefficient Q hQ D Φ (quadraticGridScale (Real.exp (-200 * T)) j)
        1 r h₀ (quadraticGridPhase (Real.exp (-200 * T)) j) s‖ ≤ _
    rw [← arithmeticQuadraticCoefficient_mod Q hQ D Φ _ 1 M h₀ _ s hM]
    exact (he' s hs).1

end Ostmann

end OAI
