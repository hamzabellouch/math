import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallKernelFamily

namespace OAI

/-! # The fixed subfamily in which all small-kernel witnesses fail -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def fixedPrimeDivisorTerm (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex) (V U : Finset ℕ) (s : ℕ) : ℂ :=
  primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue i.1) V)
    (fun _ => (i.2.1 : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) i.2.2.2)
    Φ (quadraticGridScale (Real.exp (-200 * T)) i.2.2.2) V.toList.prod U s

noncomputable def offWitnessParameters (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (S : Finset ℕ) : Finset QuadraticFamilyIndex := by
  classical
  exact (smallKernelParameters T Q.toList.prod).filter (fun i =>
    ∀ s ∈ S, ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
      ‖fixedPrimeDivisorTerm T Q hQ D Φ i V U s‖ ≤
        Real.exp (-9 * Q.card / 10) * (Real.sqrt 2) ^ U.card)

theorem fixedQuadraticCoefficient_principal (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex) (s : ℕ) (hi : i.2.2.1 = 1) :
    fixedQuadraticCoefficient T Q hQ D Φ i s =
      divisorWeightedCoefficient Q (quadraticDivisorSymbol i.1)
        (fun V s => ∑ U ∈ Q.powerset,
          quadraticSymbolCoefficient i.1 U * fixedPrimeDivisorTerm T Q hQ D Φ i V U s) s := by
  simp only [fixedQuadraticCoefficient, arithmeticQuadraticCoefficient, hi,
    fullQuadraticCoefficient_one, fixedPrimeDivisorTerm]

theorem eventual_full_off_witness_norm (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (c ξ : Finset ℕ → ℂ) (G : Finset ℕ → Finset ℕ → ℕ → ℂ),
      (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) →
      (∀ s ∈ S, ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
        ‖G V U s‖ ≤ Real.exp (-9 * Q.card / 10) * (Real.sqrt 2) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖divisorWeightedCoefficient Q ξ (fun V s => ∑ U ∈ Q.powerset, c U * G V U s) s‖ ^ 2) ≤
        Real.exp ((-799 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_off_witness_norm_card C₀ ε hC₀ hε] with T hn
  intro Q M S u hK hlarge hM hS hu huU c ξ G hc hξ hG
  refine (divisorWeightedCoefficient_energy_exp_le Q ξ _ S _
    (Real.exp ((-4 / 5 + ε) * Q.card)) hlarge (fun _ _ => by positivity)
    (Real.exp_nonneg _) hξ ?_).trans_eq ?_
  · intro V hV
    exact hn Q M S u hK hM hS hu huU c (G V) hc
      (fun s hs U hU => hG s hs V hV U hU)
  · rw [← Real.exp_add]
    congr 1
    ring

theorem eventual_off_witness_family_norm (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex),
      i ∈ offWitnessParameters T Q hQ D Φ S →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤
        Real.exp ((-799 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_full_off_witness_norm C₀ ε hC₀ hε] with T hn
  intro Q hQ M S u hK hlarge hM hS hu huU D Φ i hi
  have hi' := Finset.mem_filter.mp hi
  have hiP := (Finset.mem_filter.mp hi'.1).2.1
  simp_rw [fixedQuadraticCoefficient_principal T Q hQ D Φ i _ hiP]
  exact hn Q M S u hK hlarge hM hS hu huU (quadraticSymbolCoefficient i.1)
    (quadraticDivisorSymbol i.1) (fixedPrimeDivisorTerm T Q hQ D Φ i)
    (fun U _ => quadraticSymbolCoefficient_norm_le _ U)
    (fun V _ => quadraticDivisorSymbol_norm_le _ V) hi'.2

end Ostmann

end OAI
