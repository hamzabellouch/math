import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalPairBound
import OAI.NumberTheory.Ostmann.Arithmetic.RangedPairUniformDecay
import OAI.NumberTheory.Ostmann.Construction.HarmonicPriorAtomDecay
import OAI.NumberTheory.Ostmann.Construction.ConstituentGuardCost

namespace OAI

/-! # The original final pair decays from explicit prime and history bounds -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- The threshold is uniform over the growing constituent coordinate space.
The ranged-character error and the discarded prime guards are both derived
from the stated scalar size bounds. -/
theorem eventual_constituent_final_pair_decay
    (n : ℕ) (a₀ b₀ d₀ C S H z α₀ β γ c : ℝ)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hd₀ : 0 ≤ d₀) (hC : 0 ≤ C) (hS : 1 ≤ S)
    (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type u) [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (SurvivingConstituent role size n))
      (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let K := SurvivingConstituent role size n
    let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
    let W := primeWordEmbedding (scheduleConstituentWord role size n)
    let W' := primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
    let G := graphDifference (scheduledSurvivorGraph ρ pivot n)
      (transportGraph e (scheduledSurvivorGraph ρ pivot n))
    let Tpl := expandedRootTemplate role n W childBound pivotBound
    let Tpl' := expandedRootTemplate role n W' childBound pivotBound
    let D := expandedRootRanges role n W ranges
    let D' := expandedRootRanges role n W' ranges
    let U := expandedRootRanges role n W (totalAtomUnitRanges role)
    let U' := expandedRootRanges role n W' (totalAtomUnitRanges role)
    let Pr := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
    let Pr' := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
    let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀
    (a b : K) (_hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (_ht : NonzeroInternalFrequencies n t)
    (_ht' : NonzeroInternalFrequencies n t') (_hroot : frequencyRoot n t = frequencyRoot n t')
    (B : ℕ) (_hB : 1 ≤ B) (_hwords : (Tpl).WordsBounded B) (_hwords' : (Tpl').WordsBounded B)
    (_hD : (D).WordsBounded B) (_hD' : (D').WordsBounded B)
    (_hU : (U).WordsBounded B) (_hU' : (U').WordsBounded B) (_hreverse : G b a = 0)
    (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
    (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (_hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
    (A E : ℕ) (_hA : 0 < A)
    (_hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R)
    (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L)
    (Vfreq : ℕ) (_hBlinear : (B : ℝ) ≤ b₀ * (1 + M))
    (_hDcount : (((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)).count : ℝ) ≤ d₀ * (1 + M))
    (_hD'count : ((D').count : ℝ) ≤ d₀ * (1 + M))
    (_hVfreq : (Vfreq : ℝ) ≤ Real.exp (C * (1 + M)))
    (_hfv : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ Vfreq)
    (_hfv' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ Vfreq)
    (_hs₀ : SchwartzMap.seminorm ℝ 0 0 (FP).profile ≤ S)
    (_hs₁ : SchwartzMap.seminorm ℝ 0 1 (FP).profile ≤ S)
    (_hwidth : ∀ i, (FP).upper i - (FP).lower i ≤ Real.exp (C * (1 + M)))
    (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
    (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
    (_hshort : Real.exp (c * Real.exp (α₀ * L)) ≤ lower)
    (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
    (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
    (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α₀ * L)) ≤ (p : ℝ))
    (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
    (_hprimecount : (((Pr).count + (Pr').count : ℕ) : ℝ) ≤ a₀ * (1 + M))
    (_hcheckcount : ((constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      a₀ * (1 + M) ^ 2)
    (center : ∀ p : ℕ, ZMod p),
    ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
      Real.exp (-(c / 32) * Real.exp (α₀ * L)) := by
  let K₀ := 2 * (2 ^ n : ℕ) * S + a₀ * (b₀ ^ (n + 1) + 1)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  filter_upwards [eventual_ranged_pair_decay_from_data_uniform n b₀ d₀ C S H z α₀ β γ c
      hb₀ hd₀ hC hS hH hz hα₀ hαβ hγβ hc,
    eventual_primeSubsetPrior_atom_decay H z α₀ c hH hz hα₀ hc,
    eventual_prime_prior_guard_decay H z α₀ (c / 2) hH hz hα₀ (by positivity),
    eventual_prime_support_decay K₀ z α₀ (c / 4) (n + 2) hK₀ hz hα₀ (by positivity)]
    with L hranged hatoms hguards hsupport
  intro I _ role size χ κ pivot hκ e hχ childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    K ρ W W' G Tpl Tpl' D D' U U' Pr Pr' FP
    a b hab t t' ht ht' hroot B hB hwords hwords' hD hD' hU hU' hreverse
    P hP hprime Q hQP hQmass hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh
    lower hlower hlowerQ Bq hBq V R hV hR hlowerP hupperP hfreq hfreq'
    M hm hmL Vfreq hBlinear hDcount hD'count hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv
    hshort hlong hBqscale hmin hratio hprimecount hcheckcount center
  let atom := Real.exp (-(c / 2) * Real.exp (α₀ * L))
  let δ := Real.exp (-(c / 4) * Real.exp (α₀ * L))
  let loss := ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
      (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
      ((((Pr).count + (Pr').count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length)
  have hcost : loss ≤ Real.exp (K₀ * (1 + M) ^ (n + 2)) := by
    simpa only [loss, K₀, Nat.cast_pow] using
      constituent_guard_cost_le_exp n ((Pr).count + (Pr').count)
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length B
        (SchwartzMap.seminorm ℝ 0 0 (FP).profile) S a₀ b₀ M
        (apply_nonneg _ _) hs₀ ha₀ hm hprimecount hcheckcount hBlinear
  have hmax (i : K) (p : P) : primeSubsetPrior P (Q i) p ≤ atom :=
    hatoms M P (Q i) hm hmL (hQinv i) (fun q hq => hmin q (hQP i hq)) p
  have hnum := hranged (ExpandedScheduledVariable (Option K) n) Tpl Tpl'
    ((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) D'
    t t' ht ht' B Vfreq A E FP FP (Q b) (Q a) lower Bq M
    hm hmL hBlinear hDcount hD'count hVfreq hfv hfv'
    hs₀ hs₁ hs₀ hs₁ hwidth hwidth hE (hQinv b) (hQinv a) hshort hlong hBqscale
  have hold := constituent_final_pair_bound role size n χ κ pivot hκ e hχ childBound pivotBound
    ranges ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht' hroot B hB hwords hwords'
    hD hD' hU hU' hreverse P hP hprime Q hQP hQmass hnonprincipal A E hA hMA
    hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq atom V R (Real.exp_nonneg _)
    hV hR hmax hlowerP hupperP hfreq hfreq' δ (Real.exp_nonneg _) hnum center
  have hguard : atom + Real.log R / V * atom ≤ δ := by
    have hh := hguards M atom (Real.log R / V) hm hmL (Real.exp_nonneg _) le_rfl hratio
    convert hh using 1
    dsimp [δ]
    congr 2
    ring
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have hδ : δ ≤ Real.exp (-(c / 4 / 4) * Real.exp (α₀ * L)) := by
    dsimp [δ]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_pos (α₀ * L)]
  have hsum : δ + loss * (atom + Real.log R / V * atom) ≤ δ + loss * δ := by
    linarith only [mul_le_mul_of_nonneg_left hguard hloss]
  have hh := hsupport M δ loss δ _ hm hmL hloss hcost le_rfl hδ (hold.trans hsum)
  convert hh using 1
  congr 1
  ring

end Ostmann

end OAI
