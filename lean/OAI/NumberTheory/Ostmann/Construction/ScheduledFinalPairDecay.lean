import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalPairDecay
import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalCostData
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPrimeRanges
import OAI.NumberTheory.Ostmann.Construction.FinalPairPeriodScale
import OAI.NumberTheory.Ostmann.Construction.ConstituentPrimeFrequencySupport
import OAI.NumberTheory.Ostmann.Construction.ScheduledRootIndex

namespace OAI

/-! # Final parity pairs: cancellation for the actual scheduled constituents -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- All distinct final parity arrangements satisfy the original-prior pair estimate.
The one-sided character, word sizes, range counts and common modulus are derived
from the actual schedule; only the explicit physical prime and frequency ranges remain. -/
theorem eventual_scheduled_final_pair_decay {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (size : I → ℕ) (Smax : ℕ) (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (pivot : ℕ → (Σ i, Fin (size i)))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Aw)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (word : Fin m ≃ {i : Σ a, Fin (size a) // ρ i = .word})
      (anchor : Fin (n + 1) → (Σ a, Fin (size a)))
      (_ha : ∀ j, ρ (anchor j) = .anchor j) (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
      (A E Bq : ℕ) (_hA : 0 < A) (lower V R : ℝ)
      (_hlower : 0 < lower) (_hV : 0 < V) (_hR : 3 ≤ R)
      (_hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
      (_hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
      (_hword : ∀ i, ρ i = .word → ∀ p ∈ Q i, 2 * A ≤ p ∧ p ≤ E)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshort : Real.exp (c * Real.exp (α * L)) ≤ lower)
      (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
      (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (e f : FinalParityReassignments n m) (_hef : e ≠ f)
      (d d' : ScheduledFrequencyIndex cutoff (n + 1))
      (_hroot : scheduledRootIndex cutoff (n + 1) d = scheduledRootIndex cutoff (n + 1) d')
      (_hlarge : ∀ p ∈ P, cutoff (n + 1) < p)
      (center : ∀ p : ℕ, ZMod p),
    ‖∑ q : SurvivingConstituent role size (n + 1) → P,
      ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center (scheduledFrequencyHistory cutoff (n + 1) d) q *
      conj (constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center (scheduledFrequencyHistory cutoff (n + 1) d')
          (fun i => q (scheduledFinalRelativePerm ρ n m word e f i))))‖ ≤
        Real.exp (-(c / 32) * Real.exp (α * L)) := by
  let a₀ := constituentFinalCountRate (Fintype.card I) (n + 1) s
  let b₀ := (((2 * 3 ^ (n + 1) * Fintype.card I + Aw : ℕ) : ℝ) * s + 4)
  let d₀ : ℝ := (Kr * (2 ^ (n + 1 + 1) - 1) + 1 : ℕ)
  have ha₀ : 0 ≤ a₀ := constituentFinalCountRate_nonneg _ _ _ hs
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hd₀ : 0 ≤ d₀ := by dsimp [d₀]; positivity
  filter_upwards [eventual_constituent_final_pair_decay (n + 1) a₀ b₀ d₀ C S H z α β γ c
      ha₀ hb₀ hd₀ hC hS hH hz hα hαβ hγβ hc,
    eventual_final_pair_period_scale (n + 1) b₀ C z β hb₀ hC hz (hα.trans hαβ)]
    with L hdec hperiod
  intro size Smax hSmax hsize M hm hmL hSm χ κ hκ pivot childBound pivotBound ranges hrange
    hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ FP m word anchor ha hp P hP hprime Q hQP hQmass
    A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP cutoff hcutoff hVfreq
    hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio e f hef d d' hroot hlarge center
  let Vfreq := cutoff (n + 1)
  let t := scheduledFrequencyHistory cutoff (n + 1) d
  let t' := scheduledFrequencyHistory cutoff (n + 1) d'
  have hfv := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d
  have hfv' := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d'
  have hroot' := (scheduledRootIndex_eq_iff cutoff (n + 1) d d').mp hroot
  by_cases htzero : ∀ q : SurvivingConstituent role size (n + 1) → P,
      constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q = 0
  · dsimp only [t] at htzero
    simp only [htzero, zero_mul, mul_zero, Finset.sum_const_zero, norm_zero]
    exact Real.exp_nonneg _
  by_cases htzero' : ∀ q : SurvivingConstituent role size (n + 1) → P,
      constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' q = 0
  · dsimp only [t'] at htzero'
    simp only [htzero', map_zero, mul_zero, Finset.sum_const_zero, norm_zero]
    exact Real.exp_nonneg _
  push Not at htzero htzero'
  obtain ⟨q, hq⟩ := htzero
  obtain ⟨q', hq'⟩ := htzero'
  obtain ⟨ht, hn⟩ := constituentPrimeTerm_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo center t q hq
  obtain ⟨ht', hn'⟩ := constituentPrimeTerm_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo center t' q' hq'
  obtain ⟨hsmall, hfreq⟩ := finite_frequency_range_data P hP R Vfreq hlarge hupperP
    (n + 1) t hn hfv
  obtain ⟨hsmall', hfreq'⟩ := finite_frequency_range_data P hP R Vfreq hlarge hupperP
    (n + 1) t' hn' hfv'
  let perm := scheduledFinalRelativePerm ρ n m word e f
  let W := primeWordEmbedding (scheduleConstituentWord role size (n + 1))
  let W' := primeWordEmbedding (fun v => List.map perm (scheduleConstituentWord role size (n + 1) v))
  let B := 2 * 3 ^ (n + 1) * Fintype.card I * Smax + Aw * Smax + 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBlinear : (B : ℝ) ≤ b₀ * (1 + M) :=
    constituent_word_budget_linear (n + 1) Aw Smax s M hSm hm
  obtain ⟨hw, hw', hD, hD', hU, hU'⟩ :=
    constituent_final_word_bounds role size (n + 1) perm childBound pivotBound ranges
      Smax Aw hSmax hsize hrange
  have hcounts := constituent_final_linear_counts role size (n + 1) perm Smax s M
    hSmax hsize hs hm hSm
  have hranges := expandedRootRanges_pair_linear_count role (n + 1) Kr W W' ranges hcount
    (originalProductRange ([] : List (Option (SurvivingConstituent role size (n + 1)))) (n + 1) 1 0) M hm
  obtain ⟨a, b, hab, haQ, hbQ, hnonprincipal, hreverse⟩ :=
    scheduled_final_relative_prime_ranges ρ pivot n m word anchor ha hp Q χ lower Bq A E
      hsquare hanchor hword e f hef
  have hχ : ∀ i, χ (copyScheduleOrigin (n + 1) (perm i).val) =
      χ (copyScheduleOrigin (n + 1) i.val) := by
    intro i
    rw [scheduledFinalRelativePerm_origin]
  have hMA := hperiod M B Vfreq A t t' hm hmL hBlinear hVfreq hfv hfv' hlong
  exact hdec I role size χ κ pivot hκ perm hχ childBound pivotBound ranges ψ hreal X lo hi
    hlo hhi hu a b hab t t' ht ht' hroot' B hB hw hw' hD hD' hU hU' hreverse
    P hP hprime (fun i => Q (copyScheduleOrigin (n + 1) i.val))
    (fun i => hQP _) (fun i => hQmass _) hnonprincipal A E hA hMA hsmall hsmall'
    (fun p hp => (hbQ p hp).1) (fun p hp => (hbQ p hp).2) lower hlower
    (fun q hq => (haQ q hq).1) Bq (fun q => (haQ q.val q.property).2)
    V R hV hR hlowerP hupperP hfreq hfreq' M hm hmL Vfreq hBlinear
    hranges.1 hranges.2 hVfreq hfv hfv' hs₀ hs₁ hwidth hE (fun i => hQinv _)
    hshort hlong hBqscale hmin hratio hcounts.1 hcounts.2 center

end Ostmann

end OAI
