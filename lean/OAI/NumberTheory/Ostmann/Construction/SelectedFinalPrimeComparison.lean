import OAI.NumberTheory.Ostmann.Construction.SelectedFinalPairDecay
import OAI.NumberTheory.Ostmann.Construction.SelectedFinalEnergyComparison

namespace OAI

/-! # The original final comparison from explicit prime-range data -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- The final second-moment estimate has no assumed energy or pair bound.
The two thresholds are uniform over the growing word and constituent lists. -/
theorem selected_final_comparison_from_prime_data {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (C₀ K ε : ℝ) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ (size : I → ℕ) (Smax : ℕ) (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hM₀ : M₀ ≤ M) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (pivot : ℕ → (Σ i, Fin (size i)))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Aw)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (_hbulk : ∀ i, ρ (bulk i) = .word)
      (anchor : Fin (n + 1) → (Σ a, Fin (size a)))
      (_ha : ∀ j, ρ (anchor j) = .anchor j) (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
      (A E Bq : ℕ) (_hA : 0 < A) (lower V R : ℝ)
      (_hlower : 0 < lower) (_hV : 0 < V) (_hR : 3 ≤ R)
      (_hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
      (_hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
      (_hword : ∀ i p, p ∈ Q (bulk i) → 2 * A ≤ p ∧ p ≤ E)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * M))
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
      (_hlarge : ∀ p ∈ P, cutoff (n + 1) < p)
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (Δ : ℝ) (_hcutoff₀ : (cutoff 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt M))
      (_hlo₀ : Real.exp (Δ - C₀) ≤ lo)
      (h J : ℕ)
      (_hmod : ∀ t : FrequencyTree ((transferFrequencyRange (cutoff (n + 1))).erase 0) (n + 1),
        historyFrequencyModulus ((transferFrequencyRange (cutoff (n + 1))).erase 0) (n + 1) (n + 1) t ≤ 2 ^ h)
      (_hcellrange : ∀ p ∈ Q i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ : ℝ) (_ha₀ : 0 < a) (_hL : 1 ≤ L)
      (_hcellmass : a ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (center : ∀ p : ℕ, ZMod p),
    ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hprime Q
        childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        (scheduledFrequencyHistory cutoff (n + 1)) center‖ ^ 2 ≤
      ((transferFrequencyRange (cutoff (n + 1))).card : ℝ) *
        (Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ (n + 1) : ℕ) * L + ε * M) /
          (Fintype.card (FinalParityReassignments n m) : ℝ) +
        (Fintype.card (ScheduledFrequencyIndex cutoff (n + 1)) : ℝ) ^ 2 *
          Real.exp (-(c / 32) * Real.exp (α * L))) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventual_selected_final_energy_comparison n ψ C₀ K C ε hC hε hψ)
  refine ⟨M₀, ?_⟩
  filter_upwards [eventual_selected_final_pair_decay role n Aw Kr s C S H z α β γ c
    hs hC hS hH hz hα hαβ hγβ hc] with L hdec
  intro size Smax hSmax hsize M hMlarge hm hmL hSm χ κ hκ pivot childBound pivotBound ranges
    hrange hcount X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk anchor ha hp P hP hprime
    Q hQP hQmass A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio
    hlarge i hiword Δ hcutoff₀ hlo₀ h J hmod hcellrange a C₁ ha₀ hL hcellmass hJ center
  have hfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)) := by
    apply hVfreq.trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpairs := hdec size Smax hSmax hsize M hm hmL hSm χ κ hκ pivot childBound pivotBound
    ranges hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu m bulk hbulk anchor ha hp P hP hprime
    Q hQP hQmass A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP
    cutoff hcutoff hfreq hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio
  exact hM₀ M hMlarge role size χ κ hκ pivot childBound pivotBound ranges i hiword hu m bulk hbulk
    cutoff hcutoff Δ X lo hi hVfreq hcutoff₀ P (fun p hp => ⟨hprime p hp, hlarge p hp⟩) Q
    hX hXlo hlo₀ hQP (fun i => ne_of_gt (hQmass i)) h J hmod hcellrange a C₁ L ha₀ hL
    hcellmass hJ center _ (Real.exp_nonneg _)
    (fun e f hef d d' hd => hpairs e f hef d d' hd hlarge center)

end Ostmann

end OAI
