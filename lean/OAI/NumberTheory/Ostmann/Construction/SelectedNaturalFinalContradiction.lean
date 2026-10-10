import OAI.NumberTheory.Ostmann.Construction.SelectedFinalPairDecay
import OAI.NumberTheory.Ostmann.Construction.SelectedFinalNaturalEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalContradiction

namespace OAI

/-! # The original final comparison from explicit prime-range data -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- The final second-moment estimate has no assumed energy or pair bound.
The two thresholds are uniform over the growing word and constituent lists. -/
theorem selected_natural_final_contradiction {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (B₁ Cfinal : ℝ) (hB₁ : 0 ≤ B₁)
    (hentropy : Cfinal + (d + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ (size : I → ℕ) (Smax : ℕ) (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hM₀ : M₀ ≤ M) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M)),
    let cutoff := naturalTransferCutoff (d * M) M
    ∀       (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
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
      (_hlo₀ : Real.exp (d * M - C₀) ≤ lo)
      (h J : ℕ)
      (_hmod : cutoff (n + 1) ^ ((2 ^ (n + 2) - 1) * (n + 3)) ≤ 2 ^ h)
      (_hcellrange : ∀ p ∈ Q i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ : ℝ) (_ha₀ : 0 < a) (_hL : 1 ≤ L)
      (_hcellmass : a ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (center : ∀ p : ℕ, ZMod p),
    ∀ (_hMm : M = (m : ℝ)) (_hLm : L ≤ (m : ℝ)) (_hC₁ : 0 ≤ C₁)
    (_hcost : C₁ + max (Real.log (3 / a)) 0 + ε ≤ Cfinal)
    (_hlower : Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hprime Q
        childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        (scheduledFrequencyHistory cutoff (n + 1)) center‖), False := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventual_selected_final_natural_energy_comparison n ψ C₀ K d ε hd hε hψ)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (eventual_rounded_frequency_card (n + 1) d hd)
  refine ⟨max M₀ R₀, ?_⟩
  filter_upwards [eventual_selected_final_pair_decay role n Aw Kr s C S H z α β γ c
    hs hC hS hH hz hα hαβ hγβ hc,
    eventual_scheduled_final_contradiction n B₁ (d + 1) Cfinal 1 z α (c / 32)
      hB₁ (by linarith) (by norm_num) hz hα (by positivity) hentropy] with L hdec hcontra
  intro size Smax hSmax hsize M hMlarge hm hmL hSm cutoff χ κ hκ pivot childBound pivotBound ranges
    hrange hcount X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk anchor ha hp P hP hprime
    Q hQP hQmass A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP
    hVfreq hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio
    hlarge i hiword hlo₀ h J hmod hcellrange a C₁ ha₀ hL hcellmass hJ center hMm hLm hC₁ hcost hamp
  have hcutoff : Monotone cutoff := naturalTransferCutoff_monotone _ _ (mul_nonneg hd hm)
  have hfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)) := by
    apply hVfreq.trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hC]
  have hpairs := hdec size Smax hSmax hsize M hm hmL hSm χ κ hκ pivot childBound pivotBound
    ranges hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu m bulk hbulk anchor ha hp P hP hprime
    Q hQP hQmass A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP
    cutoff hcutoff hfreq hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio
  have hupper := hM₀ M ((le_max_left _ _).trans hMlarge) role size χ κ hκ pivot childBound pivotBound ranges i hiword hu m bulk hbulk
    X lo hi P (fun p hp => ⟨hprime p hp, hlarge p hp⟩) Q
    hX hXlo hlo₀ hQP (fun i => ne_of_gt (hQmass i)) h J hmod hcellrange a C₁ L ha₀ hL
    hcellmass hJ center _ (Real.exp_nonneg _)
    (fun e f hef d d' hd => hpairs e f hef d d' hd hlarge center)

  have hcard₀ := hR₀ M ((le_max_right _ _).trans hMlarge) (n + 1) le_rfl
  have hcard : ((transferFrequencyRange (cutoff (n + 1))).card : ℝ) ≤
      Real.exp ((d + 1) * (2 ^ (n + 1) : ℝ) * m) := by
    apply hcard₀.trans
    apply Real.exp_le_exp.mpr
    have hp : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    rw [hMm]
    have hmul := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hmul]
  have he : (C₁ + max (Real.log (3 / a)) 0) * (2 ^ (n + 1) : ℕ) * L + ε * M ≤
      Cfinal * (2 ^ (n + 1) : ℝ) * m := by
    rw [hMm]
    have hh := selected_prime_energy_exponent_le n m L
      (C₁ + max (Real.log (3 / a)) 0) ε
      (add_nonneg hC₁ (le_max_right _ _)) hε.le hLm
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1)))
      (Nat.cast_nonneg m))
  have hcompare := hupper.trans (mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he)
      (Nat.cast_nonneg _)) le_rfl) (Nat.cast_nonneg _))
  have hlog : Real.log 2 < (1 : ℝ) := by
    exact (Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)).trans_le (by norm_num)
  have hmone : 1 ≤ (m : ℝ) := (le_trans (show (1 : ℝ) ≤ L from hL) hLm)
  have hmargin : Real.log 2 < 1 * (2 ^ (n + 1) : ℝ) * m := by
    have hp : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hlog, hmone, hmul]
  apply hcontra m cutoff _ hcutoff ?_ hcard hmargin hamp hcompare
  simpa only [hMm] using hmL

end Ostmann

end OAI
