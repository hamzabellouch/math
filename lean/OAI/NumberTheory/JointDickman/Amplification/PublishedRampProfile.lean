import OAI.NumberTheory.JointDickman.Amplification.CellAverageProfile

namespace OAI

/-! # The smoothed prime channel profile from published inputs -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology NNReal

open Classical in
noncomputable def primeRampCell {D : Type*} [DecidableEq D]
    (B q : ℕ) (lower upper : D → ℝ) (lo hi : ℝ)
    (c : auxiliaryPrimes B → Bool) (a : D × (ZMod q)ˣ) : ℝ :=
  optionCellMass
    (fun e => quarterPrimeMass (auxiliaryPrimes B) e *
      averagingRamp lo hi (Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B))
    (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c) a

open Classical in
/-- Uniform bounded Lipschitz profiles and their actual weighted cell law.
The constants may depend on the fixed ramp, never on the partition or B. -/
theorem primeRampProfile_from_published
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ lo hi : ℝ, 0 < lo → lo < hi →
      ∃ M L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
        (∀ x, |rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi x| ≤ M) ∧
        LipschitzWith L (rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi) ∧
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, lower d < upper d) → (∀ d, upper d ≤ 16 / 5) →
        ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |primeRampCell B q lower upper lo hi c (d, r) -
          (∫ x in lower d..upper d,
            rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
              (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, _, H, C, hC, hlocal⟩ := primeRampCell_local_law hSD hSW hM
  refine ⟨v, hv, H, C, hC, ?_⟩
  intro lo hi hlo hlohi
  obtain ⟨M, hM0, L, hbound⟩ := scaledRoughDensity_bounded_lipschitz hM hMP v hv
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) hlo H
  let M₀ : ℝ≥0 := ⟨M, hM0⟩
  let L₀ : ℝ≥0 := ⟨(L : ℝ) + (1 / (hi - lo)) * (M₀ : ℝ), by positivity⟩
  refine ⟨M₀, L₀, ?_⟩
  have hsmall : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ lo := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
    exact (ht.eventually (eventually_lt_nhds hlo)).mono (fun _ h => h.le)
  filter_upwards [hlocal, hbound, hsmall] with B hlocalB hboundB hsmallB
  refine ⟨rampDensity_bound _ hlohi hboundB.1,
    rampDensity_lipschitz _ hlohi hboundB.1 hboundB.2, ?_⟩
  intro D _ q _ hq lower upper hdisjoint horder hupper c d r
  have hh := hlocalB D q hq lo hi hsmallB hlohi lower upper hdisjoint hupper c d r
  rw [rampIntervalIntegral_eq_rampDensity _ hlohi hboundB.2 (horder d).le] at hh
  exact hh

/-- The integral profile can be evaluated at a cell endpoint after
normalization, with explicit local-law and mesh errors. -/
theorem primeRampCell_normalized_error {D : Type*} [DecidableEq D]
    {v : ℕ → ℝ} {H B q : ℕ} {lower upper : D → ℝ} {lo hi : ℝ} {L : ℝ≥0} {ε : ℝ}
    (hφ : 0 < (q.totient : ℝ))
    (hLip : LipschitzWith L (rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi))
    (c : auxiliaryPrimes B → Bool) (d : D) (r : (ZMod q)ˣ)
    (horder : lower d < upper d)
    (hlocal : |primeRampCell B q lower upper lo hi c (d, r) -
      (∫ x in lower d..upper d,
        rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
          (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)) / q.totient| ≤ ε) :
    |primeRampCell B q lower upper lo hi c (d, r) / ((upper d - lower d) / q.totient) -
      rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
        (lower d - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)| ≤
      ε / ((upper d - lower d) / q.totient) + L * (upper d - lower d) :=
  normalizedCell_profile_error hLip horder hφ _ hlocal

end JointDickman

end OAI
