import OAI.NumberTheory.JointDickman.Amplification.ClippedProfile

namespace OAI

/-! # The actual prime-product local law with a ramp weight -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology

open Classical in
noncomputable def rampIntervalIntegral (f : ℝ → ℝ) (lo hi a b t : ℝ) : ℝ :=
  (∫ θ in lo..hi, clippedIntervalIntegral f θ a b t) / (hi - lo)

open Classical in
/-- The sharp published-input consequence survives averaging the cutoff,
with the same error and uniformity in the finite partition. -/
theorem primeRampCell_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < v 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lo hi : ℝ, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ lo → lo < hi →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, upper d ≤ 16 / 5) → ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |optionCellMass
            (fun e => quarterPrimeMass (auxiliaryPrimes B) e *
              averagingRamp lo hi (Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B))
            (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c) (d, r) -
          rampIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
            lo hi (lower d) (upper d)
            (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, hvpos, H, C, hC, hbound⟩ := highExclusiveLogCell_threshold_law hSD hSW hM
  refine ⟨v, hv, hvpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq lo hi hlo hlohi lower upper hdisjoint hupper c d r
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hlopos : 0 < lo := (Real.rpow_pos_of_pos hBpos _).trans_le hlo
  have hip := (scaledClippedProfile_intervalIntegrable v (1 / 4) H B
    hlopos hlohi.le (lower d) (upper d)
    (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)).div_const (q.totient : ℝ)
  have herr := rampCellMass_local_error
    (quarterPrimeMass (auxiliaryPrimes B))
    (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper))
    (fun e => Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B)
    c (d, r) hlohi _ hip (fun θ hθ =>
      hboundB D q hq θ (hlo.trans hθ.1) lower upper hdisjoint hupper c d r)
  simpa only [rampIntervalIntegral, intervalIntegral.integral_div, div_div, mul_comm] using herr

end JointDickman

end OAI
