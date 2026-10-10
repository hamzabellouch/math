import OAI.MeasureTheory.Falconer.Angular.StationaryProductIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularStationarySpatial
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceJetSupport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem signedStationaryJet_comp_add_const (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ) :
    signedStationaryJet plus j (fun t => f (t+θ)) 0 Λ = signedStationaryJet plus j f θ Λ := by
  cases plus <;> simp only [signedStationaryJet,normalizedStationaryJet,directStationaryOperator,
    Bool.false_eq_true,↓reduceIte,add_zero]
  congr 3
  congr 1
  funext t
  rw [add_right_comm]

theorem angularPairStationary_eq_zero_of_jets (β : Plane → UnitCircle → ℂ)
    (x y : Plane) (hd : 0 < ‖x-y‖) (r : ℝ) (hr : 0 < r) (n : ℕ)
    (hβ : ∀ z, ContDiff ℝ ∞ (fun t => β z (sourceUnitDirection t)))
    (hz : ∀ plus j, signedStationaryJet plus j
      (fun t => β x (sourceUnitDirection t)*conj (β y (sourceUnitDirection t)))
      (angularPairAngle x y) (r*‖x-y‖) = 0) :
    angularPairStationary β n x y r = 0 := by
  let f := fun t => β x (sourceUnitDirection t)*conj (β y (sourceUnitDirection t))
  have hf : ContDiff ℝ ∞ f := (hβ x).mul (Complex.conjCLE.contDiff.comp (hβ y))
  change fullCircleStationaryExpansion (r*‖x-y‖) (fun t => f (t+angularPairAngle x y)) n = 0
  rw [fullCircleStationaryExpansion_sum
    (show ContDiff ℝ ∞ (fun t => f (t+angularPairAngle x y)) from
      hf.comp (contDiff_id.add contDiff_const)) (mul_pos hr hd)]
  apply Finset.sum_eq_zero
  intro pair _
  simp only [signedStationaryTerm,signedStationaryJet_comp_add_const]
  rw [show signedStationaryJet pair.1 pair.2 f (angularPairAngle x y) (r*‖x-y‖) = 0 from hz _ _]
  exact mul_zero _

theorem uniform_actual_pair_approximant_good {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
    ∀ (ρ : Measure Plane) [SFinite ρ], ρ Q.carrierᶜ = 0 →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Finset PolicyDescriptor) (k : PolicyDescriptor → ℕ),
    remainingPolicyDescriptors (fun n => m n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S →
    ∀ (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ᵐ z ∂ρ.prod ρ, ∀ (n : ℕ) (r : ℝ), 0 < r → z.1 ≠ z.2 →
    angularPairStationary (inheritedCircleSymbol S id k Q ρ m N lam sig J i h) n z.1 z.2 r ≠ 0 →
    z ∈ positiveDistanceGoodSet Q ρ m N q b v lam sig J (i+1) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_pair_minimal_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h
  filter_upwards [h₀ N hN Q hQ ρ hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h]
    with z hz
  intro n r hpos hne hn
  by_contra hbad
  apply hn
  apply angularPairStationary_eq_zero_of_jets _ _ _ (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) r hpos n
    (inheritedCircleSymbol_contDiff _ _ _ _ (by rw [hQ]; norm_num) _ _ _ _ _ _ _ _)
  intro plus j
  by_contra hj
  apply hbad
  exact hz plus j (angularPairAngle z.1 z.2) _
    (sourceUnitDirection_sourceAngle (sourceRadialUnit z.2 z.1)).symm hj

end PlanarFalconer

end OAI
