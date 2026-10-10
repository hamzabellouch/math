import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierSpatialNetBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialInvariantBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.ActualTailTiltBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialPointwise_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.initial_pointwise {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) {N K : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ θ : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < θ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (y : Space) (hy : ‖y‖ ≤ (11/10)*r₀) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | θ < innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
        (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
          (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r₀ k
  let P : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) → ℝ :=
    fun z => innerPotential r₀ (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
  let A := {z | θ < P z}
  have hA : MeasurableSet[observationInformation ell j] A :=
    measurableSet_lt measurable_const
      (jointMasterPosterior_inner_measurable (graphRawLaw F) ell j r₀ y hc hr hs hg.continuous)
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  change p < p₀ j
  by_contra! hnot
  have hp : 0 < p := h₀.trans_le hnot
  obtain ⟨G,hGn,hlaw,hE⟩ := hF.2.2 j A hA hnot
  have hb : formEnergy Z (graphFormVector G) ≤ allSectorEnergy Z+(Z:ℝ)^(7/3:ℝ) := by
    have he := actual_priced_excess_unshifted_bound Z hlam G hGn ((le_max_left _ _).trans hE)
    have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have hnon : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    have hcoarse : lam*(2*(Z:ℝ)+1-(N:ℝ)) ≤ 3*(Z:ℝ)*lam := by nlinarith
    change formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+(Z:ℝ)^(7/3:ℝ)
    linarith only [he,hcoarse,hbudget]
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hcount := actual_priced_particle_bound_three Z hZ hlam hN
  have hupper := normalized_inner_event_global_bound (graphRawLaw F)
    (graphFormVector_admissible G hGn) ell j y hi he hc hc1 hr hs hs1 hg hcg hgn hrad hgs hy hA hp
    (by simpa only [formRawLaw_graph] using hlaw)
    (show (1:ℝ) ≤ Z by exact_mod_cast hZ) (Real.rpow_nonneg (Nat.cast_nonneg Z) _)
    (show (N:ℝ) ≤ 3*Z by exact_mod_cast hcount) hb
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_inner_integrable (graphRawLaw F) ell j r₀ y hi he hc hr hs hg hcg hgn hrad hgs
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K) hPi
    ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hp
  exact (not_le_of_gt (hupper.trans_lt hsmall)) hlower

end CoulombAtom

end Work_TailInitialPointwise_barrier_scope

section Work_TailInitialGood_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem tail_initial_good_event {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ G : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j) (hp40 : p₀ j ≤ r₀^40)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < (Z:ℝ)/(20*r₀))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
      MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j] A ∧
      (∀ z ∈ A, ∀ y : Space, ‖y‖ ≤ (11/10)*r₀ →
        innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
            (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y ≤ (Z:ℝ)/(10*r₀)) ∧
      (physicalObservationLaw (graphRawLaw F) K).real Aᶜ ≤ 1728*r₀^37 := by
  have hcount := actual_priced_particle_bound_three Z hZ hlam hN
  have hpoint := hF.initial_pointwise hZ hlam hr hs hs1 hc hc1 hN j h₀ hbudget hsmall hg hcg hgn hrad hgs
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r₀ k
  let P := fun z y => innerPotential r₀ (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
  let L := (16*Real.pi*(N:ℝ)*G*c₁⁻¹^3)*r₀^(-2-3*masterExponent)
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_initial_spatial_net hr hr1
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hm (y : Space) : Measurable[observationInformation ell j] (fun z => P z y) :=
    jointMasterPosterior_inner_measurable (graphRawLaw F) ell j r₀ y hc hr hs hg.continuous
  obtain ⟨A,hA,hgood,hbad⟩ := finite_net_good_event (physicalObservationLaw (graphRawLaw F) K) P Q
    (A := {y : Space | ‖y‖ ≤ (11/10)*r₀}) (θ := (Z:ℝ)/(20*r₀)) (p := r₀^40) (L := L) (d := r₀^2)
    (fun y _ => hm y) (fun y hy => (hpoint y (hQ y hy)).le.trans hp40) hcover hQ (by dsimp [L]; positivity)
    (fun z x hx y hy => jointMasterPosterior_inner_difference (graphRawLaw F) ell j hc hr hs hrs hg.continuous hG _ x y hx hy)
  refine ⟨A,hA,?_,?_⟩
  · intro z hz y hy
    have hh := hgood z hz y hy
    have hi := initial_interpolation_bound (show (N:ℝ) ≤ 3*(Z:ℝ) by exact_mod_cast hcount) hr hc hGn hinterp
    change L*r₀^2 ≤ (Z:ℝ)/(20*r₀) at hi
    change P z y ≤ (Z:ℝ)/(10*r₀)
    have he : (Z:ℝ)/(10*r₀) = 2*((Z:ℝ)/(20*r₀)) := by ring
    rw [he]
    linarith
  · exact hbad.trans ((mul_le_mul_of_nonneg_right hcard (pow_nonneg hr.le 40)).trans_eq (initial_net_probability hr))

end CoulombBarrier

end Work_TailInitialGood_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem tail_initial_barrier {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ ε k B : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B)
    (hrel : (Z:ℝ)*r₀^3 = ε^3)
    (heps : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hquad : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBsmall : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ G : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j) (hp40 : p₀ j ≤ r₀^40)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ a p : OriginalDatum N K (fun k => dyadicObservationWidth r₀ k) j → TFSpace → ℝ,
      IsNuclearBarrier
        ((physicalObservationLaw (graphRawLaw F) K).map
          (originalDatum (fun k => dyadicObservationWidth r₀ k) j))
        (jointMasterPosterior (graphRawLaw F) (fun k => dyadicObservationWidth r₀ k) j c₁ r₀ s g)
        (Z:ℝ) k B (max B (32*ε^3)) r₀ 2 (5184*r₀^32) a p := by
  have hZr : 0 < (Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hZ)
  have hsmall := initial_density_small_of_nuclear_relation hZr hr hε hrel heps
  have hcount := actual_priced_particle_bound_three Z hZ hlam hN
  obtain ⟨A,hA,hgood,hbad⟩ := tail_initial_good_event hZ hlam hr hr1 hs hs1 hrs hc hc1
    hN hF j h₀ hp40 hbudget hsmall hinterp hg hcg hG hgn hrad hgs
  let := graphRawLaw_probability F hF.1
  let ell : Fin K → ℝ := fun l => dyadicObservationWidth r₀ l
  let μ := jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g
  let P := (physicalObservationLaw (graphRawLaw F) K).map (originalDatum ell j)
  have hP : IsProbabilityMeasure P := inferInstance
  let := hP
  let A' : Set (OriginalDatum N K ell j) := A
  have hAm : MeasurableSet A' := hA
  have hbad' : P.real A'ᶜ ≤ 1728*r₀^37 := by
    change ((physicalObservationLaw (graphRawLaw F) K).map (originalDatum ell j)).real A'ᶜ ≤ _
    rw [map_measureReal_apply (originalDatum_measurable ell j) hAm.compl]
    exact hbad
  obtain ⟨M,hM,hMb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr hs hrs hg.continuous hcg
  have hμm : Measurable (Function.uncurry μ) := jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr hs hg.continuous
  have hμn : ∀ z y, 0 ≤ μ z y := jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s g
  have hμb : ∀ z y, μ z y ≤ M := fun z y => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hMb z y)
  have hμi : ∀ z, Integrable (μ z) := jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr hs hg.continuous hgn
  have hμc : ∀ z, ∫ y, μ z y ≤ (N:ℝ) := fun z =>
    (jointMasterPosterior_mass (graphRawLaw F) ell j hc hr hs hg.continuous hgn z).le
  have hi := initial_barrier_invariant hAm hμm hM (Nat.cast_nonneg N) hZr hB hr hr1 hε hε1 hk
    hrel hquad hBsmall hsub hμn hμb hμi hμc (by exact_mod_cast hcount) hgood hbad'
  exact ⟨_,_,hi⟩

end CoulombBarrier

end

end OAI
