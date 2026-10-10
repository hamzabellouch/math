import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedBoundaryError
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryIntegratedGain
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral

namespace OAI

/-! The actual assigned-packet boundary error has every prescribed
negative-power gain. Top-weight integrability is derived on the full
plane, and the polynomial mass budget absorbs the remaining integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_boundary_gain (D q m decay : ℝ) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (tops : Finset τ) (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w Freq : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hFreq : 0 ≤ Freq) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ Freq/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (test : ℝ×ℝ → EuclideanSpace ℂ κ)
      (g : AngularGrid) (maskExponent cutoff Kw : ℝ),
      (g.branching:ℝ) = SourceParameters.step L → 0 < Kw →
    ∀ (K : ℕ), 0 < K →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, P.length s.1 ≤ (T (assigned s)).length) →
      (∀ s ∈ packets, P.referenceCondition oldSlope (T (assigned s)).slope
        (R (assigned s)) cone w s.1 s.2.1) →
      (∀ j, g.eligible cutoff (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible cutoff (w/(T t).length) 0) →
    ∀ (a Nmass Fmass : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Nmass → 0 ≤ Fmass →
    ∀ good : Set (ℝ×ℝ), MeasurableSet good →
      (∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ 3*L) →
      (∫ x in good, ∑ t ∈ tops, (T t).weight Kw D x ∂volume.prod volume) ≤
        L^m*Nmass*Fmass →
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt hAlt
    (∀ x ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Q t).withProfile (alts t) (halt t)).rawInterval
          (fun j l u => P.physicalMultiplierCoefficient oldSlope b v test j (orig t j l) u.val)
          0 lower upper x.1 (x.2-(T t).slope*x.1)‖ ≤ L^q*((T t).weight Kw D x)^8) →
    let stop := fun s : P.PacketIndex => g.lastEligible cutoff (w/P.length s.1)
      (div_pos hw (P.length_pos s.1))
    let value := P.physicalMaskedValue alt hAlt oldSlope b v test
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let err := fun z : ℝ×(ℝ×ℝ) => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖
    Integrable err ((volume.restrict (Ioc 0 g.rootWidth)).prod ((volume.prod volume).restrict good)) ∧
      IntervalIntegrable (fun origin => ∫ x in good, err (origin,x) ∂volume.prod volume) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ∫ x in good, err (origin,x) ∂volume.prod volume)/g.rootWidth ≤
        L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_boundary_radius_small,
    eventually_boundary_integrated_gain_wide D q m decay] with L hL hsmall hgain
  intro τ κ _ N Label Item _ P packets assigned tops T oldSlope R cone w Freq hw hcone hFreq
    hwide hfrequency alt hAlt b v test g maskExponent cutoff Kw hbranch hKw K hK
    hassigned hshort hcondition hstart htopstart a Nmass Fmass ha ha1 hNmass hFmass
    good hgood hlog hmass Q orig alts halt hinterval stop value err
  have hweight : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight Kw D x) good (volume.prod volume) :=
    (integrable_finsetSum _ (fun t _ => (T t).weight_integrable hKw hD)).integrableOn
  have hresult := P.assigned_boundary_integrated_error packets assigned tops T oldSlope R cone w Freq
    hw hcone hFreq hwide hfrequency alt hAlt b v test g L maskExponent cutoff Kw D hbranch
    hsmall hKw (by linarith) hK hassigned hshort hcondition hstart htopstart a (L^q) (3*L)
    ha (Real.rpow_nonneg (by linarith) _) (volume.prod volume) good hgood hweight hlog hinterval
  refine ⟨hresult.1,hresult.2.1,hresult.2.2.trans ?_⟩
  exact hgain a Nmass Fmass _ ha ha1 hNmass hFmass hmass

end LipschitzHilbert.PacketLatticeData

end

end OAI
