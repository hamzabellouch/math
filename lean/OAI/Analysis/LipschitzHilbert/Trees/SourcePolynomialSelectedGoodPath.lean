import OAI.Analysis.LipschitzHilbert.Trees.SourcePolynomialReferenceArea
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledUniformGoodTail

namespace OAI

/-! The selected-reference weighted good set follows from original
packet spectra and selector hypotheses. The component event estimates
are proved internally, including the exact reference/path slope change.
No exceptional-set or variation estimate is supplied as source data. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_polynomial_uniform_selected_reference_good_path
    (hVariation : LepingleInput)
    (D eventPower weightPower q A F cStar cEta CEta cb Cb maskCone Lip : ℝ)
    (K Hlabels J₀ : ℕ) (hD : 2 < D)
    (hq : 0 ≤ q) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hLip : 0 ≤ Lip) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw : ℝ), 1 ≤ Kw → Kw ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (pathTop : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
      (Q : ∀ t i, Finset (P t i).family.PacketIndex) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ i ∈ events t,
        let R := P t i
        6 ≤ R.family.order ∧ R.family.absoluteConstant ≤ L^q ∧ R.slope = (pathTop t).slope ∧
        ∃ (c Cwide radius : ℝ) (E Jcut : ℕ) (w : ℝ),
          0 < R.angle ∧ 0 < c ∧ c ≤ 1 ∧ Cwide ≤ c*(2:ℝ)^Jcut ∧
          1 ≤ Cwide*((2:ℝ)^E)^4 ∧ radius ≤ K ∧
          (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
            (fun l : R.family.labels j => R.slope+R.family.rowSlope j l)
            (R.angle*(2:ℝ)^j.val) Hlabels) ∧
          (∀ j l k, Measurable (R.selector j l k)) ∧
          (∀ j l k s, ‖R.selector j l k s‖ ≤ 1) ∧
          (∀ j l k s, R.selector j l k s ≠ 0 →
            |s-(R.slope+R.family.rowSlope j l)| ≤ radius*(R.angle*(2:ℝ)^j.val)) ∧
          (∀ j l k s, |s-R.slope| ≤ c*(R.angle*(2:ℝ)^j.val) →
            ‖R.selector j l k s-R.selector j l k R.slope‖ ≤
              Lip*(|s-R.slope|/(R.angle*(2:ℝ)^j.val))) ∧
          (∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(R.angle*(2:ℝ)^j.val) < |s-R.slope| →
            R.selector j l k s = 0) ∧
          Measurable R.direction ∧ Measurable R.test ∧ (∀ z, ‖R.test z‖ ≤ 1) ∧
          Jcut ≤ J₀ ∧ E = SourceParameters.stepExponent L*SourceParameters.blockCount L ∧
          0 < w ∧ Cb*w ≤ R.family.width ∧ (∀ k, |R.family.frequency k| ≤ F/w) ∧
          (∀ j l u k xi eta,
            planarAngularFourier (R.family.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
              |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
                cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
          (∀ j l u k xi eta,
            planarAngularFourier ((R.family.withProfile R.alternate R.alternate_bound).physicalPacket
              R.slope j l u k) (xi,eta) ≠ 0 →
              |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
                cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
          (∀ j l, (∃ k, R.selector j l k R.slope ≠ 0) →
            cb*w/R.family.length j ≤ |R.family.rowSlope j l| ∧
              |R.family.rowSlope j l| ≤ Cb*w/R.family.length j) ∧
          (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
            R.family.length j ≤ (R.packetTop j l u).length) ∧
          (∀ j (_l : R.family.labels j), R.family.length j ≤ (pathTop t).length) ∧
          (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
            R.family.length j ≤ (pathTop t).length →
            |R.family.rowSlope j l| ≤ Cb*w/R.family.length j →
            |R.slope-(R.packetTop j l u).slope| ≤
              maskCone*(R.packetTop j l u).width/R.family.length j)) →
      let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad
        L A (q+8) (2*q+9) (2*q+11)
      let good := sourceGoodPathSet base tops (fun t => (pathTop t).weight Kw D) bad L
      Integrable (sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad)
        (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad z
        ∂volume.prod volume) ≤
        (∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i ∈ events t,
        z ∉ ((P t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11) ∧
        ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
          finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
            (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
            (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
            (2*H) ≤ (L^(2*q+11))^3 := by
  filter_upwards [SourceLabeledLattice.eventually_uniform_physical_reference_good_tail
      hVariation q 12 A F cStar cEta CEta cb Cb maskCone Lip K Hlabels J₀
      hq (by norm_num) hA hF hcStar hcEta hCEta hcb hCb hmaskCone hLip hgap,
    eventually_polynomial_selected_reference_prefix_area D eventPower weightPower hD] with L htail harea
  intro Kw hKw hKwL ι σ tops pathTop events N κ Label Item _ _ P Q base hbase hcard hdata
  apply harea Kw hKw hKwL ι σ tops pathTop events N κ Label Item P Q A (q+8) (2*q+9) (2*q+11)
    base hbase hcard
  intro t ht
  filter_upwards [] with y
  intro tile i hi
  obtain ⟨horder,hP,hslope,c,Cwide,radius,E,Jcut,w,hcutoff,hc,hc1,hC,hwideError,hradius,
    hlocal,hb,hb1,hsupport,hnear,hfar,hv,hg,hg1,hJcut,hE,hw,hwide,hfrequency,
    hspectrum,haltSpectrum,hselector,hlength,hshort,hangle⟩ := hdata t ht i hi
  let R := P t i
  let Fsel := R.family.restrictPackets (Q t i)
  let alt := R.family.restrictedAlternate R.alternate (Q t i)
  have hmem (j : Fin N) (l : Fsel.labels j)
      (u : R.family.RestrictedPacketItem (Q t i) j l) :
      (⟨j,⟨l,u.val⟩⟩ : R.family.PacketIndex) ∈ Q t i := by
    obtain ⟨_,hm⟩ := u.property
    exact hm
  have hAlt := R.family.restrictedAlternate_bound R.alternate R.alternate_bound (Q t i)
  have hspectrum' : ∀ j l u k xi eta,
      planarAngularFourier (Fsel.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
        |xi+(R.slope+Fsel.rowSlope j l)*eta| ≤ cStar/Fsel.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hxi
    exact hspectrum j l u.val k xi eta hxi
  have haltSpectrum' : ∀ j l u k xi eta,
      planarAngularFourier ((Fsel.withProfile alt hAlt).physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
        |xi+(R.slope+Fsel.rowSlope j l)*eta| ≤ cStar/Fsel.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hxi
    exact haltSpectrum j l u.val k xi eta hxi
  have h := htail N κ Label (R.family.RestrictedPacketItem (Q t i)) Fsel horder hP
    alt hAlt R.slope R.angle c Cwide radius E Jcut hcutoff hc hc1 hC hwideError hradius
    hlocal R.selector hb hb1 hsupport hnear hfar R.direction hv R.test hg hg1 hJcut hE
    w hw hwide hfrequency hspectrum' haltSpectrum' hselector
    (fun j l u => R.packetTop j l u.val) (fun j l u => hlength j l u.val (hmem j l u))
    y ((pathTop t).length*tile) (pathTop t).length (pathTop t).length_pos hshort
    (fun j l u => hangle j l u.val (hmem j l u))
  have htile : sourceLineTile (pathTop t).length tile =
      Ico ((pathTop t).length*tile) ((pathTop t).length*tile+(pathTop t).length) := by
    unfold sourceLineTile
    congr 1
    ring
  have hmeasure : (volume.restrict (sourceLineTile (pathTop t).length tile)) univ =
      ENNReal.ofReal (pathTop t).length := by
    rw [htile,Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  rw [hmeasure,htile]
  have hbad : ((P t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11) =
      Fsel.physicalReferenceBad alt hAlt R.slope R.angle R.selector R.direction R.test
        (fun j l u => R.packetTop j l u.val) L A (q+8) (2*q+9) (2*q+11) := rfl
  rw [hbad]
  have hslope' : R.slope = (pathTop t).slope := hslope
  simpa only [hslope'] using h

end LipschitzHilbert

end

end OAI
