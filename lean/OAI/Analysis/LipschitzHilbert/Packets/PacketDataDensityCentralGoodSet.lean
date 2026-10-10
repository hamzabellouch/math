import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityForest
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedSelectorCentralGoodSet
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataJetBudget

namespace OAI

/-! The actual density forest supplies every geometric and witness input
of the common concentration, mask-removal and direction-count theorem.
The small auxiliary jet bound is derived from the raw profile bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_selector_central_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aDensity p0 Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn Ct L0 : ℝ, aDensity+3 < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 16 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope cone w tau : ℝ)
      (Eset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      let assigned := forest.assigned
      let R := fun i => (T i).length
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
    ∀ (angle : forest.keepers → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
      LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset ≤ ratio^2*(volume.prod volume).real Fset →
    ∀ widthScale : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ widthScale →
      widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
      P.width = widthScale*w →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, ∀ i, (T i).weight (L^(A+2)) (D:ℝ) z ≤ (2:ℝ)^D) ∧
        (∀ z ∈ G, Real.log (max 1 (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z)) ≤ 3*L) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*(p0+2*(aDensity+3)+1)+8)*((T top).weight (L^(A+2)) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset forest.keepers,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100 := by
  obtain ⟨A,Cn,Ct,Lbase,haA,hA,hCn,hCt,_hLbase,hmain⟩ := source_assigned_selector_central_good_set
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    (aDensity+3) (aDensity+2) (p0+2*(aDensity+3)+1) (aDensity+1) Hloss Lip D K H J₀
    (by linarith) (by linarith) (by linarith) (by linarith) hHloss hLip hD
  refine ⟨A,Cn,Ct,max Lbase 16,haA,hA,hCn,hCt,le_max_right _ _,?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope cone w tau Eset field forest T assigned R
    hprofile horder alt hAlt hw hcone hwide hfrequency
    angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
    b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
    l r hslopes hfield hlength hEstrip ratio Fset hratio hFset hFfinite hFstrip hNupper hlogRatio hEF
    widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthExact
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hL16 : 16 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hP := P.smallJetControl_referenceEnvelopeConstant hL16 (by linarith : 0 ≤ aDensity+3)
    P.width_pos.le (le_refl P.width) hprofile
  have hwidth (i : forest.keepers) : P.width ≤ L^(aDensity+3)*(T i).width := by
    rw [forest.width]
    exact le_mul_of_one_le_left P.width_pos.le (Real.one_le_rpow hL1 (by linarith))
  have hscale (i : forest.keepers) : 4*(L^(aDensity+3)*P.width) =
      4*(L^(aDensity+3)*(T i).width) := by rw [forest.width]
  have hS : (∑ i, (T i).area) ≤ L^(aDensity+1)*ratio^2*(volume.prod volume).real Fset :=
    forest.area_budget (by linarith) ratio _ measureReal_nonneg hEF
  have hwidthIdentity (i : forest.keepers) : (T i).width =
      widthScale*(T i).length*(w/(T i).length) := by
    rw [forest.width,hwidthExact]
    field_simp [(T i).length_pos.ne']
  exact hmain L hLb forest.keepers κ N Label Item P packets assigned
    (4*(L^(aDensity+3)*P.width)) (4*L^(aDensity+3))
    (smallJetRatio_ge_one hL1 (by linarith))
    (P.smallJetScale_control hLp P.width_pos.le (le_refl P.width)) hP horder
    alt hAlt T oldSlope R cone w hw hcone hwide hfrequency hwidth hscale
    forest.horizontal forest.transverse angle small wide radius E J hangle hsmall hsmall1
    hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar v hv f hf hf1
    hspectrum haltSpectrum hsep hJ hE forest.reference l r hslopes field hfield hlength
    forest.witness forest.measurable forest.disjoint
    (fun i z hz => ⟨hEstrip z (forest.subset i hz),forest.radius i z hz⟩)
    forest.close forest.mass forest.area_pos ratio Fset hratio hFset hFfinite hFstrip hNupper
    hlogRatio hS widthScale tau hwidthLow hwidthHigh htimeLow htimeHigh forest.short
    forest.finite forest.precision hwidthIdentity

end LipschitzHilbert.PacketLatticeData

end

end OAI
