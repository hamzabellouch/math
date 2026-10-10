import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopSelector
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentration

namespace OAI

/-! Original-selector concentration for the assigned top families,
recentered at their own slopes. All source bounds concern the original
labels and selected packets. Neither restriction introduces multiplicity
or changes the analyzing coefficient. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_top_selector_concentration (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (rate aWeight p Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : SourceLabeledLattice N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      P.absoluteConstant ≤ L^p → 6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.topLength ≤ L^aWeight*(T top).length) →
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, P.scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
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
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let V := fun x y => ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
              j (orig top j l) u.val) 0 lower upper x y
          ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
            ‖covariantSignal P.frequency (fun k y => V z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  filter_upwards [eventually_source_selector_concentration hL cStar cEta CEta cb Cb F
    hcStar hcEta hCEta hcb hCb hF hgap rate aWeight p Lip D K H J₀
    hrate haWeight hp hLip] with L hconc
  intro τ κ _ _ N Label Item _ P packets assigned hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hlength hwidth hscale hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
  classical
  let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
    oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
  let orig := fun top j (l : (Q top).labels j) =>
    ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
      oldSlope (T top).slope (R top) cone w j l).val.2
  let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
    alt j (orig top j l) u.val k
  let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
    hAlt j (orig top j l) u.val k
  change ∃ bad, _
  have hcond top j (l : (Q top).labels j) :
      P.referenceCondition oldSlope (T top).slope (R top) cone w j (orig top j l) :=
    P.assignedTopReference_condition packets assigned top oldSlope (T top).slope
      (R top) cone w F hw hcone hF hwide hfrequency j l
  have hgeometry top : SourceLabeledTopGeometry (Q top) (T top) (L^aWeight) D := by
    apply P.assignedTopReference_topGeometry packets assigned top oldSlope (R top) cone w F
      hw hcone hF hwide hfrequency (T top) (L^aWeight) D
      (hlength top) (hwidth top) (by omega) (hscale top)
    · intro q hq heq
      simpa only [heq] using hX q hq
    · intro q hq heq
      simpa only [heq] using hZ q hq
  have hcenter top j (l : (Q top).labels j) :
      (T top).slope+(Q top).rowSlope j l = oldSlope+P.rowSlope j (orig top j l) :=
    P.assignedTopReference_physical_center packets assigned top oldSlope (T top).slope
      (R top) cone w F hw hcone hF hwide hfrequency j l
  have hactive top j (l : (Q top).labels j)
      (hl : ∃ k, b j (orig top j l) k (T top).slope ≠ 0) :
      cb*w/(Q top).length j ≤ |(Q top).rowSlope j l| ∧
        |(Q top).rowSlope j l| ≤ Cb*w/(Q top).length j := by
    have hs := hsep top j (orig top j l) (hcond top j l) hl
    have he : (Q top).rowSlope j l = oldSlope+P.rowSlope j (orig top j l)-(T top).slope := by
      linarith [hcenter top j l]
    rw [he]
    exact hs
  obtain ⟨bad,hbad,harea,hpoint⟩ := hconc τ κ (fun _ => N)
    (fun _ j => τ×P.labels j) (fun _ => P.AssignedTopItem packets assigned) Q
    (fun _ => hP) (fun _ => horder) a ha T hgeometry angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius
    (fun top j => P.assignedTopReference_localMultiplicity packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency j
      (angle top*(2:ℝ)^j.val) H (hlocal top j))
    (fun top j l => b j (orig top j l))
    (fun _ j l k => hb j _ k) (fun _ j l k s => hb1 j _ k s)
    (by
      intro top j l k s hs
      rw [hcenter top j l]
      exact hsupport top j (orig top j l) k s (hcond top j l) hs)
    (fun top j l k s => hnear top j (orig top j l) k s (hcond top j l))
    (fun top j l k s => hfar top j (orig top j l) k s (hcond top j l))
    (fun _ => v) (fun _ => hv) (fun _ => f) (fun _ => hf) (fun _ => hf1) w hw
    (fun _ => hfrequency)
    (fun top => P.assignedTopReference_spectrum packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      cStar cEta CEta (fun q hq _ => hspectrum q hq))
    (fun top => P.assignedTopReference_alt_spectrum packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      alt hAlt cStar cEta CEta (fun q hq _ => haltSpectrum q hq))
    hactive hJ hE
  refine ⟨bad,hbad,harea,?_⟩
  intro top lower upper hlu hu z shift hshift hz
  have hcoeff : (Q top).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig top j l)) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  have h := hpoint top lower upper hlu hu z shift hshift hz
  rw [hcoeff] at h
  exact h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
