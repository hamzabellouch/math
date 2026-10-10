import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityCentralGoodSet
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataRecenteredSelector

namespace OAI

/-! Specialize common-set concentration to the manuscript's original
physical selector mesh, support, and Lipschitz bounds. This step precedes
popular recovery and introduces no extra selector assumptions. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

private theorem selector_far_of_reference {N : ℕ} {κ : Type}
    {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : PacketLatticeData N κ Label Item)
    (oldSlope t R cone w cutoff : ℝ) (hw : 0 < w) (hcut : 2*cone ≤ cutoff)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j))
    (j : Fin N) (l : P.labels j) (k : κ) (s : ℝ)
    (hcondition : P.referenceCondition oldSlope t R cone w j l)
    (hs : cutoff*((w/P.topLength)*(2:ℝ)^j.val) < |s-t|) : b j l k s = 0 := by
  by_contra hn
  rw [P.reference_angular_mesh w j] at hs
  have ht : |s-t| ≤ (2*cone)*(w/P.length j) := by
    calc
      _ ≤ |s-(oldSlope+P.rowSlope j l)|+|oldSlope+P.rowSlope j l-t| := abs_sub_le _ _ _
      _ ≤ cone*(w/P.length j)+cone*w/P.length j := add_le_add (hsupport j l k s hn) hcondition.2
      _ = _ := by ring
  exact (not_lt_of_ge (ht.trans (mul_le_mul_of_nonneg_right hcut
    (div_pos hw (P.length_pos j)).le))) hs

theorem source_density_selector_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F cone : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hcone : 0 ≤ cone) (hgap : cStar < cEta*cb)
    (aDensity p0 Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D)
    (hconeK : cone ≤ K) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ A Cn Ct L0 : ℝ, aDensity+3 < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 16 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ)
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
      (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
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
  obtain ⟨A,Cn,Ct,L0,haA,hA,hCn,hCt,hL0,hgood⟩ := source_density_selector_central_good_set
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    aDensity p0 Hloss Lip D K H J₀ haDensity hp0 hHloss hLip hD
  refine ⟨A,Cn,Ct,L0,haA,hA,hCn,hCt,hL0,?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope w tau Eset field forest T assigned R
    hprofile horder alt hAlt hw hwide hfrequency b hb hb1 hsupp hmotion hactive hlocal
    v hv f hf hf1 hspectrum haltSpectrum l r hslopes hfield hstrip hEstrip
    ratio Fset hratio hFset hFfinite hFstrip hratioExp hloghigh hratioEq
    widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthEq
  have hangle : 0 < w/P.topLength := div_pos hw P.topLength_pos
  have hwide1 : 1 ≤ (2*cone+1)*((2:ℝ)^(SourceParameters.stepExponent L*SourceParameters.blockCount L))^4 :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hcone]) (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  exact hgood L hL κ N Label Item P packets oldSlope cone w tau Eset field forest hprofile horder
      alt hAlt hw hcone hwide hfrequency (fun _ => w/P.topLength) 1 (2*cone+1) cone
      (SourceParameters.stepExponent L*SourceParameters.blockCount L) J₀
      (fun _ => hangle) (by norm_num) (le_refl _) (by simpa only [one_mul] using hJ)
      hwide1 hconeK
      (by intro i j; simpa only [P.reference_angular_mesh w j] using hlocal j)
      b hb hb1
      (by intro i j l k s _ hs; simpa only [P.reference_angular_mesh w j] using hsupp j l k s hs)
      (by intro i j l k s _ _; simpa only [P.reference_angular_mesh w j] using hmotion j l k s (T i).slope)
      (by
        intro i j l k s hc hs
        apply selector_far_of_reference P oldSlope (T i).slope (T i).length cone w
          ((2*cone+1)*((2:ℝ)^(SourceParameters.stepExponent L*SourceParameters.blockCount L))^4)
          hw _ b hsupp j l k s hc hs
        have hpow : 1 ≤ ((2:ℝ)^(SourceParameters.stepExponent L*SourceParameters.blockCount L))^4 :=
          one_le_pow₀ (one_le_pow₀ (by norm_num))
        nlinarith only [mul_le_mul_of_nonneg_left hpow (by linarith only [hcone] : 0 ≤ 2*cone+1),hcone])
      v hv f hf hf1 hspectrum haltSpectrum
      (by
        intro i j l _ hk
        obtain ⟨k,hk⟩ := hk
        simpa only [abs_sub_comm] using hactive j l k (T i).slope hk)
      (le_refl _) rfl l r hslopes hfield hstrip hEstrip ratio Fset hratio hFset hFfinite hFstrip
      hratioExp hloghigh hratioEq widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthEq

end LipschitzHilbert.PacketLatticeData

end

end OAI
