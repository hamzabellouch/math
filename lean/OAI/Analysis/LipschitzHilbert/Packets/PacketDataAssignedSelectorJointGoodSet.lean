import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedSelectorControlledGoodSet
import OAI.Analysis.LipschitzHilbert.Trees.SourceSimultaneousCount
import OAI.Analysis.LipschitzHilbert.Estimates.PlaneSlopeLipschitz

namespace OAI

/-! A common fixed set for the actual original selector coefficients,
mask removal and the simultaneous direction count at the larger dilation.
All numerical choices precede the finite packet and top families. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_selector_joint_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aWeight aw p s Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haWeight : 0 ≤ aWeight) (haw : 0 ≤ aw) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn Ct L0 : ℝ, aWeight < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 2 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
    ∀ (scale ratioBound : ℝ) (hratioBound : 1 ≤ ratioBound)
      (hcontrol : |scale/P.width| ≤ ratioBound),
      (P.withJetControl scale ratioBound hratioBound hcontrol).referenceEnvelopeConstant ≤ L^p →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, scale = 4*(L^aWeight*(T top).width)) →
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
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ), LipschitzWith 1 u → 600*(r-l) ≤ 1 →
    ∀ witness : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (witness i)) →
      (Pairwise fun i j => Disjoint (witness i) (witness j)) →
      (∀ i z, z ∈ witness i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (witness i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real Fset →
    ∀ widthScale timeScale : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ widthScale →
      widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      0 ≤ timeScale → timeScale ≤ Real.exp (-(L^(97/100:ℝ))) →
      (∀ i, (T i).length ≤ timeScale) →
      (∀ i, (volume.prod volume) (witness i) ≠ ∞) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤ w/(T i).length) →
      (∀ i, (T i).width = widthScale*(T i).length*(w/(T i).length)) →
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
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset τ,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100 := by
  obtain ⟨A,Cn,Lmask,haA,hA,hCn,hLm,hmask⟩ := source_assigned_selector_mask_good_set_with_jet_control
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    aWeight aw p s (Hloss+1) Lip D K H J₀ haWeight haw hp hs (by linarith) hLip hD
  let pg := aw+A+4
  let tg := 2*aw+pg+2
  have hap : aw+1 ≤ pg := by dsimp [pg]; linarith
  have hkp : (A+2)+1 ≤ pg := by dsimp [pg]; linarith
  have ht : 2*aw+pg+1 ≤ tg := by dsimp [tg]; linarith
  obtain ⟨Lcount,hLcount⟩ := eventually_atTop.mp
    (eventually_source_simultaneous_count_universal 2 aw (A+2) pg tg 9 1 10 haw hap hkp ht
      (by norm_num) (by norm_num))
  obtain ⟨Larea,hLarea⟩ := eventually_atTop.mp (eventually_top_area_factor s Hloss)
  let L0 := max Lmask (max Lcount Larea)
  refine ⟨A,Cn,tg+4,L0,haA,hA,hCn,?_,hLm.trans (le_max_left _ _),?_⟩
  · dsimp [tg,pg]; linarith
  intro L hL τ κ _ _ N Label Item _ P packets assigned scale ratioBound hratioBound hcontrol hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscaleEq hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE hcondition l r hslopes u hu hlength
    witness hW hdisj hinside hclose hsize hSpos ratio Fset hratio hFset hFfinite hFstrip hNupper hS
    widthScale timeScale hwidthLow hwidthHigh htimeLow htimeHigh htopLength hWfinite hprecision hwidthExact
    Q orig a ha
  have hLmL : Lmask ≤ L := (le_max_left _ _).trans hL
  have hLcL : Lcount ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLaL : Larea ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 2 ≤ L := hLm.trans hLmL
  have hLpos : 0 < L := by linarith
  have hlength' : 300*((2*(1:ℝ≥0):ℝ≥0):ℝ)*(r-l) ≤ 1 := by norm_num; exact hlength
  obtain ⟨G₁,hG₁,hG₁F,harea₁,hcount₁,htop₁,hint₁,herror₁⟩ :=
    hmask L hLmL τ κ N Label Item P packets assigned scale ratioBound hratioBound hcontrol hP horder alt hAlt T oldSlope R cone w
      hw hcone hwide hfrequency hwidth hscaleEq hX hZ
      angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
      b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
      hcondition l r hslopes u 1 hu hlength' witness hW hdisj hinside hclose hsize hSpos
      ratio Fset hratio hFset hFfinite hFstrip hNupper hS
  have huProd : LipschitzWith 2 (fun z => u (planeCoordinates z)) := by
    simpa only [mul_one] using product_slope_lipschitz u hu
  have hareaReal (i : τ) : L^(-aw)*(T i).length*(T i).width ≤ (volume.prod volume).real (witness i) := by
    have h := ENNReal.toReal_mono (hWfinite i) (hsize i)
    have hn : 0 ≤ L^(-aw)*(T i).length*(T i).width :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hLpos.le _) (T i).length_pos.le) (T i).width_pos.le
    rw [ENNReal.toReal_ofReal hn] at h
    exact h
  obtain ⟨bad,hbad,hbadfin,hbadarea,hseparated⟩ := hLcount L hLcL
    (fun z => u (planeCoordinates z)) huProd τ widthScale timeScale hwidthLow hwidthHigh
    htimeLow htimeHigh T (fun i => w/(T i).length) witness htopLength hW hWfinite
    (fun i z hz => (hinside i z hz).2) hareaReal
    (fun i z hz => by simpa only [one_mul] using hprecision i z hz)
    (fun i => (div_pos hw (T i).length_pos).le) hwidthExact
  have hbadArea : (volume.prod volume) bad ≤
      ENNReal.ofReal ((1/2)*L^(-Hloss)*(volume.prod volume).real Fset) := by
    have hr := top_area_discard_numeric L s Hloss ratio ((volume.prod volume).real Fset)
      (∑ i, (T i).area) hLpos hratio.le measureReal_nonneg hNupper hS (hLarea L hLaL)
    have hb : (volume.prod volume).real bad ≤ (1/2)*L^(-Hloss)*(volume.prod volume).real Fset := by
      apply le_trans ?_ hr
      simpa only [SlopeBox.area,mul_comm] using hbadarea
    rw [← ENNReal.ofReal_toReal hbadfin]
    exact ENNReal.ofReal_le_ofReal hb
  have hpower : L^(-(Hloss+1)) ≤ (1/2)*L^(-Hloss) := by
    have hi : L⁻¹ ≤ (1/2:ℝ) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hL2
    calc
      _ = L^(-Hloss)*L⁻¹ := by rw [← Real.rpow_neg_one,← Real.rpow_add hLpos]; congr 1; ring
      _ ≤ L^(-Hloss)*(1/2) := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := mul_comm _ _
  let G := G₁ \ bad
  have hGG₁ : G ⊆ G₁ := sdiff_subset
  refine ⟨G,hG₁.diff hbad,hGG₁.trans hG₁F,?_,?_,?_,?_,?_,?_⟩
  · have hsub : Fset \ G ⊆ (Fset \ G₁) ∪ bad := by
      intro z hz
      by_cases hg : z ∈ G₁
      · exact Or.inr (by by_contra hn; exact hz.2 ⟨hg,hn⟩)
      · exact Or.inl ⟨hz.1,hg⟩
    calc
      _ ≤ (volume.prod volume) (Fset \ G₁)+(volume.prod volume) bad :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal ((1/2)*L^(-Hloss)*(volume.prod volume).real Fset)+
          ENNReal.ofReal ((1/2)*L^(-Hloss)*(volume.prod volume).real Fset) := add_le_add
        (harea₁.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpower measureReal_nonneg))) hbadArea
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · exact fun z hz => hcount₁ z (hGG₁ hz)
  · exact fun top lower upper hlu hup z hz => htop₁ top lower upper hlu hup z (hGG₁ hz)
  · exact hint₁.mono_set hGG₁
  · have herr := setIntegral_mono_set hint₁
      (Filter.Eventually.of_forall (fun z => norm_nonneg _))
      (Filter.Eventually.of_forall hGG₁)
    apply herr.trans (herror₁.trans ?_)
    have hh : L^(-(Hloss+1)) ≤ L^(-Hloss) := hpower.trans (by nlinarith [Real.rpow_nonneg hLpos.le (-Hloss)])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hratio.le) measureReal_nonneg
  · intro z hz rho hrho I hsig hprec hspan hsep
    exact hseparated z hz.2 rho hrho I hsig hprec hspan hsep

end LipschitzHilbert.PacketLatticeData

end

end OAI
