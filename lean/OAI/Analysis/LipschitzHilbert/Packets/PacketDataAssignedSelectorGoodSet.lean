import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSupportedAssignedConcentration
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedMaskRemoval
import OAI.Analysis.LipschitzHilbert.Estimates.PopularCountDiscard
import OAI.Analysis.LipschitzHilbert.Estimates.TopAreaDiscard

namespace OAI

/-! One fixed testing subset for the original selector coefficients.
The mask exponent is chosen before the larger counting dilation. Actual
concentration, smooth-count cutoff and mask removal all hold on this set. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_selector_mask_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aWeight aw p s Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haWeight : 0 ≤ aWeight) (haw : 0 ≤ aw) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn L0 : ℝ, aWeight < A ∧ 2 < A ∧ 0 < Cn ∧ 2 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      P.referenceEnvelopeConstant ≤ L^p → 6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
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
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
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
          L^(-Hloss)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨A,Lmask,haA,hA,hLmask,hmask⟩ := source_assigned_mask_removal hLL
    (2*p+8) Hloss aWeight aw s (D:ℝ) (by linarith) hHloss haw hs (by exact_mod_cast hD)
  obtain ⟨Cn,Lcount,hCn,hLcount,hcount⟩ := popular_top_count_discard hLL aw (A+2)
    (D:ℝ) s (Hloss+1) haw (by exact_mod_cast hD) hs (by linarith)
  obtain ⟨Lconc,hLconc⟩ := eventually_atTop.mp
    (eventually_assigned_top_selector_concentration_of_supported hVariation
      cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
      10 aWeight p Lip D K H J₀ (by norm_num) haWeight hp hLip)
  obtain ⟨Larea,hLarea⟩ := eventually_atTop.mp (eventually_top_area_factor s (Hloss+1))
  let L0 := max 2 (max Lmask (max Lcount (max Lconc Larea)))
  refine ⟨A,Cn,L0,haA,hA,hCn,le_max_left _ _,?_⟩
  intro L hL τ κ _ _ N Label Item _ P packets assigned hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscale hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE hcondition l r hslopes u lip hu hlength
    witness hW hdisj hinside hclose hsize hSpos ratio Fset hratio hFset hFfinite hFstrip hNupper hS
    Q orig a ha
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hLm : Lmask ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLc : Lcount ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLt : Lconc ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  have hLa : Larea ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  obtain ⟨bad,hbad,hbadArea,hpoint⟩ := hLconc L hLt τ κ N Label Item P packets assigned hP horder
    alt hAlt T oldSlope R cone w hw hcone hwide hfrequency hwidth hscale hX hZ
    angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
    b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
  let count := fun z => ∑ i, (T i).weight (L^(A+2)) (D:ℝ) z
  let tail := {z | ratio*L^Cn < count z}
  have htail : MeasurableSet tail := measurableSet_lt measurable_const
    (Finset.measurable_sum _ (fun i _ => ((T i).continuous_weight
      (Real.rpow_pos_of_pos hLpos _) _).measurable))
  let G := Fset \ (bad ∪ tail)
  have hG : MeasurableSet G := hFset.diff (hbad.union htail)
  have hGF : G ⊆ Fset := sdiff_subset
  have hgBad {z : ℝ×ℝ} (hz : z ∈ G) : z ∉ bad := fun hb => hz.2 (Or.inl hb)
  have hraw top lower upper (hlu : lower ≤ upper) (hup : upper ≤ N) z (hz : z ∈ G) yy
      (hy : |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width) :
      let V := ((Q top).withProfile (a top) (ha top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
        (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
    have hh := hpoint top lower upper hlu hup z (yy-(z.2-(T top).slope*z.1)) hy (hgBad hz)
    have he : z.2-(T top).slope*z.1+(yy-(z.2-(T top).slope*z.1)) = yy := by ring
    simpa only [he] using hh
  have hcountArea := hcount L hLc τ T l r hslopes u lip hu hlength witness hW hdisj
    hinside hclose hsize ratio Fset hratio hFstrip hS
  have hbArea : (volume.prod volume) bad ≤ ENNReal.ofReal
      (L^(-(Hloss+1))*(volume.prod volume).real Fset) := by
    apply hbadArea.trans
    apply ENNReal.ofReal_le_ofReal
    have hnum := top_area_discard_numeric L s (Hloss+1) ratio ((volume.prod volume).real Fset)
      (∑ i, (T i).area) hLpos hratio.le measureReal_nonneg hNupper hS (hLarea L hLa)
    have hn : 0 ≤ L^(-(Hloss+1))*(volume.prod volume).real Fset :=
      mul_nonneg (Real.rpow_nonneg hLpos.le _) measureReal_nonneg
    exact hnum.trans (by nlinarith)
  have harea : (volume.prod volume) (Fset\G) ≤
      ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) := by
    have hsub : Fset\G ⊆ bad ∪ (Fset ∩ tail) := by
      intro z hz
      have hh : z ∈ bad ∪ tail := by
        by_contra hn
        exact hz.2 ⟨hz.1,hn⟩
      rcases hh with hb | ht
      · exact Or.inl hb
      · exact Or.inr ⟨hz.1,ht⟩
    have hpower : 2*L^(-(Hloss+1)) ≤ L^(-Hloss) := by
      have hi : L⁻¹ ≤ (1/2:ℝ) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hL2
      rw [show L^(-(Hloss+1)) = L^(-Hloss)*L⁻¹ by
        rw [← Real.rpow_neg_one,← Real.rpow_add hLpos]; congr 1; ring]
      nlinarith [Real.rpow_nonneg hLpos.le (-Hloss)]
    calc
      _ ≤ (volume.prod volume) bad+(volume.prod volume) (Fset ∩ tail) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (L^(-(Hloss+1))*(volume.prod volume).real Fset)+
          ENNReal.ofReal (L^(-(Hloss+1))*(volume.prod volume).real Fset) := add_le_add hbArea hcountArea
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_right hpower (measureReal_nonneg (μ := volume.prod volume) (s := Fset))]
  refine ⟨G,hG,hGF,harea,?_,?_,?_⟩
  · intro z hz
    exact le_of_not_gt (fun ht => hz.2 (Or.inr ht))
  · exact hraw
  · apply hmask L hLm τ κ N Label Item P packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f hcondition l r hslopes u lip hu hlength
      witness hW hdisj hinside hclose hsize hSpos ratio Fset G hratio.le hFfinite hG hGF
      (fun z hz => hFstrip z (hGF hz)) hS
    intro z hz top
    have hh := hraw top 0 N (Nat.zero_le _) le_rfl z hz (z.2-(T top).slope*z.1)
      (by simpa only [sub_self,abs_zero] using (T top).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T top).width_pos.le (norm_nonneg _))).trans hh

end LipschitzHilbert.PacketLatticeData

end

end OAI
