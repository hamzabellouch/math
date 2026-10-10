import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularOrdinaryTree
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedFrozenEstimate
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedTreeSplit
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMasks

namespace OAI

/-! Ordinary trees in arbitrary reference coordinates. Original angular
cells and density tests are kept through the measure-preserving shear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem exists_reference_ordinary_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B K : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (_hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → P.topLength≤tau → 0≤Lip → 0≤eta → 0≤sigma →
      1≤radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q : P.PacketIndex, t∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ j l, t+P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ j l v, ‖c j l v‖≤sigma) →
      P.angularSeparatedTreeEnergy cb w c≤sigma^2*(P.topLength*P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k, selector j l k t≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 →
        |s-(t+P.rowSlope j l)|≤radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q, P.ordinaryDensity t cell grid w tau E u q≤eta) →
      let F := fun z => P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u z)) z
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          P.ordinaryTreeConstant C B K Lip*sigma*eta*P.topLength*P.width := by
  obtain ⟨C,hC,hfrozen⟩ := exists_masked_frozen_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B K hcard horder hne c t a b w tau radius Lip eta sigma cell grid
    hw htime hLip heta hsigma hwide hK hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  let E0 := (slopeShear t) ⁻¹' E
  let u0 := fun z => u (slopeShear t z)-t
  let sel := fun j l k s => selector j l k (s+t)
  have hE0 : MeasurableSet E0 := hE.preimage (slopeShear t).measurable
  have hu0 : Measurable u0 := (hu.comp (slopeShear t).measurable).sub_const t
  have hsel0 : ∀ j l k, Measurable (sel j l k) := fun j l k =>
    (hsel j l k).comp (measurable_id.add_const t)
  let d := P.frozenSelectorCoefficient c sel
  have hd (j : Fin N) (l : P.labels j) (v : Item j l) : ‖d j l v‖≤‖c j l v‖ :=
    P.frozenSelectorCoefficient_norm_le c sel (fun j l k => by
      simpa only [sel,zero_add] using hselbound j l k t) j l v
  have hlowerD (j : Fin N) (l : P.labels j) (v : Item j l) (hv : d j l v≠0) :
      cb*w/P.length j≤|P.rowSlope j l| := by
    by_contra hl
    apply hv
    ext k
    have hb : sel j l k 0=0 := by
      by_contra hk
      exact hl (hselaway j l k (by simpa only [sel,zero_add] using hk))
    simp only [d,frozenSelectorCoefficient,WithLp.ofLp_toLp,hb,mul_zero,
      WithLp.ofLp_zero,Pi.zero_apply]
  have hsizeD : (∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖d j l v‖^2*P.length j*P.width)≤
      sigma^2*(P.topLength*P.width) := by
    apply le_trans _ hsize
    unfold angularSeparatedTreeEnergy
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro v _
    by_cases hsep : cb*w/P.length j≤|P.rowSlope j l|
    · rw [ite_eq_left hsep]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd j l v) 2)
          (P.length_pos j).le) P.width_pos.le
    · have hz : d j l v=0 := by
        by_contra hn
        exact hsep (hlowerD j l v hn)
      simp only [ite_eq_right hsep,hz,norm_zero,zero_pow (by decide : 2≠0),zero_mul,le_refl]
  obtain ⟨Omega,hOm,hEmpty,hcontains,hmass⟩ := P.exists_reference_whitney_masks t b w
    cell grid tau htime hY href E hE u hu eta heta hdensity
  have hspectrum0 := P.reference_packet_spectrum t w cStar cEta CEta hspectrum
  have hbin0 := P.reference_packet_bin t Cv hbin
  have hsizeD' := hsizeD
  have hfrozen := hfrozen N κ Label Item P B hcard horder hne d a b w eta sigma
    hw heta hsigma hX hY hspectrum0 hslope hbin0 hlowerD hsizeD' E0 hE0 u0 hu0
    Omega hOm hEmpty hmass
  have hFI := hfrozen.1
  have hFB := hfrozen.2
  have hY' (j : Fin N) (l : P.labels j) (v : Item j l) : |P.actualZ j l v-b|≤P.width :=
    (hY ⟨j,⟨l,v⟩⟩).trans (by linarith [P.width_pos])
  have hshort := P.short_tree_integrable_bound hne B hcard t cell grid w tau htime
    hangle (by omega) 1 sigma eta (by norm_num) hsigma heta
    (fun q => c q.1 q.2.1 q.2.2) (fun q => hc q.1 q.2.1 q.2.2)
    selector hsel hselbound hselsupport u hu E hE hdensity a b 32 (by norm_num) hX hY'
  let S0 := P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) sel u0
  let St := P.shortTreeValue hne t 32 (fun q => c q.1 q.2.1 q.2.2) selector u
  have hSeq : S0=(fun z => St (slopeShear t z)) := by
    funext z
    exact P.shortTreeValue_slopeShear hne t 32 (fun q => c q.1 q.2.1 q.2.2) selector u z
  have hSI0 : IntegrableOn S0 E0 (volume.prod volume) := by
    rw [hSeq]
    exact (integrableOn_slopeShear_iff t E hE St).mpr hshort.1
  have hSbound : (∫ z in E0, ‖S0 z‖ ∂volume.prod volume)=
      ∫ z in E, ‖St z‖ ∂volume.prod volume := by
    rw [hSeq]
    exact integralOn_slopeShear t E hE (fun z => ‖St z‖)
  have hselradius0 : ∀ j l k s, sel j l k s≠0 →
      |s-P.rowSlope j l|≤radius*(w/P.length j) := by
    intro j l k s hs
    have he : s+t-(t+P.rowSlope j l)=s-P.rowSlope j l := by ring
    simpa only [he] using hselradius j l k (s+t) hs
  have hselnear0 : ∀ j l k s, |s|≤w/P.length j →
      ‖sel j l k s-sel j l k 0‖≤Lip*(|s|/(w/P.length j)) := by
    intro j l k s hs
    simpa only [sel,add_sub_cancel_right,zero_add] using hselnear j l k (s+t)
      (by simpa only [add_sub_cancel_right] using hs)
  have herr := P.angular_long_error_integrable_bound w hw hne K B (by omega) hcard a b radius Cb 1 Lip sigma eta
    (by norm_num) hLip hsigma heta hwide hK hX hY'
    (by simpa only [mul_div_assoc] using hslope)
    c hc sel hsel0 (fun j l k s => hselbound j l k (s+t)) hselradius0 hselnear0 E0 hE0 u0 hu0 Omega hOm hEmpty hmass
  let S := E0.indicator S0
  let F := P.frozenTreeValueAtWidth w hne d E0 u0 Omega
  let R := P.longErrorTreeValueAtWidth w hne c sel E0 u0 Omega
  let V := fun z => P.physicalTreeSelectorValue 0 c (fun j l k => sel j l k (u0 z)) z
  let Vt := fun z => P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u z)) z
  have hVeq : V=(fun z => Vt (slopeShear t z)) := by
    funext z
    exact P.physicalTreeSelectorValue_slopeShear t c selector u z
  have hSI : Integrable S (volume.prod volume) := (integrable_indicator_iff hE0).mpr hSI0
  have hident : E0.indicator V = fun z => S z+F z+R z :=
    P.masked_ordinary_tree_split_identity w hne c sel u0 Omega
      (fun i q hq k s hs => hcontains i q hq (hselsupport q.1 q.2.1 k (s+t) hs)) E0
  have hVI : Integrable (E0.indicator V) (volume.prod volume) := by
    rw [hident]
    exact (hSI.add hFI).add herr.1
  have hnormS : (∫ z, ‖S z‖ ∂volume.prod volume)=
      ∫ z in E, ‖St z‖
        ∂volume.prod volume := by
    simp only [S,norm_indicator_eq_indicator_norm]
    exact (integral_indicator hE0).trans hSbound
  have hSB : (∫ z, ‖S z‖ ∂volume.prod volume)≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*P.profileBound*1)*sigma*eta*P.topLength*P.width := by
    rw [hnormS]
    exact hshort.2
  have hVtI : IntegrableOn Vt E (volume.prod volume) := by
    apply (integrableOn_slopeShear_iff t E hE Vt).mp
    rw [←hVeq]
    exact (integrable_indicator_iff hE0).mp hVI
  refine ⟨hVtI,?_⟩
  have hnormV : (∫ z, ‖E0.indicator V z‖ ∂volume.prod volume)=
      ∫ z in E, ‖Vt z‖ ∂volume.prod volume := by
    simp only [norm_indicator_eq_indicator_norm]
    apply (integral_indicator hE0).trans
    rw [hVeq]
    exact integralOn_slopeShear t E hE (fun z => ‖Vt z‖)
  rw [←hnormV,hident]
  calc
    _ ≤ ∫ z, ‖S z‖+‖F z‖+‖R z‖ ∂volume.prod volume := by
      apply integral_mono ((hSI.add hFI).add herr.1).norm ((hSI.norm.add hFI.norm).add herr.1.norm)
      intro z
      change ‖S z+F z+R z‖≤‖S z‖+‖F z‖+‖R z‖
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (∫ z, ‖S z‖ ∂volume.prod volume)+(∫ z, ‖F z‖ ∂volume.prod volume)+
        (∫ z, ‖R z‖ ∂volume.prod volume) := by
      have hiSF : Integrable (fun z => ‖S z‖+‖F z‖) (volume.prod volume) := hSI.norm.add hFI.norm
      have hiR : Integrable (fun z => ‖R z‖) (volume.prod volume) := herr.1.norm
      have hiS : Integrable (fun z => ‖S z‖) (volume.prod volume) := hSI.norm
      have hiF : Integrable (fun z => ‖F z‖) (volume.prod volume) := hFI.norm
      rw [integral_add hiSF hiR,integral_add hiS hiF]
    _ ≤ _ := add_le_add (add_le_add hSB hFB) herr.2
    _ = _ := by
      simp only [ordinaryTreeConstant,add_mul,mul_one]
      simp only [mul_assoc,mul_comm,mul_left_comm]


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
