import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinaryTreeEstimate
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularFrozenEstimate
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularTreeSplit

namespace OAI

/-! The ordinary size-density tree bound with separate angular width
and spatial width. Constants are uniform in their ratio and in the
number of vertical frequency bins. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The separated portion of the original coefficient family, as in
Eq. (size) of the manuscript. -/
def angularSeparatedTreeEnergy (P : SourceLabeledLattice N κ Label Item) (cb w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) : ℝ :=
  ∑ j, ∑ l : P.labels j, ∑ v : Item j l,
    if cb*w/P.length j≤|P.rowSlope j l| then
      ‖c j l v‖^2*P.length j*P.width else 0

theorem exists_angular_ordinary_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B K : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (_hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → P.topLength≤tau → 0≤Lip → 0≤eta → 0≤sigma →
      1≤radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q : P.PacketIndex, 0∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ j l, P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ j l v, ‖c j l v‖≤sigma) →
      P.angularSeparatedTreeEnergy cb w c≤sigma^2*(P.topLength*P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k, selector j l k 0≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 →
        |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s, |s|≤w/P.length j →
        ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          P.ordinaryTreeConstant C B K Lip*sigma*eta*P.topLength*P.width := by
  obtain ⟨C,hC,hfrozen⟩ := exists_angular_frozen_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B K hcard horder hne c a b w tau radius Lip eta sigma cell grid
    hw htime hLip heta hsigma hwide hK hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  let d := P.frozenSelectorCoefficient c selector
  have hd (j : Fin N) (l : P.labels j) (v : Item j l) : ‖d j l v‖≤‖c j l v‖ :=
    P.frozenSelectorCoefficient_norm_le c selector (fun j l k => hselbound j l k 0) j l v
  have hlowerD (j : Fin N) (l : P.labels j) (v : Item j l) (hv : d j l v≠0) :
      cb*w/P.length j≤|P.rowSlope j l| := by
    by_contra hl
    apply hv
    ext k
    have hb : selector j l k 0=0 := by
      by_contra hk
      exact hl (hselaway j l k hk)
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
  obtain ⟨Omega,hOm,hEmpty,hcontains,hmass,hFI,hFB⟩ := hfrozen N κ Label Item P B hcard horder
    hne d a b w tau eta sigma cell grid hw htime heta hsigma hX hY href hspectrum hslope hbin hlowerD hsizeD
    E hE u hu hdensity
  have hY' (j : Fin N) (l : P.labels j) (v : Item j l) : |P.actualZ j l v-b|≤P.width :=
    (hY ⟨j,⟨l,v⟩⟩).trans (by linarith [P.width_pos])
  have hshort := P.short_tree_integrable_bound hne B hcard 0 cell grid w tau htime
    (by simpa only [zero_add] using hangle) (by omega) 1 sigma eta (by norm_num) hsigma heta
    (fun q => c q.1 q.2.1 q.2.2) (fun q => hc q.1 q.2.1 q.2.2)
    selector hsel hselbound hselsupport u hu E hE hdensity a b 32 (by norm_num) hX hY'
  have herr := P.angular_long_error_integrable_bound w hw hne K B (by omega) hcard a b radius Cb 1 Lip sigma eta
    (by norm_num) hLip hsigma heta hwide hK hX hY'
    (by simpa only [mul_div_assoc] using hslope)
    c hc selector hsel hselbound hselradius hselnear E hE u hu Omega hOm hEmpty hmass
  let S := E.indicator (P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u)
  let F := P.frozenTreeValueAtWidth w hne d E u Omega
  let R := P.longErrorTreeValueAtWidth w hne c selector E u Omega
  let V := fun z => P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z
  have hSI : Integrable S (volume.prod volume) := (integrable_indicator_iff hE).mpr hshort.1
  have hident : E.indicator V = fun z => S z+F z+R z :=
    P.angular_ordinary_tree_split_identity w hne c selector u cell grid hselsupport Omega hcontains E
  have hVI : Integrable (E.indicator V) (volume.prod volume) := by
    rw [hident]
    exact (hSI.add hFI).add herr.1
  have hnormS : (∫ z, ‖S z‖ ∂volume.prod volume)=
      ∫ z in E, ‖P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u z‖
        ∂volume.prod volume := by
    simp only [S,norm_indicator_eq_indicator_norm]
    exact integral_indicator hE
  have hSB : (∫ z, ‖S z‖ ∂volume.prod volume)≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*P.profileBound*1)*sigma*eta*P.topLength*P.width := by
    rw [hnormS]
    exact hshort.2
  refine ⟨(integrable_indicator_iff hE).mp hVI,?_⟩
  have hnormV : (∫ z, ‖E.indicator V z‖ ∂volume.prod volume)=
      ∫ z in E, ‖V z‖ ∂volume.prod volume := by
    simp only [norm_indicator_eq_indicator_norm]
    exact integral_indicator hE
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
