import OAI.Analysis.LipschitzHilbert.Trees.SourceTwoSidedSizeArea
import OAI.Analysis.LipschitzHilbert.Trees.SourceTwoSidedRemovedIntegral

namespace OAI

/-! The ordinary two-sided size-selection lemma with an L2 top-area
bound, derived from the actual packet geometry and scalar variation input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_two_sided_size_removal_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hspectral : cStar<cEta*cb) :
    ∃ C CT : ℝ, 0<C ∧ 0<CT ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0<sigma → 0≤D → 0<epsilon →
      0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4 →
      (1+cb/4)/(2:ℝ)^packGap≤cb/4 → cb/2≤margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : MemLp g 2 (volume.prod volume))
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (_hc : c=P.ordinaryCoefficient g)
      (initial : Finset P.PacketIndex),
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ q∈initial,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, epsilon≤cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈initial, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    ∀ (R K D0 : ℕ), (1:ℝ)≤R → 207≤P.order → A≤D0 → tau≤P.topLength →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
    ∃ positive middle negative remaining,
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial positive middle ∧
      P.SizeStoppingRun true w cb tau sigma epsilon A cell grid c middle negative remaining ∧
      remaining⊆initial ∧
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T≤sigma^2*T.area) ∧
      (positive.map SlopeBox.area).sum+(negative.map SlopeBox.area).sum≤
        (4*(selectedNearConstant P gap M Q+
          2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
            ∫ z, ‖g z‖^2 ∂volume.prod volume ∧
    ∀ (radius Lip eta : ℝ), 0≤Lip → 0≤eta → 1≤radius+1 → radius+1≤(2:ℝ)^K →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ p∈(P.sizeDeletionRecords w A cell grid initial positive ++
        P.sizeDeletionRecords w A cell grid middle negative), ∀ q∈p.2, ∀ k,
        selector q.1 q.2.1 k p.1.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ p∈(P.sizeDeletionRecords w A cell grid initial positive ++
        P.sizeDeletionRecords w A cell grid middle negative), ∀ j l k s,
        |s-p.1.slope|≤w/P.length j →
        ‖selector j l k s-selector j l k p.1.slope‖≤Lip*(|s-p.1.slope|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      let H := fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)
      IntegrableOn H E (volume.prod volume) ∧
        (∫ z in E, ‖H z‖ ∂volume.prod volume)≤
          ((((4*D0+1)^2:ℕ):ℝ)*P.ordinaryTreeConstant CT ((2*R+1)*M) K Lip*(D*sigma)*eta)*
            ((4*(selectedNearConstant P gap M Q+
              2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
              ∫ z, ‖g z‖^2 ∂volume.prod volume) := by
  obtain ⟨C,hC,hSelect⟩ := exists_two_sided_size_selection_with_area hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb (by linarith) hspectral
  obtain ⟨CT,hCT,hIntegral⟩ := exists_two_sided_removed_integral hL cStar cEta CEta cb Cv
    hcStar hcEta hCEta hCv hcb.le hcbQuarter hspectral
  refine ⟨C,CT,hC,hCT,?_⟩
  intro N κ Label Item _ _ P M Q gap packGap w tau sigma D epsilon A margin F
    hsigma hD hepsilonPos hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal
    cell grid g hg c hc initial hsize hrow hepsilon hspectrum hmargin R K D0 hR horder hD0 htime hbin
  obtain ⟨positive,middle,negative,remaining,hpos,hneg,hr,hsmall,harea⟩ :=
    hSelect N κ Label Item P M Q gap packGap w tau sigma D epsilon A margin F
      hsigma hD hcbQuarter hepsilonPos hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear
      hlocal cell grid g hg c hc initial hsize hrow hepsilon hspectrum hmargin
  refine ⟨positive,middle,negative,remaining,hpos,hneg,hr,hsmall,harea,?_⟩
  intro radius Lip eta hLip heta hwide hK selector hsel hbound haway hsupport hradius hnear
    E hE u hu hdensity
  have h := hIntegral N κ Label Item P M R K D0 hR horder c cell grid w tau radius Lip eta
    (D*sigma) F A sigma epsilon initial middle remaining positive negative hpos hneg
    (by linarith) hD0 hw hF hwW hfreq htime hLip heta (mul_nonneg hD hsigma.le)
    hwide hK hlocal hrow (fun q _ k xi et hn => hspectrum q.1 q.2.1 q.2.2 k xi et hn)
    hbin hsize selector hsel hbound haway hsupport hradius hnear E hE u hu hdensity
  refine ⟨h.1,h.2.trans ?_⟩
  have hTreeNonneg : 0≤P.ordinaryTreeConstant CT ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have ha := P.absoluteConstant_pos
    have hp := P.profileBound_pos
    dsimp [ordinaryTreeConstant]
    positivity
  exact mul_le_mul_of_nonneg_left harea (by positivity)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
