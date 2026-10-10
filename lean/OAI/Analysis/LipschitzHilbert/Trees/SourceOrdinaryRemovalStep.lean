import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityRemovalIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceSizeRemovalIntegral

namespace OAI

/-! One actual ordinary-model step: remove high density, then lower
size by both signed selections. The two removed packet sums telescope. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_ordinary_removal_step (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M Q gap packGap R K D0 : ℕ),
    ∀ (w tau sigma D epsilon A margin F radius Lip eta density : ℝ),
      0<sigma → 0≤D → 0<epsilon → 0<eta → 0≤density → 0≤Lip →
      0<w → w≤P.width → 0≤F → (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4 →
      (1+cb/4)/(2:ℝ)^packGap≤cb/4 → cb/2≤margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (1:ℝ)≤R → 207≤P.order → A≤D0 → tau≤P.topLength →
      1≤radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ), c=P.ordinaryCoefficient g →
    ∀ (initial : Finset P.PacketIndex),
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, epsilon≤cb*(w/P.length q.1)/4) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ s∈initial, ∀ k xi et,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-margin*(w/P.length s.1)) (-xi/et+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
      (∀ q∈initial, ∀ k xi et,
        planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
    ∃ remaining : Finset P.PacketIndex, remaining⊆initial ∧
      (∀ q∈remaining, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T≤sigma^2*T.area) ∧
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
        (625*densityRadiusConstant^2)*P.ordinaryTreeConstant CD ((2*R+1)*M) K Lip*
          (D*sigma)*density*(1+eta^(-(1/20:ℝ)))*(2*(volume.prod volume).real E/eta) +
        (((4*D0+1)^2:ℕ):ℝ)*P.ordinaryTreeConstant CT ((2*R+1)*M) K Lip*(D*sigma)*density*
          ((4*(selectedNearConstant P gap M Q+
            2*Real.sqrt (2*selectedFarConstant P cb D CS packGap M Q))/sigma^2)*
              ∫ z, ‖g z‖^2 ∂volume.prod volume) := by
  obtain ⟨CD,hCD,hDensity⟩ := exists_density_removal_integral hL cStar cEta CEta cb Cv
    hcStar hcEta hCEta hCv hcb.le hcbQuarter hspectral
  obtain ⟨CS,CT,hCS,hCT,hSize⟩ := exists_two_sided_size_removal_integral hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P M Q gap packGap R K D0 w tau sigma D epsilon A margin F
    radius Lip eta density hsigma hD hepsilon heta hdensity hLip hw hW hF hfreq
    hgap hpack hmargin hA hQ hQnear hR horder hD0 htime hwide hK hlocal
    cell grid g hg c hc initial hsize hrow heps hspectrum hmarginSpec hbin
    selector hsel hbound haway hsupport hradius hnear E hE hEfin u hu hden
  let removed := initial.filter (fun q => eta<P.ordinaryDensity 0 cell grid w tau E u q)
  let middle := initial\removed
  have hDensityStep := hDensity N κ Label Item P M R K hR horder initial c cell grid
    w tau eta density (D*sigma) radius Lip F heta hw hW hF hfreq htime hLip hdensity
    (mul_nonneg hD hsigma.le) hwide hK hlocal hrow
    (fun q _ k xi et hn => hspectrum q.1 q.2.1 q.2.2 k xi et hn) hbin hsize
    selector hsel hbound haway hsupport hradius hnear E hE hEfin u hu hden
  change middle⊆initial ∧
    (∀ q∈middle, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧ _ at hDensityStep
  have hm : middle⊆initial := hDensityStep.1
  have hmSize (T : SlopeBox) (hwT : T.width=P.width) (htT : T.length≤tau) :
      P.unsignedSizeTestEnergy w cb cell grid c middle T≤(D*sigma)^2*T.area :=
    (P.unsignedSizeTestEnergy_mono w cb cell grid c hm T).trans (hsize T hwT htT)
  obtain ⟨positive,intermediate,negative,remaining,hpos,hneg,hr,hsmall,harea,hSizeIntegral⟩ :=
    hSize N κ Label Item P M Q gap packGap w tau sigma D epsilon A margin F
      hsigma hD hepsilon hw hW hF hfreq hgap hpack hmargin hA hQ hQnear hlocal
      cell grid g hg c hc middle hmSize (fun q hq => hrow q (hm hq))
      (fun q hq => heps q (hm hq)) hspectrum (fun q hq => hmarginSpec q (hm hq))
      R K D0 hR horder hD0 htime (fun q hq => hbin q (hm hq))
  have hRemoved := hSizeIntegral radius Lip density hLip hdensity hwide hK selector hsel hbound
    (fun p _ q _ k hn => haway q.1 q.2.1 k p.1.slope hn) hsupport hradius
    (fun p _ j l k s hs => hnear j l k s p.1.slope hs) E hE u hu
    (fun q hq => hden q (hm hq))
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  have heq (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=
      ((∑ q∈initial, V q z)-(∑ q∈middle, V q z))+
      ((∑ q∈middle, V q z)-(∑ q∈remaining, V q z)) := by abel
  have hI := (hDensityStep.2.2.1.add hRemoved.1).congr
    (Filter.Eventually.of_forall fun z => (heq z).symm)
  refine ⟨remaining,hr.trans hm,fun q hq => hDensityStep.2.1 q (hr hq),hsmall,hI,?_⟩
  calc
    _ ≤ ∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈middle, V q z)‖+
        ‖(∑ q∈middle, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume :=
      integral_mono hI.norm (hDensityStep.2.2.1.norm.add hRemoved.1.norm)
        (fun z => by rw [heq]; exact norm_add_le _ _)
    _ = (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈middle, V q z)‖ ∂volume.prod volume)+
        (∫ z in E, ‖(∑ q∈middle, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume) :=
      integral_add hDensityStep.2.2.1.norm hRemoved.1.norm
    _ ≤ _ := add_le_add hDensityStep.2.2.2 hRemoved.2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
