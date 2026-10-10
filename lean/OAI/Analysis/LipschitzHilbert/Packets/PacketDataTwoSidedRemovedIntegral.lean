import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDeletionTreeEstimate

namespace OAI

/-! Apply the actual tree estimate to every full deletion tree in one
signed stopping run, and sum with its recorded top-area budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_two_sided_removed_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hcbquarter : cb≤1/4) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau radius Lip eta sigma F dilation threshold epsilon : ℝ)
      (initial middle remaining : Finset P.PacketIndex) (positive negative : List SlopeBox),
      P.SizeStoppingRun false w cb tau threshold epsilon dilation cell grid c initial positive middle →
      P.SizeStoppingRun true w cb tau threshold epsilon dilation cell grid c middle negative remaining →
      1/2≤dilation → dilation≤D → 0<w → 0≤F → w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤eta → 0≤sigma → 1≤radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial U≤sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ p∈(P.sizeDeletionRecords w dilation cell grid initial positive ++
        P.sizeDeletionRecords w dilation cell grid middle negative), ∀ q∈p.2, ∀ k,
        selector q.1 q.2.1 k p.1.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ p∈(P.sizeDeletionRecords w dilation cell grid initial positive ++
        P.sizeDeletionRecords w dilation cell grid middle negative), ∀ j l k s,
        |s-p.1.slope|≤w/P.length j →
        ‖selector j l k s-selector j l k p.1.slope‖≤Lip*(|s-p.1.slope|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      let H := fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)
      IntegrableOn H E (volume.prod volume) ∧
        (∫ z in E, ‖H z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*((positive.map SlopeBox.area).sum+(negative.map SlopeBox.area).sum) := by
  obtain ⟨C,hC,hForest⟩ := exists_deletion_forest_integral hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbquarter hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder c cell grid w tau radius Lip eta sigma F
    dilation threshold epsilon initial middle remaining positive negative hpos hneg hDil hD hw hF hwW hfreq htime
    hLip heta hsigma hwide hK hlocal hrow hspectrum hbin hsize selector hsel hselbound haway
    hsupport hradius hnear E hE u hu hdensity
  have hmid := hpos.remaining_subset
  have hp := hForest N κ Label Item P M R K D hR horder c cell grid
    w tau radius Lip eta sigma F dilation threshold epsilon false initial middle positive hpos
    hDil hD hw hF hwW hfreq htime hLip heta hsigma hwide hK hlocal hrow hspectrum hbin hsize
    selector hsel hselbound (fun p hp => haway p (List.mem_append_left _ hp)) hsupport hradius
    (fun p hp => hnear p (List.mem_append_left _ hp)) E hE u hu hdensity
  have hn := hForest N κ Label Item P M R K D hR horder c cell grid
    w tau radius Lip eta sigma F dilation threshold epsilon true middle remaining negative hneg
    hDil hD hw hF hwW hfreq htime hLip heta hsigma hwide hK hlocal
    (fun q hq => hrow q (hmid hq)) (fun q hq => hspectrum q (hmid hq))
    (fun q hq => hbin q (hmid hq))
    (fun U hw ht => (P.unsignedSizeTestEnergy_mono w cb cell grid c hmid U).trans (hsize U hw ht))
    selector hsel hselbound (fun p hp => haway p (List.mem_append_right _ hp)) hsupport hradius
    (fun p hp => hnear p (List.mem_append_right _ hp)) E hE u hu
    (fun q hq => hdensity q (hmid hq))
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let A := fun z => (∑ q∈initial, V q z)-(∑ q∈middle, V q z)
  let B := fun z => (∑ q∈middle, V q z)-(∑ q∈remaining, V q z)
  have hAI : IntegrableOn A E (volume.prod volume) := hp.1
  have hBI : IntegrableOn B E (volume.prod volume) := hn.1
  have heq : (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z))=
      fun z => A z+B z := by
    funext z
    dsimp [A,B]
    abel
  have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=A z+B z := congrFun heq z
  dsimp only
  change IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E _ ∧
    (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤_
  rw [heq]
  simp only [heval]
  refine ⟨hAI.add hBI,?_⟩
  calc
    _ ≤ ∫ z in E, ‖A z‖+‖B z‖ ∂volume.prod volume :=
      integral_mono (hAI.add hBI).norm (hAI.norm.add hBI.norm) (fun z => norm_add_le _ _)
    _ = (∫ z in E, ‖A z‖ ∂volume.prod volume)+(∫ z in E, ‖B z‖ ∂volume.prod volume) :=
      integral_add hAI.norm hBI.norm
    _ ≤ _ := add_le_add hp.2 hn.2
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
