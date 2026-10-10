import OAI.Analysis.LipschitzHilbert.Packets.PacketDataTopEstimate
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDeletionForest
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeForestIntegral
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeOnePacket

namespace OAI

/-! Apply the actual tree estimate to every full deletion tree in one
signed stopping run, and sum with its recorded top-area budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_deletion_forest_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hcbquarter : cb≤1/4) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau radius Lip eta sigma F dilation threshold epsilon : ℝ)
      (negative : Bool) (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun negative w cb tau threshold epsilon dilation cell grid c initial tops remaining →
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
      (∀ p∈P.sizeDeletionRecords w dilation cell grid initial tops, ∀ q∈p.2, ∀ k,
        selector q.1 q.2.1 k p.1.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ p∈P.sizeDeletionRecords w dilation cell grid initial tops, ∀ j l k s,
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
            sigma*eta*(tops.map SlopeBox.area).sum := by
  obtain ⟨C,hC,hTree⟩ := exists_selected_top_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder c cell grid w tau radius Lip eta sigma F
    dilation threshold epsilon negative initial remaining tops hRun hDil hD hw hF hwW hfreq htime
    hLip heta hsigma hwide hK hlocal hrow hspectrum hbin hsize selector hsel hselbound haway
    hsupport hradius hnear E hE u hu hdensity
  let forest := P.sizeDeletionRecords w dilation cell grid initial tops
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let B := (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta
  have hp (p : SlopeBox × Finset P.PacketIndex) (hp : p∈forest) :
      IntegrableOn (fun z => ∑ q∈p.2, V q z) E (volume.prod volume) ∧
      (∫ z in E, ‖∑ q∈p.2, V q z‖ ∂volume.prod volume)≤B*p.1.area := by
    have hsub := P.sizeDeletionRecords_subset w dilation cell grid initial tops p hp
    obtain ⟨hwidth,hpt,hgeom⟩ := hRun.deletion_forest_geometry p hp
    have hn := hRun.deletion_forest_nonempty hDil p hp
    have h := hTree N κ Label Item P M R K D hR horder p.2 initial hsub hn c p.1
      dilation w tau radius Lip eta sigma cell grid hwidth hD hw F hF hwW hfreq
      (hpt.trans htime) hpt (fun q hq => (hgeom q hq).1) hLip heta hsigma hwide hK hlocal
      (fun q hq => (hgeom q hq).2.1) (fun q hq => (hgeom q hq).2.2)
      (fun q hq => hrow q (hsub hq)) (fun q hq => hspectrum q (hsub hq))
      (fun q hq => hbin q (hsub hq))
      (fun q hq => P.coefficient_le_of_size_tests w cb tau sigma hw hcbquarter hsigma
        cell grid c initial hsize q (hsub hq) ((hgeom q hq).1.trans hpt)) hsize
      selector hsel hselbound (haway p hp) hsupport hradius (hnear p hp)
      E hE u hu (fun q hq => hdensity q (hsub hq))
    refine ⟨h.1,h.2.trans_eq ?_⟩
    dsimp only [B]
    ring
  have hforest := tree_list_integral_bound forest (fun p z => ∑ q∈p.2, V q z)
    (fun p => B*p.1.area) E hp
  have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=
      (forest.map (fun p => ∑ q∈p.2, V q z)).sum := by
    have h := hRun.deletion_forest_sum (fun q => V q z)
    rw [h]
    abel
  dsimp only
  have hefun : (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z))=
      fun z => (forest.map (fun p => ∑ q∈p.2, V q z)).sum := funext heval
  change IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E _ ∧
    (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
      B*(tops.map SlopeBox.area).sum
  rw [hefun]
  simp only [heval]
  refine ⟨hforest.1,hforest.2.trans_eq ?_⟩
  rw [List.sum_map_mul_left]
  have harea : (forest.map (fun p => p.1.area)).sum=(tops.map SlopeBox.area).sum :=
    SizeStoppingRun.deletion_forest_area
  rw [harea]

end LipschitzHilbert.PacketLatticeData

end

end OAI
