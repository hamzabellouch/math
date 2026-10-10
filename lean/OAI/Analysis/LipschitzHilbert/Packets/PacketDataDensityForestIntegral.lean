import OAI.Analysis.LipschitzHilbert.Packets.PacketDataOrdinaryDensityForest
import OAI.Analysis.LipschitzHilbert.Packets.SourceAssignedPacketSum
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataTopEstimate
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeOnePacket

namespace OAI

/-! Integrate all trees in the actual sharp density forest. Coefficients
are controlled by the original size tests, and the forest area is supplied
by disjoint witnesses rather than by an additional analytic assumption. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_density_forest_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hcbQuarter : cb≤1/4)
    (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (packets initial : Finset P.PacketIndex), packets⊆initial →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau eta density sigma radius Lip F : ℝ)
      (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
      (forest : OrdinaryDensityForest P packets cell grid w tau eta E u),
      5*densityRadius eta≤D → 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤density → 0≤sigma → 1≤radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈packets, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈packets, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈packets, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤sigma^2*T.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ i, ∀ q∈assignedPacketSet packets forest.assigned i, ∀ k,
        selector q.1 q.2.1 k (forest.top i).slope≠0 →
          cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-(forest.top i).slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ i, ∀ j l k s, |s-(forest.top i).slope|≤w/P.length j →
        ‖selector j l k s-selector j l k (forest.top i).slope‖≤
          Lip*(|s-(forest.top i).slope|/(w/P.length j))) →
      MeasurableSet E → Measurable u →
      (∀ q∈packets, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn (fun z => ∑ q∈packets, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈packets, V q z‖ ∂volume.prod volume)≤
          ((((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*density)*
            (2*(volume.prod volume).real E/eta) := by
  obtain ⟨C,hC,hTree⟩ := exists_selected_top_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder packets initial hsub c cell grid
    w tau eta density sigma radius Lip F E u forest hD hw hW hF hfreq htime
    hLip hdensity hsigma hwide hK hlocal hrow hspectrum hbin hsize
    selector hsel hbound haway hsupport hradius hnear hE hu hden
  classical
  let part := assignedPacketSet packets forest.assigned
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let B := (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*density
  have hCtree : 0≤P.referenceTreeConstant C ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have hp := P.profileBound_pos
    dsimp [referenceTreeConstant,referenceEnvelopeConstant]
    positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  have hpart (i : forest.keepers) :
      IntegrableOn (fun z => ∑ q∈part i, V q z) E (volume.prod volume) ∧
      (∫ z in E, ‖∑ q∈part i, V q z‖ ∂volume.prod volume)≤B*(forest.top i).area := by
    have hsubset : part i⊆packets := assignedPacketSet_subset _ _ _
    have hgeom (q : P.PacketIndex) (hq : q∈part i) :
        P.length q.1≤(forest.top i).length ∧
        (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈
          densitySpatialBox (forest.top i) (5*densityRadius eta) ∧
        (forest.top i).slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) := by
      obtain ⟨hqp,ha⟩ := mem_assignedPacketSet packets forest.assigned i q hq
      simpa only [ha] using
        And.intro (forest.length_le ⟨q,hqp⟩) (And.intro (forest.center ⟨q,hqp⟩) (forest.direction ⟨q,hqp⟩))
    by_cases hn : (part i).Nonempty
    · have h := hTree N κ Label Item P M R K D hR horder (part i) initial
        (hsubset.trans hsub) hn c (forest.top i) (5*densityRadius eta)
        w tau radius Lip density sigma cell grid (forest.width i) hD hw F hF hW hfreq
        ((forest.short i).trans htime) (forest.short i) (fun q hq => (hgeom q hq).1)
        hLip hdensity hsigma hwide hK hlocal
        (fun q hq => (hgeom q hq).2.1) (fun q hq => (hgeom q hq).2.2)
        (fun q hq => hrow q (hsubset hq)) (fun q hq => hspectrum q (hsubset hq))
        (fun q hq => hbin q (hsubset hq))
        (fun q hq => P.coefficient_le_of_size_tests w cb tau sigma hw hcbQuarter hsigma
          cell grid c initial hsize q (hsub (hsubset hq)) ((hgeom q hq).1.trans (forest.short i)))
        hsize selector hsel hbound (haway i) hsupport hradius (hnear i) E hE u hu
        (fun q hq => hden q (hsubset hq))
      refine ⟨h.1,h.2.trans_eq ?_⟩
      dsimp only [B]
      ring
    · have he : part i=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he,Finset.sum_empty,norm_zero,integral_zero]
      exact ⟨integrableOn_zero,mul_nonneg hB (forest.top i).area_pos.le⟩
  have heval (z : ℝ×ℝ) : (∑ i : forest.keepers, ∑ q∈part i, V q z)=∑ q∈packets, V q z :=
    sum_assignedPacketSets packets forest.assigned (fun q => V q z)
  have hI := integrable_finsetSum Finset.univ (fun i _ => (hpart i).1)
  have hefun : (fun z => ∑ i : forest.keepers, ∑ q∈part i, V q z)=
      fun z => ∑ q∈packets, V q z := funext heval
  refine ⟨?_,?_⟩
  · change IntegrableOn (fun z => ∑ q∈packets, V q z) E (volume.prod volume)
    rw [hefun] at hI
    exact hI
  · change (∫ z in E, ‖∑ q∈packets, V q z‖ ∂volume.prod volume)≤B*(2*(volume.prod volume).real E/eta)
    calc
      _ = ∫ z in E, ‖∑ i : forest.keepers, ∑ q∈part i, V q z‖ ∂volume.prod volume := by
        simp only [heval]
      _ ≤ ∫ z in E, ∑ i : forest.keepers, ‖∑ q∈part i, V q z‖ ∂volume.prod volume :=
        integral_mono hI.norm (integrable_finsetSum Finset.univ (fun i _ => (hpart i).1.norm))
          (fun z => norm_sum_le _ _)
      _ = ∑ i : forest.keepers, ∫ z in E, ‖∑ q∈part i, V q z‖ ∂volume.prod volume :=
        integral_finsetSum _ (fun i _ => (hpart i).1.norm)
      _ ≤ ∑ i : forest.keepers, B*(forest.top i).area :=
        Finset.sum_le_sum (fun i _ => (hpart i).2)
      _ = B*∑ i : forest.keepers, (forest.top i).area := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left forest.area hB

end LipschitzHilbert.PacketLatticeData

end

end OAI
