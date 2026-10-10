import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSpatialTree
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDropTreeTransport
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataEnclosingScale

namespace OAI

/-! The ordinary tree estimate for an actual selected packet set. Local
angular multiplicity supplies the row count; empty ambient rows disappear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_rooted_selected_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      Cb≤R → 207≤P.order → ∀ (Q A : Finset P.PacketIndex), Q⊆A → Q.Nonempty →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (L t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → ∀ (F : ℝ), 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → L≤P.topLength → L≤tau →
      (∀ q∈Q, P.length q.1≤L) → 0≤Lip → 0≤eta → 0≤sigma →
      1≤radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤(D:ℝ)*L) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤(D:ℝ)*P.width) →
      (∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖≤sigma) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c A U≤sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ q∈Q, ∀ k, selector q.1 q.2.1 k t≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈Q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*L*P.width) := by
  obtain ⟨C,hC,hTree⟩ := exists_spatial_selected_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder Q A hQA hQ c L t a b w tau radius Lip eta sigma cell grid
    hw F hF hwideW hfreq hLtop htime hlength hLip heta hsigma hwide hK hlocal hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  classical
  obtain ⟨q0,hq0⟩ := hQ
  obtain ⟨first,hfirst,hcomp,hmin⟩ := P.exists_enclosing_scale L hLtop ⟨q0.1,hlength q0 hq0⟩
  let S := P.dropScales first
  let Qs := P.dropPackets first Q
  let As := P.dropPackets first A
  let d := fun j l v => c (dropIndex first j) l v
  let beta := fun j l k s => selector (dropIndex first j) l k s
  let cells := fun j l => cell (dropIndex first j) l
  let grid' := (((first.val:ℤ).negOnePow : ℤ)*grid)
  have hlevel (q : P.PacketIndex) (hq : q∈Q) : first.val≤q.1.val := hmin q.1 (hlength q hq)
  have hQs : Qs.Nonempty := P.dropPackets_nonempty first Q ⟨q0,hq0⟩ hlevel
  have hsub : Qs⊆As := P.dropPackets_mono first hQA
  have hmem (q : S.PacketIndex) (hq : q∈Qs) : P.dropPacket first q∈Q :=
    (P.mem_dropPackets first Q q).mp hq
  have hlocalS (j : Fin (N-first.val)) : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : S.labels j => S.rowSlope j l) (w/S.length j) M := by
    change SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels (dropIndex first j) => P.rowSlope (dropIndex first j) l)
      (w/(P.dropScales first).length j) M
    rw [P.dropScales_length]
    exact hlocal (dropIndex first j)
  have hXS (q : S.PacketIndex) (hq : q∈Qs) :
      |S.actualX q.1 q.2.1 q.2.2-a|≤(2*D:ℕ)*S.topLength := by
    have hh := hX (P.dropPacket first q) (hmem q hq)
    have he : S.actualX q.1 q.2.1 q.2.2=P.actualX (P.dropPacket first q).1
        (P.dropPacket first q).2.1 (P.dropPacket first q).2.2 := P.dropScales_actualX first q.1 q.2.1 q.2.2
    rw [he]
    apply hh.trans
    change (D:ℝ)*L≤(2*D:ℕ)*P.length first
    push_cast
    nlinarith [(Nat.cast_nonneg D : (0:ℝ)≤D)]
  have hYS (q : S.PacketIndex) (hq : q∈Qs) :
      |S.actualZ q.1 q.2.1 q.2.2-t*S.actualX q.1 q.2.1 q.2.2-b|≤(2*D:ℕ)*S.width := by
    have hh := hY (P.dropPacket first q) (hmem q hq)
    have hx : S.actualX q.1 q.2.1 q.2.2=P.actualX (P.dropPacket first q).1
        (P.dropPacket first q).2.1 (P.dropPacket first q).2.2 := P.dropScales_actualX first q.1 q.2.1 q.2.2
    have hy : S.actualZ q.1 q.2.1 q.2.2=P.actualZ (P.dropPacket first q).1
        (P.dropPacket first q).2.1 (P.dropPacket first q).2.2 := P.dropScales_actualZ first q.1 q.2.1 q.2.2
    rw [hx,hy]
    apply hh.trans
    change (D:ℝ)*P.width≤(2*D:ℕ)*P.width
    apply mul_le_mul_of_nonneg_right _ P.width_pos.le
    push_cast
    linarith [(Nat.cast_nonneg D : (0:ℝ)≤D)]
  have hRef (q : S.PacketIndex) (hq : q∈Qs) :
      t∈scaledAngularCell (w/S.topLength) grid' q.1.val (cells q.1 q.2.1) := by
    rw [P.dropScales_angularCell first w hw]
    exact href (P.dropPacket first q) (hmem q hq)
  have hAngle (q : S.PacketIndex) (hq : q∈Qs) :
      S.rowSlope q.1 q.2.1∈scaledAngularCell (w/S.topLength) grid' q.1.val (cells q.1 q.2.1) := by
    rw [P.dropScales_angularCell first w hw]
    exact hangle (P.dropPacket first q) (hmem q hq)
  have hSpec (q : S.PacketIndex) (hq : q∈Qs) (k : κ) (xi eta : ℝ)
      (hn : planarAngularFourier (S.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0) :
      |xi+S.rowSlope q.1 q.2.1*eta|≤cStar/S.length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta := by
    rw [P.dropScales_physicalPacket] at hn
    change |xi+P.rowSlope (dropIndex first q.1) q.2.1*eta|≤
      cStar/(P.dropScales first).length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta
    rw [P.dropScales_length]
    exact hspectrum (P.dropPacket first q) (hmem q hq) k xi eta hn
  have hBin (q : S.PacketIndex) (hq : q∈Qs) (k : κ) (xi eta : ℝ)
      (hn : planarAngularFourier (S.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0) :
      |eta-S.frequency k|≤Cv/S.width := by
    rw [P.dropScales_physicalPacket] at hn
    exact hbin (P.dropPacket first q) (hmem q hq) k xi eta hn
  have hSize (U : SlopeBox) (hU : U.width=S.width) (hUt : U.length≤tau) :
      S.unsignedSizeTestEnergy w cb cells grid' d As U≤sigma^2*U.area :=
    (P.dropScales_unsignedSizeTestEnergy_le first A w cb hw cell grid c U).trans (hsize U hU hUt)
  have hDensity (q : S.PacketIndex) (hq : q∈Qs) : S.ordinaryDensity 0 cells grid' w tau E u q≤eta := by
    rcases q with ⟨j,l,v⟩
    exact (P.dropScales_ordinaryDensity first 0 w tau hw cell grid E u j l v).le.trans
      (hdensity ⟨dropIndex first j,⟨l,v⟩⟩ (hmem ⟨j,⟨l,v⟩⟩ hq))
  have hSlope (q : S.PacketIndex) (hq : q∈Qs) : |S.rowSlope q.1 q.2.1-t|≤Cb*w/S.length q.1 := by
    change |P.rowSlope (dropIndex first q.1) q.2.1-t|≤Cb*w/(P.dropScales first).length q.1
    rw [P.dropScales_length]
    exact hslope (P.dropPacket first q) (hmem q hq)
  have hAway (q : S.PacketIndex) (hq : q∈Qs) (k : κ) (hk : beta q.1 q.2.1 k t≠0) :
      cb*w/S.length q.1≤|S.rowSlope q.1 q.2.1-t| := by
    change cb*w/(P.dropScales first).length q.1≤|P.rowSlope (dropIndex first q.1) q.2.1-t|
    rw [P.dropScales_length]
    exact hselaway (P.dropPacket first q) (hmem q hq) k hk
  have hRadius (j : Fin (N-first.val)) (l : S.labels j) (k : κ) (s : ℝ) (hs : beta j l k s≠0) :
      |s-S.rowSlope j l|≤radius*(w/S.length j) := by
    change |s-P.rowSlope (dropIndex first j) l|≤radius*(w/(P.dropScales first).length j)
    rw [P.dropScales_length]
    exact hselradius (dropIndex first j) l k s hs
  have hNear (j : Fin (N-first.val)) (l : S.labels j) (k : κ) (s : ℝ)
      (hs : |s-t|≤w/S.length j) :
      ‖beta j l k s-beta j l k t‖≤Lip*(|s-t|/(w/S.length j)) := by
    have he : S.length j=P.length (dropIndex first j) := P.dropScales_length first j
    rw [he] at hs ⊢
    exact hselnear (dropIndex first j) l k s hs
  have h := hTree (N-first.val) κ (fun j => Label (dropIndex first j))
    (fun j l => Item (dropIndex first j) l) S M R K (2*D) hR horder Qs As hsub d t a b
    w tau radius Lip eta sigma cells grid' hw F hF hwideW hfreq (hfirst.trans htime) hLip heta hsigma
    hwide hK hlocalS hXS hYS hRef hAngle hSpec hSlope
    hBin (fun q hq => hc (P.dropPacket first q) (hmem q hq)) hSize beta
    (fun j l k => hsel (dropIndex first j) l k)
    (fun j l k s => hselbound (dropIndex first j) l k s) hAway
    (fun j l k s hs => by
      rw [P.dropScales_angularCell first w hw]
      exact hselsupport (dropIndex first j) l k s hs)
    hRadius hNear E hE u hu hDensity
  have heval (z : ℝ×ℝ) := P.dropPackets_selector_value first Q hlevel 0 c
    (fun j l k => selector j l k (u z)) z
  dsimp only [S,Qs,d,beta] at h
  dsimp only
  change IntegrableOn _ E _ ∧ _ at h
  simp only [heval,P.dropScales_treeConstant] at h
  refine ⟨h.1,h.2.trans ?_⟩
  have hCt : 0≤P.referenceTreeConstant C ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have hp := P.profileBound_pos
    dsimp [referenceTreeConstant,referenceEnvelopeConstant]
    positivity
  have hwP := P.width_pos
  have hfac : 0≤(((4*D+1)^2:ℕ):ℝ)*
      (P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta*P.width) := by positivity
  have hecount : 2*(2*D)+1=4*D+1 := by omega
  rw [hecount]
  change (((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
    sigma*eta*P.length first*P.width)≤_
  calc
    _ = ((((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
        sigma*eta*P.width))*P.length first := by ring
    _ ≤ ((((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
        sigma*eta*P.width))*L := mul_le_mul_of_nonneg_left hfirst hfac
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
