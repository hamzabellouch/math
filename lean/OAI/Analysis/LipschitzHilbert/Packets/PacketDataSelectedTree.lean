import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum

namespace OAI

/-! Ordinary tree estimates for selected packets of an unrestricted slope
family. The only published input is scalar Lépingle variation. Small shear
is proved for the selected reference family, not assumed globally. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_recentered_selected_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K : ℕ),
      Cb≤R → 207≤P.order → ∀ (Q : Finset P.PacketIndex), Q.Nonempty →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → ∀ (F : ℝ), 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → P.topLength≤tau → 0≤Lip → 0≤eta → 0≤sigma →
      1≤radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖≤sigma) →
      (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
        ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)≤sigma^2*(P.topLength*P.width) →
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
          P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta*P.topLength*P.width := by
  obtain ⟨C,hC,hTree⟩ := SourceLabeledLattice.exists_reference_ordinary_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K hR horder S hS c t a b w tau radius Lip eta sigma cell grid
    hw F hF hwideW hfreq htime hLip heta hsigma hwide hK hlocal hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  let T := P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope
  let d := P.selectedCoefficients S t Cb w F hw hCb hF hwideW hfreq hslope c
  let beta := fun j (l : T.labels j) k s => selector j (P.selectedOriginalLabel S j l) k s
  let cells := P.selectedCells S t Cb w F hw hCb hF hwideW hfreq hslope cell
  have hmem (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l) :
      (⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ : P.PacketIndex)∈S :=
    P.selectedItem_mem S j l v
  have hne : Nonempty T.PacketIndex := by
    obtain ⟨q,hq⟩ := hS
    exact ⟨(P.selectedReferenceEquiv S t Cb w F hw hCb hF hwideW hfreq hslope).symm ⟨q,hq⟩⟩
  have hcard (j : Fin N) : (T.labels j).card≤(2*R+1)*M :=
    P.selectedReference_card S t Cb w F hw hCb hF hwideW hfreq hslope M R hR hlocal j
  have hTX (q : T.PacketIndex) : |T.actualX q.1 q.2.1 q.2.2-a|≤T.topLength/2 := by
    rcases q with ⟨j,l,v⟩
    exact hX ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTY (q : T.PacketIndex) : |T.actualZ q.1 q.2.1 q.2.2-b|≤T.width/2 := by
    rcases q with ⟨j,l,v⟩
    change |(P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope).actualZ j l v-b|≤P.width/2
    rw [P.selectedReference_actualZ S t Cb w F hw hCb hF hwideW hfreq hslope j l v]
    exact hY ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTref (q : T.PacketIndex) : t∈scaledAngularCell (w/T.topLength)
      grid q.1.val (cells q.1 q.2.1) := by
    rcases q with ⟨j,l,v⟩
    exact href ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTangle (j : Fin N) (l : T.labels j) : t+T.rowSlope j l∈
      scaledAngularCell (w/T.topLength) grid j.val (cells j l) := by
    obtain ⟨v,hv⟩ := P.selectedLabel_has_packet S j l
    rw [P.selectedReference_slope S t Cb w F hw hCb hF hwideW hfreq hslope j l]
    exact hangle ⟨j,⟨P.selectedOriginalLabel S j l,v⟩⟩ hv
  have hTspectrum (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l)
      (k : κ) (xi eta : ℝ) (h : planarAngularFourier (T.physicalPacket t j l v k) (xi,eta)≠0) :
      |xi+(t+T.rowSlope j l)*eta|≤cStar/T.length j ∧ cEta≤w*eta ∧ w*eta≤CEta :=
    P.selectedReference_spectrum_at S t Cb w F hw hCb hF hwideW hfreq hslope cStar cEta CEta
      j l v k xi eta (hspectrum ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v) k xi eta) h
  have hTslope (j : Fin N) (l : T.labels j) : |T.rowSlope j l|≤Cb*w/T.length j :=
    P.selectedLabel_near S t Cb w hslope j l
  have hTbin (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l)
      (k : κ) (xi eta : ℝ) (h : planarAngularFourier (T.physicalPacket t j l v k) (xi,eta)≠0) :
      |eta-T.frequency k|≤Cv/T.width := by
    change planarAngularFourier
      ((P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope).physicalPacket t j l v k) (xi,eta)≠0 at h
    rw [P.selectedReference_physicalPacket S t Cb w F hw hCb hF hwideW hfreq hslope j l v k] at h
    exact hbin ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v) k xi eta h
  have hTc (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l) : ‖d j l v‖≤sigma :=
    hc ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTsize : T.angularSeparatedTreeEnergy cb w d≤sigma^2*(T.topLength*T.width) :=
    (P.selectedReference_separated_energy S t Cb w F hw hCb hF hwideW hfreq hslope c cb).le.trans hsize
  have haway (j : Fin N) (l : T.labels j) (k : κ) :
      beta j l k t≠0 → cb*w/T.length j≤|T.rowSlope j l| := by
    obtain ⟨v,hv⟩ := P.selectedLabel_has_packet S j l
    exact hselaway ⟨j,⟨P.selectedOriginalLabel S j l,v⟩⟩ hv k
  have hradius (j : Fin N) (l : T.labels j) (k : κ) (s : ℝ) (hs : beta j l k s≠0) :
      |s-(t+T.rowSlope j l)|≤radius*(w/T.length j) := by
    rw [P.selectedReference_slope S t Cb w F hw hCb hF hwideW hfreq hslope j l]
    exact hselradius j (P.selectedOriginalLabel S j l) k s hs
  have hD (q : T.PacketIndex) : T.ordinaryDensity t cells grid w tau E u q≤eta := by
    rcases q with ⟨j,l,v⟩
    change (P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope).ordinaryDensity t
      (P.selectedCells S t Cb w F hw hCb hF hwideW hfreq hslope cell) grid w tau E u ⟨j,l,v⟩≤eta
    rw [P.selectedReference_density S t Cb w F hw hCb hF hwideW hfreq hslope cell grid tau E u j l v]
    exact hdensity ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have h := hTree N κ Label (P.SelectedItem S) T ((2*R+1)*M) K hcard horder hne
    d t a b w tau radius Lip eta sigma cells grid hw htime hLip heta hsigma hwide hK
    hTX hTY hTref hTangle hTspectrum hTslope hTbin hTc hTsize beta
    (fun j l k => hsel j (P.selectedOriginalLabel S j l) k)
    (fun j l k s => hselbound j (P.selectedOriginalLabel S j l) k s) haway
    (fun j l k s => hselsupport j (P.selectedOriginalLabel S j l) k s) hradius
    (fun j l k s => hselnear j (P.selectedOriginalLabel S j l) k s)
    E hE u hu hD
  dsimp only at h ⊢
  have heval (z : ℝ×ℝ) : T.physicalTreeSelectorValue t d
      (fun j l k => beta j l k (u z)) z=
      ∑ q∈S, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) :=
    P.selectedReference_synthesis S t Cb w F hw hCb hF hwideW hfreq hslope c
      (fun j l k => selector j l k (u z)) z
  have hconst : T.ordinaryTreeConstant C ((2*R+1)*M) K Lip=
      P.referenceTreeConstant C ((2*R+1)*M) K Lip := rfl
  simp only [heval,hconst] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
