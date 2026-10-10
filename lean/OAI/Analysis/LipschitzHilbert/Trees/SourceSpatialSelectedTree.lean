import OAI.Analysis.LipschitzHilbert.Trees.SourceRecenteredSelectedTree
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceTreeSize
import OAI.Analysis.LipschitzHilbert.Trees.SourceSpatialTreePieces

namespace OAI

/-! The ordinary tree estimate for an actual selected packet set. Local
angular multiplicity supplies the row count; empty ambient rows disappear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem exists_spatial_selected_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M R K D : ℕ),
      Cb≤R → 207≤P.order → ∀ (Q A : Finset P.PacketIndex), Q⊆A →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → ∀ (F : ℝ), 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → P.topLength≤tau → 0≤Lip → 0≤eta → 0≤sigma →
      1≤radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤(D:ℝ)*P.topLength) →
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
          (((2*D+1)^2:ℕ):ℝ)*(P.ordinaryTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*P.topLength*P.width) := by
  obtain ⟨C,hC,hTree⟩ := exists_recentered_selected_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder Q A hQA c t a b w tau radius Lip eta sigma cell grid
    hw F hF hwideW hfreq htime hLip heta hsigma hwide hK hlocal hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  classical
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let Y := fun q : P.PacketIndex => P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2
  let cells := (Finset.Icc (-(D:ℤ)) D) ×ˢ (Finset.Icc (-(D:ℤ)) D)
  let part := fun p => spatialTreePiece Q X Y a b P.topLength P.width p
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let B := P.ordinaryTreeConstant C ((2*R+1)*M) K Lip*sigma*eta*P.topLength*P.width
  have hCtree : 0≤P.ordinaryTreeConstant C ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have ha := P.absoluteConstant_pos
    have hp := P.profileBound_pos
    dsimp [ordinaryTreeConstant]
    positivity
  have hB : 0≤B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCtree hsigma) heta)
      P.topLength_pos.le) P.width_pos.le
  have hp (p : ℤ×ℤ) :
      IntegrableOn (fun z => ∑ q∈part p, V q z) E (volume.prod volume) ∧
      (∫ z in E, ‖∑ q∈part p, V q z‖ ∂volume.prod volume)≤B := by
    have hsub : part p⊆Q := Finset.filter_subset _ _
    by_cases hn : (part p).Nonempty
    · have hcenter := fun q hq => spatialTreePiece_centers Q X Y a b P.topLength P.width
        P.topLength_pos P.width_pos p q hq
      have henergy := P.reference_piece_size_bound (part p) A (hsub.trans hQA)
        t (spatialCellCenter a P.topLength p.1) (spatialCellCenter b P.width p.2)
        w cb tau sigma cell grid c htime (fun q hq => (hcenter q hq).1)
        (fun q hq => (hcenter q hq).2) (fun q hq => href q (hsub hq)) hsize
      exact hTree N κ Label Item P M R K hR horder (part p) hn c t
        (spatialCellCenter a P.topLength p.1) (spatialCellCenter b P.width p.2)
        w tau radius Lip eta sigma cell grid hw F hF hwideW hfreq htime hLip heta hsigma
        hwide hK hlocal (fun q hq => (hcenter q hq).1) (fun q hq => (hcenter q hq).2)
        (fun q hq => href q (hsub hq)) (fun q hq => hangle q (hsub hq))
        (fun q hq => hspectrum q (hsub hq)) (fun q hq => hslope q (hsub hq))
        (fun q hq => hbin q (hsub hq)) (fun q hq => hc q (hsub hq)) henergy
        selector hsel hselbound (fun q hq => hselaway q (hsub hq)) hselsupport hselradius
        hselnear E hE u hu (fun q hq => hdensity q (hsub hq))
    · have he : part p=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he,Finset.sum_empty,norm_zero,integral_zero]
      exact ⟨integrableOn_zero,hB⟩
  have heval (z : ℝ×ℝ) : (∑ p∈cells, ∑ q∈part p, V q z)=∑ q∈Q, V q z :=
    sum_spatialTreePieces Q X Y a b P.topLength P.width P.topLength_pos P.width_pos D hX hY (fun q => V q z)
  have hI := integrable_finsetSum cells (fun p _ => (hp p).1)
  refine ⟨?_,?_⟩
  · change IntegrableOn (fun z => ∑ q∈Q, V q z) E (volume.prod volume)
    have he : (fun z => ∑ p∈cells, ∑ q∈part p, V q z)=(fun z => ∑ q∈Q, V q z) := funext heval
    rw [he] at hI
    exact hI
  · calc
      _ = ∫ z in E, ‖∑ p∈cells, ∑ q∈part p, V q z‖ ∂volume.prod volume := by
        change (∫ z in E, ‖∑ q∈Q, V q z‖ ∂volume.prod volume)=_
        simp only [heval]
      _ ≤ ∫ z in E, ∑ p∈cells, ‖∑ q∈part p, V q z‖ ∂volume.prod volume :=
        integral_mono hI.norm (integrable_finsetSum cells (fun p _ => (hp p).1.norm))
          (fun z => norm_sum_le _ _)
      _ = ∑ p∈cells, ∫ z in E, ‖∑ q∈part p, V q z‖ ∂volume.prod volume :=
        integral_finsetSum _ (fun p _ => (hp p).1.norm)
      _ ≤ ∑ _p∈cells, B := Finset.sum_le_sum (fun p _ => (hp p).2)
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        rw [show cells.card=(2*D+1)^2 from spatialCell_count D]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
