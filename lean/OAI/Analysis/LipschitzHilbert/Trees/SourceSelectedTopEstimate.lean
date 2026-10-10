import OAI.Analysis.LipschitzHilbert.Trees.SourceRootedSelectedTree
import OAI.Analysis.LipschitzHilbert.Trees.SourceTopReferenceGeometry

namespace OAI

/-! The ordinary tree estimate for an actual selected packet set. Local
angular multiplicity supplies the row count; empty ambient rows disappear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem exists_selected_top_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0≤cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order → ∀ (Q A : Finset P.PacketIndex), Q⊆A → Q.Nonempty →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (T : SlopeBox) (dilation w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      T.width=P.width → dilation≤D → 0<w → ∀ (F : ℝ), 0≤F → w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → T.length≤P.topLength → T.length≤tau →
      (∀ q∈Q, P.length q.1≤T.length) → 0≤Lip → 0≤eta → 0≤sigma →
      1≤radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T dilation) →
      (∀ q∈Q, T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖≤sigma) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c A U≤sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ q∈Q, ∀ k, selector q.1 q.2.1 k T.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-T.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s, |s-T.slope|≤w/P.length j →
        ‖selector j l k s-selector j l k T.slope‖≤Lip*(|s-T.slope|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈Q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*(P.ordinaryTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*T.area) := by
  obtain ⟨C,hC,hTree⟩ := exists_rooted_selected_tree_estimate hL
    cStar cEta CEta cb 1 Cv hcStar hcEta hCEta hCv hcb (by norm_num) hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder Q A hQA hQ c T dilation w tau radius Lip eta sigma cell grid
    hwidth hdilation hw F hF hwideW hfreq hLtop htime hlength hLip heta hsigma hwide hK hlocal hcenter href hangle hspectrum hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  have hX (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualX q.1 q.2.1 q.2.2-T.x|≤(D:ℝ)*T.length :=
    (P.selected_top_centers T dilation q hwidth (hcenter q hq)).1.trans
      (mul_le_mul_of_nonneg_right hdilation T.length_pos.le)
  have hY (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|≤(D:ℝ)*P.width :=
    (P.selected_top_centers T dilation q hwidth (hcenter q hq)).2.trans
      (mul_le_mul_of_nonneg_right hdilation P.width_pos.le)
  have hcone (q : P.PacketIndex) (hq : q∈Q) :
      |P.rowSlope q.1 q.2.1-T.slope|≤1*w/P.length q.1 := by
    simpa only [one_mul] using P.selected_top_cone w hw cell grid q T (hlength q hq)
      (hangle q hq) (href q hq)
  have h := hTree N κ Label Item P M R K D hR horder Q A hQA hQ c
    T.length T.slope T.x (T.y-T.slope*T.x) w tau radius Lip eta sigma cell grid hw F hF
    (by simpa only [one_mul] using hwideW) hfreq hLtop htime hlength hLip heta hsigma
    hwide hK hlocal hX hY href hangle hspectrum hcone hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  refine ⟨h.1,h.2.trans_eq ?_⟩
  rw [SlopeBox.area,hwidth]
  ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
