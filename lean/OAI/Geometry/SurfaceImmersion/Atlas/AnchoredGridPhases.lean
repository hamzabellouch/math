import OAI.Geometry.SurfaceImmersion.Geometry.AnchoredCellGeometry
import OAI.Geometry.Immersion.ClosedSurface.GridPhases

namespace OAI

/-! Grid phases selected at support anchors, with a fixed finite phase catalog. -/
noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set

theorem anchored_polynomial_grid_phases {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ stock : Finset PhaseBasis, ∃ ε C δ z₀ W κ : ℝ,
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < W ∧ 0 < κ ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
      ∀ F : RField 4, ContDiff ℝ ∞ F → WeightedBound univ z 3 A F →
      ∀ H : Base → PhaseMean.Tensor,
        (∀ x y, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∀ s : Finset PhaseGrid.Index,
        (∀ a ∈ s, ∃ x : Base, ‖x-z^6 • PhaseGrid.center a‖ ≤ 3*z^6 ∧
          ‖firstJetPair F x‖ ≤ R ∧
          c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 ∧
          b ≤ ‖realSecondTensor F x‖ ∧ H x ∈ T) →
      ∃ (P : {a // a ∈ s} → PhaseBasis) (w : {a // a ∈ s} × Fin 3 → ℝ),
        (∀ a, P a ∈ stock) ∧
        (∀ a i, ‖(P a).ξ i‖ ≤ C ∧ ‖(P a).Q i‖ ≤ C) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        (∀ a y G H', y ∈ tsupport (PhaseGrid.cutoff (z^6) a.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
          c/4 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
          b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ (P a).Q i H' ∧
            (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-((P a).ξ i).2,((P a).ξ i).1)‖ ∧
            Good (realSecondTensor G y) ((P a).ξ i)) ∧
        (∀ a d y G, a ≠ d → y ∈ tsupport (PhaseGrid.cutoff (z^6) a.1.val) →
          y ∈ tsupport (PhaseGrid.cutoff (z^6) d.1.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 →
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).1)‖ ∧
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).1)‖ ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2) ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2)) := by
  classical
  obtain ⟨stock,ε,C,δ,z₀,hε,hC,hδ,hz₀,hz₀1,hstock,hcell⟩ :=
    anchored_polynomial_cell_phases hT hT0 hTd R c A b K hc hA hb hK
  obtain ⟨d,k,hd,hk,hm⟩ := universal_relative_length_margin (n := 4) (C := C) (by positivity : 0 < ε/4)


  let aa : ℝ := 1+1/d
  let WW : ℝ := aa^(Fintype.card PhaseGrid.Label)
  have haa : 1 ≤ aa := by dsimp [aa]; linarith [one_div_pos.mpr hd]
  have haa0 : 0 < aa := zero_lt_one.trans_le haa
  have had : 1 < d*aa := by dsimp [aa]; rw [mul_add,mul_one,mul_one_div_cancel hd.ne']; linarith
  refine ⟨stock,ε,C,δ,z₀,WW,k,hε,hC,hδ,hz₀,hz₀1,pow_pos haa0 _,hk,?_⟩
  intro z hz hzsmall F hF hFbound H hHLip s hanchors
  let I := {a // a ∈ s}
  choose anchor hdist hjet hgram hnormal htarget using
    fun a : I => hanchors a.val a.property
  have hselection (a : I) := hcell z hz hzsmall F hF hFbound H (anchor a)
    (hjet a) (hgram a) (hnormal a) (htarget a) (hHLip (anchor a))
  choose P hPs hP using hselection
  let w (a : I × Fin 3) : ℝ := aa^(PhaseGrid.phaseLabel (a.1.val,a.2)).val
  have hw (a : I × Fin 3) : 1 ≤ w a ∧ w a ≤ WW :=
    ⟨one_le_pow₀ haa,pow_le_pow_right₀ haa (PhaseGrid.phaseLabel (a.1.val,a.2)).isLt.le⟩
  have hpoint (a : I) (y : Base) (G : RField 4) (H' : PhaseMean.Tensor)
      (hy : y ∈ tsupport (PhaseGrid.cutoff (z^6) a.val))
      (h1 : ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4)
      (h2 : ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4) (hh : ‖H'-H y‖ ≤ δ) :=
    hP a y G H' (by
      have hy := cutoff_distance_to_center (pow_pos hz 6) a.val hy
      calc
        ‖y-anchor a‖ ≤ ‖y-z^6 • PhaseGrid.center a.val‖+
            ‖z^6 • PhaseGrid.center a.val-anchor a‖ := by
              simpa only [dist_eq_norm] using dist_triangle y (z^6 • PhaseGrid.center a.val) (anchor a)
        _ = ‖y-z^6 • PhaseGrid.center a.val‖+
            ‖anchor a-z^6 • PhaseGrid.center a.val‖ := by rw [norm_sub_rev (z^6 • PhaseGrid.center a.val)]
        _ ≤ 6*z^6 := by linarith [hdist a]) h1 h2 hh
  refine ⟨P,w,hPs,fun a i => hstock (P a) (hPs a) i,hw,?_,?_⟩
  · intro a y G H' hy h1 h2 hh
    obtain ⟨hg,hB,hi⟩ := hpoint a y G H' hy h1 h2 hh
    exact ⟨hg,hB,fun i => ⟨(hi i).1,(hi i).2.1,(hi i).2.2.2⟩⟩
  · intro a e y G hae hay hey h1 h2
    have haB := hpoint a.1 y G (H y) hay h1 h2 (by simpa using hδ.le)
    have heB := hpoint e.1 y G (H y) hey h1 h2 (by simpa using hδ.le)
    have hBn : realSecondTensor G y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((half_pos hb).trans_le haB.2.1))
    have ordered (a e : I × Fin 3)
        (ha : y ∈ tsupport (PhaseGrid.cutoff (z^6) a.1.val))
        (he : y ∈ tsupport (PhaseGrid.cutoff (z^6) e.1.val))
        (hlt : (PhaseGrid.phaseLabel (a.1.val,a.2)).val < (PhaseGrid.phaseLabel (e.1.val,e.2)).val) :
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).1)‖ ∧
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).1)‖ := by
      have hmargin := ((hpoint e.1 y G (H y) he h1 h2 (by simpa using hδ.le)).2.2 e.2).2.1
      exact power_weight_length_pairs _ _ _ haa had
        (fun t ht => hm _ _ _ hBn (hstock (P e.1) (hPs e.1) e.2).1
          (hstock (P a.1) (hPs a.1) a.2).1 hmargin t ht.le) hlt
    have hne : (a.1.val,a.2) ≠ (e.1.val,e.2) := by
      intro heq
      have hfirst : a.1.val = e.1.val := congrArg (fun p : PhaseGrid.Index × Fin 3 => p.1) heq
      have hsecond : a.2 = e.2 := congrArg (fun p : PhaseGrid.Index × Fin 3 => p.2) heq
      exact hae (Prod.ext (Subtype.ext hfirst) hsecond)
    have hlab := PhaseGrid.distinct_labels_on_intersection (pow_pos hz _) hne hay hey
    have hnv : (PhaseGrid.phaseLabel (a.1.val,a.2)).val ≠ (PhaseGrid.phaseLabel (e.1.val,e.2)).val :=
      fun heq => hlab (Fin.ext heq)
    have hlen :
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).1)‖ ∧
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).1)‖ := by
      rcases lt_or_gt_of_ne hnv with hlt | hgt
      · exact ordered a e hay hey hlt
      · obtain ⟨hp,hm⟩ := ordered e a hey hay hgt
        refine ⟨by simpa only [add_comm] using hp,?_⟩
        have heq : w e • (P e.1).ξ e.2-w a • (P a.1).ξ a.2 = -(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2) := by abel
        simpa only [heq,norm_secondQuadratic_rotated_neg] using hm
    have hpos : 0 < k*‖realSecondTensor G y‖ := mul_pos hk (norm_pos_iff.mpr hBn)
    exact ⟨hlen.1,hlen.2,good_of_direction_length_pos _ _ (hpos.trans_le hlen.1),
      good_of_direction_length_pos _ _ (hpos.trans_le hlen.2)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
