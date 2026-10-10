import OAI.Geometry.Immersion.ClosedSurface.GridBumps

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

lemma norm_sub_center_lt {h R : ℝ} {a : Index} {x : Base}
    (hx : x ∈ cell h R a) : ‖x-h • center a‖ < R*h := by
  change max |x.1-h*a.1| |x.2-h*a.2| < R*h
  exact max_lt hx.1 hx.2




theorem compact_subpatch_grid {K U : Set Base} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < C ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ C/h^2 ∧
        (∀ x ∈ K, ∃ a ∈ s, x ∈ cell h 1 a) ∧
        (∀ a ∈ s, h • center a ∈ U ∧ tsupport (cutoff h a) ⊆ U) := by
  classical
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨A,hA,hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨min 1 (δ/5),(2*A+5)^2,lt_min zero_lt_one (by positivity),
    min_le_left _ _,by positivity,?_⟩
  intro h hh hsmall
  have hh1 : h ≤ 1 := hsmall.trans (min_le_left _ _)
  have hδh : 4*h ≤ δ := by
    have ht : h ≤ δ/5 := hsmall.trans (min_le_right _ _)
    linarith
  let N : ℕ := ⌈A/h+1⌉₊
  have hNlo : A/h+1 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ A/h+2 := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ A/h+1 by positivity)
    dsimp [N]
    linarith
  let s := (box N).filter (fun a => ∃ x ∈ K, x ∈ cell h 1 a)
  refine ⟨s,?_,?_,?_⟩
  · calc
      (s.card : ℝ) ≤ ((box N).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ ((2*A+5)/h)^2 := box_card_bound hA.le hh hh1 hNhi
      _ = (2*A+5)^2/h^2 := div_pow _ _ _
  · intro x hx
    have hnorm := hbound x hx
    have hcoords : |x.1| ≤ A ∧ |x.2| ≤ A :=
      ⟨(le_max_left _ _).trans hnorm,(le_max_right _ _).trans hnorm⟩
    obtain ⟨a,ha,hxa⟩ := finite_box_covers hh hNlo hcoords
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,x,hx,hxa⟩,hxa⟩
  · intro a ha
    obtain ⟨_,x,hx,hxa⟩ := Finset.mem_filter.mp ha
    have hxc : ‖x-h • center a‖ < h := by
      simpa using norm_sub_center_lt hxa
    constructor
    · apply hthick
      apply Metric.mem_cthickening_of_dist_le _ x δ K hx
      rw [dist_eq_norm,norm_sub_rev]
      linarith
    · intro y hy
      have hyc : ‖y-h • center a‖ < 3*h := norm_sub_center_lt (cutoff_tsupport_subset hh a hy)
      have hxy : ‖y-x‖ ≤ ‖y-h • center a‖+‖x-h • center a‖ := by
        simpa [dist_eq_norm,norm_sub_rev] using dist_triangle y (h • center a) x
      apply hthick
      apply Metric.mem_cthickening_of_dist_le _ x δ K hx
      rw [dist_eq_norm]
      linarith



theorem compact_subpatch_polynomial_grid {K U : Set Base}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ z₀ C : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < C ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ C/z^12 ∧
        (∀ x ∈ K, ∃ a ∈ s, x ∈ cell (z^6) 1 a) ∧
        (∀ a ∈ s, z^6 • center a ∈ U ∧ tsupport (cutoff (z^6) a) ⊆ U) := by
  obtain ⟨h₀,C,hh₀,hh₀1,hC,hgrid⟩ := compact_subpatch_grid hK hU hKU
  refine ⟨h₀,C,hh₀,hh₀1,hC,fun z hz hzsmall => ?_⟩
  have hz1 : z ≤ 1 := hzsmall.trans hh₀1
  have hp : z^5 ≤ 1 := by simpa using pow_le_pow_left₀ hz.le hz1 5
  have hzpow : z^6 ≤ h₀ := by
    have hm := mul_le_mul_of_nonneg_left hp hz.le
    nlinarith [hm]
  obtain ⟨s,hcard,hcover,hsub⟩ := hgrid (z^6) (pow_pos hz _) hzpow
  refine ⟨s,?_,hcover,hsub⟩
  simpa only [← pow_mul] using hcard
end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.PhaseGrid
open Set
attribute [local instance] Classical.propDecidable
abbrev Label := (ZMod 6 × ZMod 6) × Fin 3

def phaseLabel (a : Index × Fin 3) : Fin (Fintype.card Label) :=
  Fintype.equivFin Label (color 6 a.1, a.2)

lemma phase_label_count : Fintype.card Label = 108 := by norm_num [Label]



theorem distinct_labels_on_intersection {h : ℝ} (hh : 0 < h)
    {a b : Index × Fin 3} (hab : a ≠ b) {x : Base}
    (ha : x ∈ tsupport (cutoff h a.1)) (hb : x ∈ tsupport (cutoff h b.1)) :
    phaseLabel a ≠ phaseLabel b := by
  intro he
  have hp := (Fintype.equivFin Label).injective he
  have hc : color 6 a.1 = color 6 b.1 := congrArg Prod.fst hp
  have hi : a.2 = b.2 := congrArg (fun p : Label => p.2) hp
  by_cases hcelleq : a.1 = b.1
  · exact hab (Prod.ext hcelleq hi)
  · exact (Set.disjoint_left.mp (cutoff_same_color_disjoint hh hcelleq hc)) ha hb


theorem active_cutoff_count {h : ℝ} (hh : 0 < h) (s : Finset Index) (x : Base) :
    (s.filter (fun a => x ∈ tsupport (cutoff h a))).card ≤ 36 := by
  classical
  let t := s.filter (fun a => x ∈ tsupport (cutoff h a))
  have hinj : Set.InjOn (color 6) (t : Set Index) := by
    intro a ha b hb he
    by_contra hne
    exact (Set.disjoint_left.mp (cutoff_same_color_disjoint hh hne he))
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have heq := Finset.card_image_of_injOn hinj
  have hb := Finset.card_le_univ (t.image (color 6))
  rw [heq] at hb
  simpa using hb

end ClosedSurfaceR4.PhaseGrid

end

end OAI
