import OAI.Probability.SLE.Geometry.SimpleArcComplement
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! A common connected exterior for every bounded half-plane obstacle.
This lets unbounded complementary components be identified without any
boundary regularity or choice of a conformal map. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

def halfPlaneRectangleExterior (R : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ (R < |z.re| ∨ R < z.im)}

lemma halfPlaneRectangleExterior_connected {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (halfPlaneRectangleExterior R) := by
  let L : Set ℂ := {z | z.re < -R ∧ 0 < z.im}
  let U : Set ℂ := {z | R < z.im}
  let V : Set ℂ := {z | R < z.re ∧ 0 < z.im}
  have hL : Convex ℝ L :=
    (convex_halfSpace_re_lt (-R)).inter (convex_halfSpace_im_gt 0)
  have hU : Convex ℝ U := convex_halfSpace_im_gt R
  have hV : Convex ℝ V :=
    (convex_halfSpace_re_gt R).inter (convex_halfSpace_im_gt 0)
  have hLU : (L ∩ U).Nonempty := by
    refine ⟨((-R-1 : ℝ) : ℂ)+((R+1:ℝ):ℂ)*I,?_,?_⟩
    all_goals norm_num [L,U]
    all_goals linarith
  have hUV : ((L ∪ U) ∩ V).Nonempty := by
    refine ⟨((R+1 : ℝ) : ℂ)+((R+1:ℝ):ℂ)*I,Or.inr ?_,?_⟩
    all_goals norm_num [U,V]
    all_goals linarith
  have hpre := (hL.isPreconnected.union' hLU hU.isPreconnected).union' hUV hV.isPreconnected
  have he : halfPlaneRectangleExterior R = (L ∪ U) ∪ V := by
    ext z
    simp only [halfPlaneRectangleExterior,L,U,V,mem_ofPred_eq,mem_union]
    rw [lt_abs]
    constructor
    · rintro ⟨hi,(hr|hiR)⟩
      · rcases hr with hr|hr
        · exact Or.inr ⟨hr,hi⟩
        · exact Or.inl (Or.inl ⟨by linarith,hi⟩)
      · exact Or.inl (Or.inr hiR)
    · rintro ((⟨hr,hi⟩|hi)|⟨hr,hi⟩)
      · exact ⟨hi,Or.inl (Or.inr (by linarith))⟩
      · exact ⟨lt_of_le_of_lt hR hi,Or.inr hi⟩
      · exact ⟨hi,Or.inl (Or.inl hr)⟩
  rw [he]
  exact ⟨⟨hLU.choose,Or.inl (Or.inl hLU.choose_spec.1)⟩,hpre⟩

lemma mem_halfPlaneRectangleExterior_of_norm_lt {R : ℝ} {z : ℂ}
    (hz : 0 < z.im) (hn : 2*R < ‖z‖) :
    z ∈ halfPlaneRectangleExterior R := by
  refine ⟨hz,?_⟩
  by_contra h
  push Not at h
  have hb := norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hz] at hb
  linarith

lemma halfPlaneRectangleExterior_disjoint_bounded {K : Set ℂ} {R : ℝ}
    (hK : ∀ z ∈ K, ‖z‖ ≤ R) :
    halfPlaneRectangleExterior R ⊆ upperHalfPlane \ K := by
  intro z hz
  refine ⟨hz.1,?_⟩
  intro hzK
  rcases hz.2 with hr|hi
  · exact (hK z hzK).not_gt (hr.trans_le (abs_re_le_norm z))
  · exact (hK z hzK).not_gt (hi.trans_le ((le_abs_self z.im).trans (abs_im_le_norm z)))

theorem halfPlane_complement_connected_of_unbounded_components
    {K : Set ℂ} (hK : Bornology.IsBounded K)
    (hcomp : ∀ z ∈ upperHalfPlane \ K,
      ¬ Bornology.IsBounded (connectedComponentIn (upperHalfPlane \ K) z)) :
    IsConnected (upperHalfPlane \ K) := by
  obtain ⟨R,hR,hbound⟩ := hK.subset_ball_lt 0 (0:ℂ)
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := by
    intro z hz
    exact (show ‖z‖ < R by simpa only [mem_ball,dist_zero_right] using hbound hz).le
  let E := halfPlaneRectangleExterior R
  have hE : IsConnected E := halfPlaneRectangleExterior_connected hR.le
  have hED : E ⊆ upperHalfPlane \ K := halfPlaneRectangleExterior_disjoint_bounded hKR
  obtain ⟨w,hw⟩ := hE.nonempty
  have heq : upperHalfPlane \ K = connectedComponentIn (upperHalfPlane \ K) w := by
    apply Subset.antisymm _ (connectedComponentIn_subset _ _)
    intro z hz
    have hn := hcomp z hz
    have hexc : ∃ v ∈ connectedComponentIn (upperHalfPlane \ K) z, 2*R < ‖v‖ := by
      by_contra he
      push Not at he
      apply hn
      apply (isBounded_closedBall (x := (0:ℂ)) (r := 2*R)).subset
      intro v hv
      simpa only [mem_closedBall,dist_zero_right] using he v hv
    obtain ⟨v,hv,hvR⟩ := hexc
    have hvE : v ∈ E := mem_halfPlaneRectangleExterior_of_norm_lt
      (connectedComponentIn_subset _ _ hv).1 hvR
    have hwC := hE.isPreconnected.subset_connectedComponentIn hvE hED hw
    rw [← connectedComponentIn_eq hv] at hwC
    rw [← connectedComponentIn_eq hwC]
    exact mem_connectedComponentIn hz
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr (hED hw)

end SLEExactGauge

end

end OAI
