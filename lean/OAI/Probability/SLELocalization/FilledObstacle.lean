import Mathlib
import OAI.Probability.SLELocalization.CommonClocks
import OAI.Probability.SLELocalization.PastObstacle

namespace OAI


/-! Conformal localization and Filled Obstacle estimates. -/

noncomputable section
open Set Filter Topology
open scoped Topology
namespace SLEExactGauge

lemma nearest_segment_subset_filling {A K : Set ℂ} (hAK : A ⊆ K)
    (hfill : ∀ x ∈ K, connectedComponentIn Aᶜ x ⊆ K)
    {x a : ℂ} (hx : x ∈ K) (ha : a ∈ A)
    (hnear : ∀ b ∈ A, dist x a ≤ dist x b) :
    _root_.segment ℝ x a ⊆ K := by
  by_cases he : x = a
  · subst a
    simpa using singleton_subset_iff.mpr hx
  have hd : 0 < dist x a := dist_pos.mpr he
  let L : ℝ → ℂ := AffineMap.lineMap x a
  have hc : Continuous L := (lipschitzWith_lineMap x a).continuous
  have hLA : L '' Ico 0 1 ⊆ Aᶜ := by
    rintro _ ⟨t,ht,rfl⟩ hb
    have hh := hnear _ hb
    rw [dist_left_lineMap,Real.norm_eq_abs,abs_of_nonneg ht.1] at hh
    have ht1 := ht.2
    nlinarith
  have hxL : x ∈ L '' Ico 0 1 := ⟨0,by norm_num,by simp [L]⟩
  have hLK : L '' Ico 0 1 ⊆ K := (isPreconnected_Ico.image _ hc.continuousOn
    |>.subset_connectedComponentIn hxL hLA).trans (hfill x hx)
  rw [segment_eq_image_lineMap]
  rintro _ ⟨t,ht,rfl⟩
  rcases lt_or_eq_of_le ht.2 with ht1 | rfl
  · exact hLK ⟨t,⟨ht.1,ht1⟩,rfl⟩
  · simpa using hAK ha

lemma past_obstacle_subset_filled {γ : ℝ → ℂ} {T : ℝ} :
    halfPlaneᶜ ∪ localizationSegment γ 0 T ⊆ (localizationDomain γ T)ᶜ := by
  intro z hz hd
  rcases hz with h | h
  · exact h hd.1.1
  · exact hd.1.2 h

lemma past_filled_component_closed {γ : ℝ → ℂ} {T : ℝ} :
    ∀ x ∈ (localizationDomain γ T)ᶜ,
      connectedComponentIn (halfPlaneᶜ ∪ localizationSegment γ 0 T)ᶜ x ⊆
        (localizationDomain γ T)ᶜ := by
  intro x hx y hy hys
  have he : (halfPlaneᶜ ∪ localizationSegment γ 0 T)ᶜ = halfPlane \ localizationSegment γ 0 T := by
    ext z; simp
  rw [he] at hy
  have hxx : x ∈ halfPlane \ localizationSegment γ 0 T :=
    (connectedComponentIn_nonempty_iff).mp ⟨y,hy⟩
  apply hx
  refine ⟨hxx,?_⟩
  simpa only [connectedComponentIn_eq hy] using hys.2

lemma locallyConnected_of_component_balls {K : Set ℂ}
    (h : ∀ x ∈ K, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ K, dist y x < δ → y ∈ connectedComponentIn (K ∩ Metric.ball x ε) x) :
    LocallyConnectedSpace K := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨δ,hδ,hh⟩ := h x x.property ε hε
  let C := connectedComponentIn (K ∩ Metric.ball (x:ℂ) ε) (x:ℂ)
  have hCK : C ⊆ K := (connectedComponentIn_subset _ _).trans inter_subset_left
  refine ⟨Subtype.val ⁻¹' C,?_,?_,?_⟩
  · apply Metric.mem_nhds_iff.mpr
    exact ⟨δ,hδ,fun y hy => hh y y.property hy⟩
  · apply IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe,inter_eq_right.mpr hCK] using
      (isPreconnected_connectedComponentIn : IsPreconnected C)
  · intro y hy
    exact hεU ((connectedComponentIn_subset _ _ hy).2)

lemma locallyConnected_filling {A K : Set ℂ} (hA : IsClosed A)
    [LocallyConnectedSpace A] (hAK : A ⊆ K)
    (hfill : ∀ x ∈ K, connectedComponentIn Aᶜ x ⊆ K) :
    LocallyConnectedSpace K := by
  apply locallyConnected_of_component_balls
  intro x hx ε hε
  by_cases hxA : x ∈ A
  · let xA : A := ⟨x,hxA⟩
    obtain ⟨V,hV,hVc,hVε⟩ := locallyConnectedSpace_iff_connected_subsets.1
      (inferInstance : LocallyConnectedSpace A) xA (Metric.ball xA ε)
      (Metric.ball_mem_nhds _ hε)
    obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp hV
    let C : Set ℂ := Subtype.val '' V
    have hCA : C ⊆ A := Subtype.coe_image_subset _ _
    have hCε : C ⊆ Metric.ball x ε := by
      rintro _ ⟨v,hv,rfl⟩
      exact hVε hv
    have hxC : x ∈ C := ⟨xA,mem_of_mem_nhds hV,rfl⟩
    have hCc : IsPreconnected C := hVc.image _ continuous_subtype_val.continuousOn
    refine ⟨min r ε / 4,by positivity,?_⟩
    intro y hy hyx
    obtain ⟨a,ha,hea⟩ := hA.exists_infDist_eq_dist ⟨x,hxA⟩ y
    have hnear : ∀ b ∈ A, dist y a ≤ dist y b := by
      intro b hb
      rw [← hea]
      exact Metric.infDist_le_dist_of_mem hb
    have hya : dist y a ≤ dist y x := hnear x hxA
    have hax : dist a x < r := by
      have hh := dist_triangle a y x
      rw [dist_comm a y] at hh
      have hm := min_le_left r ε
      linarith
    have haC : a ∈ C := ⟨⟨a,ha⟩,hrV hax,rfl⟩
    have hyε : y ∈ Metric.ball x ε := by
      have hm := min_le_right r ε
      change dist y x < ε
      linarith
    let S := _root_.segment ℝ y a
    have hSK : S ⊆ K := nearest_segment_subset_filling hAK hfill hy ha hnear
    have hSε : S ⊆ Metric.ball x ε := (convex_ball x ε).segment_subset hyε (hCε haC)
    have hUc : IsPreconnected (C ∪ S) := hCc.union a haC (right_mem_segment ℝ y a) (convex_segment y a).isPreconnected
    exact hUc.subset_connectedComponentIn (F := K ∩ Metric.ball x ε) (Or.inl hxC)
      (union_subset (fun _ hz => ⟨hAK (hCA hz),hCε hz⟩)
        (fun _ hz => ⟨hSK hz,hSε hz⟩)) (Or.inr (left_mem_segment ℝ y a))
  · obtain ⟨r,hr,hrA⟩ := Metric.isOpen_iff.mp hA.isOpen_compl x hxA
    refine ⟨min r ε,lt_min hr hε,?_⟩
    intro y hy hyx
    let B := Metric.ball x (min r ε)
    have hxB : x ∈ B := Metric.mem_ball_self (lt_min hr hε)
    have hBA : B ⊆ Aᶜ := (Metric.ball_subset_ball (min_le_left _ _)).trans hrA
    have hBK : B ⊆ K := ((convex_ball x (min r ε)).isPreconnected.subset_connectedComponentIn
      hxB hBA).trans (hfill x hx)
    exact (convex_ball x (min r ε)).isPreconnected.subset_connectedComponentIn
      (F := K ∩ Metric.ball x ε) hxB
      (fun _ hz => ⟨hBK hz,(Metric.ball_subset_ball (min_le_right _ _)) hz⟩) hyx

theorem past_filled_locallyConnected {γ : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn γ (Icc 0 T)) :
    LocallyConnectedSpace (↑((localizationDomain γ T)ᶜ) : Type) := by
  have := past_obstacle_locallyConnected hT hc
  exact locallyConnected_filling
    (halfPlane_open.isClosed_compl.union (past_trace_continuum hT hc).1.isClosed)
    past_obstacle_subset_filled past_filled_component_closed

end SLEExactGauge

end

end OAI
