import Mathlib
import OAI.Analysis.Crouzeix.BoundaryChart

namespace OAI

/-! Boundary Patching. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem extension_eqOn_lens {U : Set ℂ} (hU : IsOpen U) {f g₁ g₂ : ℂ → ℂ}
    {p q : ℂ} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hg₁ : AnalyticOnNhd ℂ g₁ (ball p r)) (hg₂ : AnalyticOnNhd ℂ g₂ (ball q s))
    (he₁ : EqOn g₁ f (U ∩ ball p r)) (he₂ : EqOn g₂ f (U ∩ ball q s))
    (hover : (ball p (r / 3) ∩ ball q (s / 3)).Nonempty) :
    EqOn g₁ g₂ (ball p r ∩ ball q s) := by
  let L := ball p r ∩ ball q s
  have hL : IsOpen L := isOpen_ball.inter isOpen_ball
  have hLU : (L ∩ U).Nonempty := by
    obtain ⟨z, hzp, hzq⟩ := hover
    have hpq : dist p q < (r + s) / 3 := by
      have h := dist_triangle p z q
      rw [dist_comm p z] at h
      have := mem_ball.mp hzp
      have := mem_ball.mp hzq
      linarith
    rcases le_total s r with hsr | hrs
    · have hqL : q ∈ L := ⟨by rw [mem_ball, dist_comm]; linarith, mem_ball_self hs⟩
      exact (mem_closure_iff_nhds.mp hq) L (hL.mem_nhds hqL)
    · have hpL : p ∈ L := ⟨mem_ball_self hr, by rw [mem_ball]; linarith⟩
      exact (mem_closure_iff_nhds.mp hp) L (hL.mem_nhds hpL)
  obtain ⟨z, hzL, hzU⟩ := hLU
  apply (hg₁.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hg₂.mono inter_subset_right) ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected hzL
  filter_upwards [(hL.inter hU).mem_nhds ⟨hzL, hzU⟩] with w hw
  exact (he₁ ⟨hw.2, hw.1.1⟩).trans (he₂ ⟨hw.2, hw.1.2⟩).symm

theorem exists_extension_to_closure {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ g V ∧ EqOn g f U ∧
      (∀ p ∈ closure U, deriv g p ≠ 0) ∧ (∀ p ∈ frontier U, ‖g p‖ = 1) := by
  have hl : ∀ p : frontier U, ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      AnalyticOnNhd ℂ g (ball (p : ℂ) r) ∧ EqOn g f (U ∩ ball (p : ℂ) r) ∧ deriv g p ≠ 0 :=
    fun p => exists_extension_at_boundary hU hf hbij p.property (hchart p p.property).some
  choose r G hr hGa hGe hGd using hl
  let B : frontier U → Set ℂ := fun p => ball (p : ℂ) (r p / 3)
  have hBsub : ∀ p, B p ⊆ ball (p : ℂ) (r p) := fun p =>
    ball_subset_ball (by have := hr p; linarith)
  let V := U ∪ ⋃ p, B p
  let g : ℂ → ℂ := fun z => if z ∈ U then f z else
    if h : ∃ p : frontier U, z ∈ B p then G h.choose z else 0
  have hgu : EqOn g f U := by intro z hz; simp only [g, ite_eq_left hz]
  have hgb : ∀ p, EqOn g (G p) (B p) := by
    intro p z hz
    by_cases hzu : z ∈ U
    · exact (hgu hzu).trans (hGe p ⟨hzu, hBsub p hz⟩).symm
    · have h : ∃ q : frontier U, z ∈ B q := ⟨p, hz⟩
      simp only [g, ite_eq_right hzu, dite_eq_left h]
      exact extension_eqOn_lens hU h.choose.property.1 p.property.1
        (hr h.choose) (hr p) (hGa h.choose) (hGa p) (hGe h.choose) (hGe p)
        ⟨z, h.choose_spec, hz⟩ ⟨hBsub h.choose h.choose_spec, hBsub p hz⟩
  have hVo : IsOpen V := hU.union (isOpen_iUnion (fun _ => isOpen_ball))
  have hUV : closure U ⊆ V := by
    intro z hz
    by_cases hzu : z ∈ U
    · exact Or.inl hzu
    · let p : frontier U := ⟨z, hz, by simpa only [hU.interior_eq] using hzu⟩
      exact Or.inr (mem_iUnion.mpr ⟨p, mem_ball_self (by have := hr p; positivity)⟩)
  have hga : AnalyticOnNhd ℂ g V := by
    intro z hz
    rcases hz with hzU | hzB
    · exact ((hf.analyticOnNhd hU) z hzU).congr
        (hgu.eventuallyEq_of_mem (hU.mem_nhds hzU)).symm
    · obtain ⟨p, hp⟩ := mem_iUnion.mp hzB
      exact (hGa p z (hBsub p hp)).congr
        ((hgb p).eventuallyEq_of_mem (isOpen_ball.mem_nhds hp)).symm
  refine ⟨V, g, hVo, hUV, hga, hgu, ?_, ?_⟩
  · intro z hz
    by_cases hzU : z ∈ U
    · rw [(hgu.eventuallyEq_of_mem (hU.mem_nhds hzU)).deriv_eq]
      exact deriv_ne_zero_of_injOn hU hf hbij.injOn hzU
    · let p : frontier U := ⟨z, hz, by simpa only [hU.interior_eq] using hzU⟩
      have hn : B p ∈ 𝓝 z := ball_mem_nhds z (by have := hr p; positivity)
      rw [((hgb p).eventuallyEq_of_mem hn).deriv_eq]
      exact hGd p
  · intro p hp
    have : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp.1
    apply tendsto_nhds_unique ((hga p (hUV hp.1)).continuousAt.norm.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[U] p ≤ 𝓝 p))
    apply (tendsto_norm_one_at_frontier hU hf hbij hp).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact congrArg norm (hgu hz).symm

end CrouzeixHilbert.Conformal

end

end OAI
