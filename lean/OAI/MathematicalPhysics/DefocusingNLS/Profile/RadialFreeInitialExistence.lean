import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeInitialField

namespace OAI

/-! A bounded integral solution of the free initial-value problem on the manuscript's short shell. -/

open Set Metric MeasureTheory ODE
namespace DefocusingNLS

theorem exists_radial_free_initial (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ)) :
    ∃ X : ℝ → ℂ × ℂ, Continuous X ∧ X l=(1,0) ∧
      (∀ r ∈ Icc l u, X r=(1,0)+∫ t in l..r, radialFreeField b t (X t)) ∧
      (∀ r, ‖X r‖ ≤ 2) := by
  let t₀ : Icc l u := ⟨l,le_rfl,hlu⟩
  let x₀ : ℂ × ℂ := (1,0)
  have hX : ∀ x ∈ closedBall x₀ 1, ‖x‖ ≤ (2 : ℝ) := by
    intro x hx
    have hd : ‖x-x₀‖ ≤ 1 := mem_closedBall_iff_norm.mp hx
    calc
      ‖x‖ = ‖(x-x₀)+x₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-x₀‖+‖x₀‖ := norm_add_le _ _
      _ ≤ 2 := by norm_num [x₀] at hd ⊢; linarith
  have hPL : IsPicardLindelof (radialFreeField b) t₀ x₀ 1 0 14 7 := by
    constructor
    · intro t ht
      exact (radialFreeField_lipschitz b t hb ⟨hl.trans ht.1,ht.2.trans hu⟩).lipschitzOnWith
    · intro x _
      exact radialFreeField_continuousOn b l u (by linarith) x
    · intro t ht x hx
      exact (radialFreeField_norm b t hb ⟨hl.trans ht.1,ht.2.trans hu⟩ x).trans (by
        have hh := hX x hx
        change 7*‖x‖ ≤ (14 : ℝ)
        linarith)
    · change (14 : ℝ)*max (u-l) (l-l) ≤ 1-0
      rw [sub_self,max_eq_left (sub_nonneg.mpr hlu)]
      linarith
  have hx : x₀ ∈ closedBall x₀ (0 : NNReal) := mem_closedBall_self le_rfl
  obtain ⟨α,hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL hx
  have he : ∀ r ∈ Icc l u, α.compProj r=ODE.picard (radialFreeField b) l x₀ α.compProj r := by
    intro r hr
    rw [ODE.FunSpace.compProj_of_mem hr]
    exact (ODE.FunSpace.isFixedPt_next_iff hPL hx).mp hα ⟨r,hr⟩
  refine ⟨α.compProj,α.continuous_compProj,?_,?_,?_⟩
  · simpa only [ODE.picard_apply,intervalIntegral.integral_same,add_zero] using he l ⟨le_rfl,hlu⟩
  · intro r hr
    exact he r hr
  · intro r
    exact hX (α.compProj r) (α.compProj_mem_closedBall hPL.mul_max_le)

end DefocusingNLS

end OAI
