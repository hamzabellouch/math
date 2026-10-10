import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonical

namespace OAI

/-! Fixed-power finite continuation near a nonvanishing reference solution. -/

open Set Filter
namespace DefocusingNLS

theorem exists_radialExterior_fixed_continuation (n : ℕ) (ν : ℕ → ℂ) (μ : ℂ)
    (hν : Tendsto ν atTop (nhds μ)) (g : ℝ → ℂ × ℂ) (hg : Continuous g)
    (l u : ℝ) (hlu : l ≤ u)
    (hgn : ∀ t ∈ Icc l u, (g t).1 ≠ 0)
    (hgd : ∀ t ∈ Icc l u, HasDerivAt g (radialExteriorODEField μ n t (g t)) t)
    (x : ℕ → ℂ × ℂ) (hx : Tendsto x atTop (nhds (g u))) :
    ∃ X : ℕ → ℝ → ℂ × ℂ,
      (∀ i, Continuous (X i) ∧ X i u=x i) ∧
      TendstoUniformlyOn X g atTop (Icc l u) ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc l u, (X i t).1 ≠ 0 ∧
        HasDerivAt (X i) (radialExteriorODEField (ν i) n t (X i t)) t := by
  have hgc : Continuous (fun t => ‖(g t).1‖) := hg.fst.norm
  obtain ⟨t₀,ht₀,hmin⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_isMinOn
    (nonempty_Icc.mpr hlu) hgc.continuousOn
  let δ := ‖(g t₀).1‖/2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr (hgn t₀ ht₀))
  have hlow : ∀ t ∈ Icc l u, δ < ‖(g t).1‖ := by
    intro t ht
    have hh : ‖(g t₀).1‖ ≤ ‖(g t).1‖ := hmin ht
    dsimp [δ]
    linarith [norm_pos_iff.mpr (hgn t₀ ht₀)]
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_bound_of_continuousOn
    hg.fst.continuousOn
  let ρ := C+2*δ
  have hb : ∀ t ∈ Icc (u-(u-l)) u, ‖(g t).1‖+2*δ ≤ ρ := by
    intro t ht
    have ht' : t ∈ Icc l u := by simpa only [sub_sub_cancel] using ht
    exact add_le_add (hC t ht') le_rfl
  have hex (i : ℕ) := exists_radialExterior_clipped_finite (ν i) n (fun t => (g t).1)
    hg.fst δ ρ u (u-l) hδ.le (sub_nonneg.mpr hlu) hb (x i)
  choose X hXc hXu hXd using hex
  have hgd' : ∀ t ∈ Icc (u-(u-l)) u, HasDerivAt g
      (radialExteriorFiniteField μ n (fun r => (g r).1) δ t (g t)) t := by
    intro t ht
    rw [radialExteriorFiniteField_eq μ n (fun r => (g r).1) δ t (g t)
      (by simpa only [sub_self,norm_zero] using hδ.le)]
    exact hgd t (by simpa only [sub_sub_cancel] using ht)
  have hc := radialExterior_finite_parameter_limit n ν μ hν (fun t => (g t).1) hg.fst
    δ ρ u (u-l) hδ.le (sub_nonneg.mpr hlu) hb X g hXc hg hXd hgd'
    (by simpa only [hXu] using hx)
  have hc' : TendstoUniformlyOn X g atTop (Icc l u) := by
    simpa only [sub_sub_cancel] using hc
  refine ⟨X,fun i => ⟨hXc i,hXu i⟩,hc',?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hc') δ hδ] with i hi t ht
  have hd := hi t ht
  rw [dist_comm,dist_eq_norm] at hd
  have hfirst : ‖(X i t).1-(g t).1‖ < δ := (norm_fst_le (X i t-g t)).trans_lt hd
  refine ⟨?_,?_⟩
  · intro he
    rw [he,zero_sub,norm_neg] at hfirst
    exact ((hlow t ht).trans hfirst).false
  · have hh := hXd i t (by simpa only [sub_sub_cancel] using ht)
    rwa [radialExteriorFiniteField_eq (ν i) n (fun r => (g r).1) δ t (X i t) hfirst.le] at hh

end DefocusingNLS

end OAI
