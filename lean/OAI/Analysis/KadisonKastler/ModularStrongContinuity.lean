import OAI.Analysis.KadisonKastler.ModularStrongLimit

namespace OAI

/-! # Strong continuity of the limiting modular group

The cutoff error is bounded by `|t| ε ‖x‖`. At time zero this proves
continuity on the dense cutoff range using just one bounded approximation.
Contraction bounds and the group law give continuity on the whole space.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H] {M : VonNeumannAlgebra H}

theorem modularApproximation_limit_cutoff_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (n : ℕ) (t : ℝ) (x : H) :
    ‖modularApproximation M J Ω n t (graphResolventCutoff M J Ω x) -
      modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω x)‖ ≤
        |t| * modularRegularizationScale n * ‖x‖ := by
  have hc : Tendsto (fun _ : ℕ => modularApproximation M J Ω n t
      (graphResolventCutoff M J Ω x)) atTop
      (𝓝 (modularApproximation M J Ω n t (graphResolventCutoff M J Ω x))) := tendsto_const_nhds
  have hl := (hc.sub
    (modularApproximation_tendsto J Ω hsep hcyc t (graphResolventCutoff M J Ω x))).norm
  have hr : Tendsto (fun m => |t| * |modularRegularizationScale n -
      modularRegularizationScale m| * ‖x‖) atTop
      (𝓝 (|t| * modularRegularizationScale n * ‖x‖)) := by
    have hc : Tendsto (fun _ : ℕ => modularRegularizationScale n) atTop
        (𝓝 (modularRegularizationScale n)) := tendsto_const_nhds
    simpa only [sub_zero, abs_of_pos (modularRegularizationScale_pos n)] using
      ((hc.sub modularRegularizationScale_tendsto).abs.const_mul |t|).mul_const ‖x‖
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun m =>
    regularizedModularGroup_cutoff_apply_bound J Ω t (modularRegularizationScale_pos n)
      (modularRegularizationScale_pos m) x)

theorem modularStrongLimit_cutoff_tendsto_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Tendsto (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t
      (graphResolventCutoff M J Ω x)) (𝓝 0) (𝓝 (graphResolventCutoff M J Ω x)) := by
  let y := graphResolventCutoff M J Ω x
  have happ : Tendsto (fun t : ℝ => modularApproximation M J Ω 0 t y) (𝓝 0) (𝓝 y) := by
    have ht := (regularizedModularGroup_stronglyContinuous M J Ω
      (modularRegularizationScale 0) y).tendsto 0
    have he : regularizedModularGroup M J Ω (modularRegularizationScale 0)
        (Multiplicative.ofAdd 0) = 1 := map_one _
    rw [he] at ht
    exact ht
  have herr : Tendsto (fun t : ℝ => |t| * modularRegularizationScale 0 * ‖x‖)
      (𝓝 0) (𝓝 0) := by
    simpa using (((continuous_id : Continuous (fun t : ℝ => t)).abs.tendsto 0).mul_const
      (modularRegularizationScale 0)).mul_const ‖x‖
  have hz : Tendsto (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t y - y)
      (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm (fun t => ?_) (by
      simpa only [zero_add, sub_self, norm_zero] using herr.add (happ.sub_const y).norm)
    calc
      _ ≤ ‖modularStrongLimit J Ω hsep hcyc t y - modularApproximation M J Ω 0 t y‖ +
          ‖modularApproximation M J Ω 0 t y - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |t| * modularRegularizationScale 0 * ‖x‖ +
          ‖modularApproximation M J Ω 0 t y - y‖ := by
        rw [norm_sub_rev (modularStrongLimit J Ω hsep hcyc t y)]
        exact add_le_add (modularApproximation_limit_cutoff_bound J Ω hsep hcyc 0 t x) le_rfl
  simpa only [sub_add_cancel, zero_add] using hz.add_const y

theorem modularStrongLimit_tendsto_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Tendsto (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t x) (𝓝 0) (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy⟩ := (graphResolventCutoff_dense J Ω hsep hcyc).exists_dist_lt x
    (by positivity : 0 < ε / 4)
  filter_upwards [(Metric.tendsto_nhds.mp
    (modularStrongLimit_cutoff_tendsto_zero J Ω hsep hcyc y)) (ε / 2) (by positivity)] with t ht
  have hc : dist (modularStrongLimit J Ω hsep hcyc t x)
      (modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω y)) ≤
      dist x (graphResolventCutoff M J Ω y) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    rw [modularStrongLimit_norm_map]
  have hb := (dist_triangle (modularStrongLimit J Ω hsep hcyc t x)
    (modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω y)) x).trans
      (add_le_add le_rfl (dist_triangle
        (modularStrongLimit J Ω hsep hcyc t (graphResolventCutoff M J Ω y))
          (graphResolventCutoff M J Ω y) x))
  rw [dist_comm (graphResolventCutoff M J Ω y) x] at hb
  linarith

theorem modularStrongLimit_continuous (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Continuous (fun t : ℝ => modularStrongLimit J Ω hsep hcyc t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hsub : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := by fun_prop
    simpa only [sub_self] using hc.tendsto t
  have hz := (modularStrongLimit_tendsto_zero J Ω hsep hcyc x).comp hsub
  have ht := (modularStrongLimit J Ω hsep hcyc t).continuous.continuousAt.tendsto.comp hz
  change Tendsto (fun s : ℝ => modularStrongLimit J Ω hsep hcyc s x)
    (𝓝 t) (𝓝 (modularStrongLimit J Ω hsep hcyc t x))
  convert ht using 1
  funext s
  change modularStrongLimit J Ω hsep hcyc s x =
    (modularStrongLimit J Ω hsep hcyc t * modularStrongLimit J Ω hsep hcyc (s - t)) x
  rw [← modularStrongLimit_add, show t + (s - t) = s by ring]

theorem modularStrongGroup_continuous (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    Continuous (fun t : ℝ =>
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x) :=
  modularStrongLimit_continuous J Ω hsep hcyc x

end

end KadisonKastler

end OAI
