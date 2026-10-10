import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityParameter
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicBumpAverage

namespace OAI

/-! Replace three nondegenerate point masses by smooth positive-density data. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.LoopDensity

abbrev Columns := Fin 3 → Moments

def columnOperator (C : Columns) : Moments →L[ℝ] Moments :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (C i)

lemma columnOperator_smooth : ContDiff ℝ ∞ columnOperator := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smulRight (contDiff_apply ℝ Moments i)

lemma momentMap_eq_columnOperator (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) :
    momentMap p ψ = columnOperator (fun i => column p (ψ i)) := rfl

/-- A strictly positive, nondegenerate three-point barycenter can be replaced
by smooth nonnegative periodic bumps and a strictly positive constant density. -/
theorem select_positive_moment_bumps {p : ℝ → Plane} (hp : Continuous p)
    {t : Fin 3 → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    {c : Plane} {w : Moments}
    (hM : (columnOperator (fun i => augment (p (t i)))).IsInvertible)
    (hw : ∀ i, 0 < w i)
    (hbary : columnOperator (fun i => augment (p (t i))) w = augment c) :
    ∃ ψ : Fin 3 → ℝ → ℝ, (∀ i, ContDiff ℝ ∞ (ψ i)) ∧
      (∀ i, Function.Periodic (ψ i) 1) ∧ (∀ i x, 0 ≤ ψ i x) ∧
      (∀ i, (∫ x in 0..1, ψ i x) = 1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (momentMap p ψ).IsInvertible ∧
        ∀ i, 0 < weights p ψ ε c i := by
  let C₀ : Columns := fun i => augment (p (t i))
  let W : Columns × ℝ → Moments := fun z =>
    (columnOperator z.1).inverse (augment c - z.2 • background p)
  have hsource : ContDiff ℝ ∞ (fun z : Columns × ℝ => augment c - z.2 • background p) :=
    contDiff_const.sub (contDiff_snd.smul contDiff_const)
  have hi : ContDiffAt ℝ ∞ (fun z : Columns × ℝ => (columnOperator z.1).inverse) (C₀, 0) :=
    hM.contDiffAt_map_inverse.comp (C₀, 0)
      (columnOperator_smooth.comp contDiff_fst).contDiffAt
  have hW : ContDiffAt ℝ ∞ W (C₀, 0) := hi.clm_apply hsource.contDiffAt
  have hW₀ : W (C₀, 0) = w := by
    change (columnOperator C₀).inverse (augment c - (0 : ℝ) • background p) = w
    rw [zero_smul, sub_zero, ← hbary, hM.inverse_apply_self]
  have hnearM : ∀ᶠ z : Columns × ℝ in 𝓝 (C₀, 0), (columnOperator z.1).IsInvertible :=
    (columnOperator_smooth.comp contDiff_fst).continuous.continuousAt.eventually hM.eventually_nhds
  have hnearW : ∀ᶠ z : Columns × ℝ in 𝓝 (C₀, 0), ∀ i, 0 < W z i := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply i).continuousAt.comp hW.continuousAt).eventually_const_lt
      (by change 0 < W (C₀, 0) i; rw [hW₀]; exact hw i)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hnearM.and hnearW)
  have hchoose (i : Fin 3) := exists_bump_average_near (augment_continuous.comp hp) (ht i) hδ
  choose ψ hψ hper hn hm hclose using hchoose
  let C : Columns := fun i => column p (ψ i)
  have hC : ‖C - C₀‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    exact hclose i
  have hz : (C, δ / 2) ∈ ball (C₀, 0) δ := by
    rw [mem_ball, Prod.dist_eq]
    apply max_lt
    · simpa only [dist_eq_norm] using hC
    · rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
      linarith
  have hgood := hball hz
  exact ⟨ψ, hψ, hper, hn, hm, δ / 2, by positivity, hgood.1, hgood.2⟩

end ClosedSurfaceR4.LoopDensity

end

end OAI
