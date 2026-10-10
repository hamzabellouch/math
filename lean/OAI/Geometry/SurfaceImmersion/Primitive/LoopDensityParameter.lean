import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityLinear

namespace OAI

/-! Smooth local positive solutions of the three density moment equations. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma augment_smooth : ContDiff ℝ ∞ augment := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun _ : Plane => (1 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    exact contDiff_apply ℝ ℝ 0
  · change ContDiff ℝ ∞ (fun x : Plane => x 1)
    exact contDiff_apply ℝ ℝ 1

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {p : B → ℝ → Plane} {c : B → Plane} {ψ : Fin 3 → ℝ → ℝ}

lemma background_smooth (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) :
    ContDiff ℝ ∞ (fun b => background (p b)) :=
  SmoothParameterIntegral.contDiff_integral (augment_smooth.comp hp) 0 1

lemma column_smooth (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (i : Fin 3) :
    ContDiff ℝ ∞ (fun b => column (p b) (ψ i)) :=
  SmoothParameterIntegral.contDiff_integral
    (((hψ i).comp contDiff_snd).smul (augment_smooth.comp hp)) 0 1

lemma momentMap_smooth (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (fun b => momentMap (p b) ψ) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smulRight (column_smooth hp hψ i)

lemma weights_smoothAt (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hc : ContDiff ℝ ∞ c) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    {b : B} (hM : (momentMap (p b) ψ).IsInvertible) (ε : ℝ) :
    ContDiffAt ℝ ∞ (fun x => weights (p x) ψ ε (c x)) b := by
  exact (hM.contDiffAt_map_inverse.comp b (momentMap_smooth hp hψ).contDiffAt).clm_apply
    (((augment_smooth.comp hc).sub ((background_smooth hp).const_smul ε)).contDiffAt)

lemma weights_smoothOn (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hc : ContDiff ℝ ∞ c) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    {U : Set B} (hM : ∀ b ∈ U, (momentMap (p b) ψ).IsInvertible) (ε : ℝ) :
    ContDiffOn ℝ ∞ (fun x => weights (p x) ψ ε (c x)) U :=
  fun b hb => (weights_smoothAt hp hc hψ (hM b hb) ε).contDiffWithinAt

/-- Positive weights and an invertible three-moment matrix persist locally;
this constructs an actual smooth positive density with the exact required mean. -/
theorem exists_positive_density_near
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) (hc : ContDiff ℝ ∞ c)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψnonneg : ∀ i t, 0 ≤ ψ i t)
    (hψper : ∀ i, Function.Periodic (ψ i) 1)
    {b₀ : B} {ε : ℝ} (hε : 0 < ε) (hM : (momentMap (p b₀) ψ).IsInvertible)
    (hw : ∀ i, 0 < weights (p b₀) ψ ε (c b₀) i) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ Set.univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b) := by
  have hmNear : ∀ᶠ b in 𝓝 b₀, (momentMap (p b) ψ).IsInvertible :=
    (momentMap_smooth hp hψ).continuous.continuousAt.eventually hM.eventually_nhds
  have hwAt := (weights_smoothAt hp hc hψ hM ε).continuousAt
  have hwNear : ∀ᶠ b in 𝓝 b₀, ∀ i, 0 < weights (p b) ψ ε (c b) i := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply i).continuousAt.comp hwAt).eventually_const_lt (hw i)
  obtain ⟨U, hUsub, hU, hb₀⟩ := mem_nhds_iff.mp (hmNear.and hwNear)
  let ρ : B × ℝ → ℝ := fun z => density ε ψ (weights (p z.1) ψ ε (c z.1)) z.2
  have hweights := weights_smoothOn hp hc hψ (fun b hb => (hUsub hb).1) ε
  refine ⟨U, hU, hb₀, ρ, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_const.add
    apply ContDiffOn.sum
    intro i _
    have hwi : ContDiffOn ℝ ∞
        (fun z : B × ℝ => weights (p z.1) ψ ε (c z.1) i) (U ×ˢ Set.univ) :=
      ((contDiff_apply ℝ ℝ i).comp_contDiffOn hweights).comp contDiffOn_fst
        (fun _ hz => hz.1)
    exact hwi.mul ((hψ i).comp contDiff_snd).contDiffOn
  · intro b hb t
    exact density_pos hε hψnonneg (fun i => ((hUsub hb).2 i).le) t
  · intro b
    exact density_periodic ε ψ (weights (p b) ψ ε (c b)) hψper
  · intro b hb
    exact solved_moments
      (hp.continuous.comp (continuous_const.prodMk continuous_id))
      (fun i => (hψ i).continuous) (hUsub hb).1 ε (c b)

end ClosedSurfaceR4.LoopDensity

end

end OAI
