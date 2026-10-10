import OAI.Probability.FirstPassage.NoCornerContradiction

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_direction_nat_limit (henv : ExponentialEnvironment P τ) (b : ℝ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ))
      atTop (𝓝 (actualSourceTimeConstant (direction b))) := by
  filter_upwards [actualSourceTimeConstant_isTimeConstant henv (direction b)] with ω hω
  have hh := hω.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he (n : ℕ) : latticeFloor ((n : ℝ) • direction b)=((n : ℤ),⌊b*(n : ℝ)⌋) := by
    simp [latticeFloor,direction,PiLp.smul_apply,mul_comm]
  simpa only [Function.comp_def,he,show (0 : Vertex)=(0,0) from rfl] using hh

theorem actual_no_corner (henv : ExponentialEnvironment P τ) (b : ℝ) (hb : |b| ≤ 1) :
    extremeSlope actualSourceTimeConstant b false=extremeSlope actualSourceTimeConstant b true := by
  let _ := henv.probability
  let μ := actualSourceTimeConstant
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  have horder : am ≤ ap := by
    exact extreme_slopes_ordered _ (convex_transverse_profile μ (direction b) transverseUnit
      actualSourceTimeConstant_norm.triangle (norm_positive_homogeneous μ actualSourceTimeConstant_norm))
  change am=ap
  by_contra hneq
  have hgap0 : 0 < (ap-am)/8 := by have hh := lt_of_le_of_ne horder hneq; linarith
  let η := min 1 ((ap-am)/8)
  have hη : 0 < η := lt_min (by norm_num) hgap0
  have hη1 : η ≤ 1 := min_le_left ..
  have hgap : 4*η ≤ (ap-am)/2 := by have hh := min_le_right (1 : ℝ) ((ap-am)/8); nlinarith
  obtain ⟨k,m,hs,hstep,hscale₁,hscale₂,hBK⟩ := actual_witness_scale henv b η hb hη hη1
  have hlong := ae_eventually_spatial_long_paths henv b (μ (direction b)) am ap (sourceCrossingK μ b) η
    ((1 : ℝ)/1024) hb horder hη (by norm_num) (by norm_num) (by norm_num)
    hgap k m hs hstep hscale₁ hscale₂ hBK
  obtain ⟨ω,hp,hl,hh⟩ := (henv.ae_positive.and ((actual_direction_nat_limit henv b).and hlong)).exists
  exact long_paths_contradict_directional_limit (fun e => τ e ω) (fun e => (hp e).le)
    b (μ (direction b)) ((am+ap)/2) η hb hη k m hl hh

theorem actual_direction_differentiable (henv : ExponentialEnvironment P τ) (b : ℝ) (hb : |b| ≤ 1) :
    DifferentiableAt ℝ actualSourceTimeConstant (direction b) := by
  obtain ⟨ℓ,hℓ⟩ := planar_differentiability_of_no_corner actualSourceTimeConstant actualSourceTimeConstant_norm b
    (actual_no_corner henv b hb)
  exact hℓ.differentiableAt

end PlanarFPP

end OAI
