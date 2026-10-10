import OAI.Probability.GammaPassage.NoCornerContradiction
import OAI.Probability.GammaPassage.ActualTimeConstant
import OAI.Probability.GammaPassage.AnalyticSpecialization

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open MeasureTheory Filter
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- The actual time constant along the manuscript's rounded direction sequence. -/
lemma gamma_direction_nat_limit (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ))
      atTop (𝓝 ((gammaMeanNorm henv hshape hrate) (direction b))) := by
  filter_upwards [henv.isTimeConstant hshape hrate (direction b)] with ω hω
  have hh := hω.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he (n : ℕ) : latticeFloor ((n : ℝ) • direction b)=((n : ℤ),⌊b*(n : ℝ)⌋) := by
    simp [latticeFloor,direction,PiLp.smul_apply,mul_comm]
  simpa only [Function.comp_def,he,show (0 : Vertex)=(0,0) from rfl] using hh

theorem gamma_no_corner (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) (hb : |b| ≤ 1) :
    extremeSlope (gammaMeanNorm henv hshape hrate) b false=extremeSlope (gammaMeanNorm henv hshape hrate) b true := by
  let _ := henv.probability
  let μ := (gammaMeanNorm henv hshape hrate)
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  have horder : am ≤ ap := by
    exact extreme_slopes_ordered _ (convex_transverse_profile μ (direction b) transverseUnit
      (gammaMeanNorm_laws henv hshape hrate).triangle (norm_positive_homogeneous μ (gammaMeanNorm_laws henv hshape hrate)))
  change am=ap
  by_contra hneq
  have hgap0 : 0 < (ap-am)/8 := by have hh := lt_of_le_of_ne horder hneq; linarith
  let η := min 1 ((ap-am)/8)
  have hη : 0 < η := lt_min (by norm_num) hgap0
  have hη1 : η ≤ 1 := min_le_left ..
  have hgap : 4*η ≤ (ap-am)/2 := by have hh := min_le_right (1 : ℝ) ((ap-am)/8); nlinarith
  obtain ⟨k,m,hs,hstep,hscale₁,hscale₂,hBK⟩ := gamma_witness_scale henv hshape hrate b η hb hη hη1
  have hlong := ae_eventually_spatial_long_paths henv hshape hrate b (μ (direction b)) am ap (sourceCrossingK shape rate μ b) η
    ((1 : ℝ)/1024) hb horder hη (by norm_num) (by norm_num) (by norm_num)
    hgap k m hs hstep hscale₁ hscale₂ hBK
  obtain ⟨ω,hp,hl,hh⟩ := (henv.ae_positive.and ((gamma_direction_nat_limit henv hshape hrate b).and hlong)).exists
  exact long_paths_contradict_directional_limit (fun e => τ e ω) (fun e => (hp e).le)
    b (μ (direction b)) ((am+ap)/2) η hb hη k m hl hh

/-- The Gamma mean norm is Fréchet differentiable in every direction
`(1, b)` with `|b| ≤ 1`. -/
theorem gamma_direction_differentiable (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) (hb : |b| ≤ 1) :
    DifferentiableAt ℝ (gammaMeanNorm henv hshape hrate) (direction b) := by
  obtain ⟨ℓ,hℓ⟩ := planar_differentiability_of_no_corner (gammaMeanNorm henv hshape hrate) (gammaMeanNorm_laws henv hshape hrate) b
    (gamma_no_corner henv hshape hrate b hb)
  exact hℓ.differentiableAt

end GammaFPP.CrossingBridge

end OAI
