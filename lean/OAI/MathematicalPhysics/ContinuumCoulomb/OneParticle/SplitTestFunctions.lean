import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitSpectralBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarMultiwellProjection

namespace OAI

/-! Classical test functions in split coordinates: compact slices and
their exact directional derivatives. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem compact_planar_slice {f : SplitPosition → ℝ} (hc : HasCompactSupport f) (z : ℝ) :
    HasCompactSupport (fun r => f (r,z)) := by
  have hK := hc.image (continuous_fst : Continuous (Prod.fst : SplitPosition → PlanarPosition))
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro r hr
  exact ⟨(r,z),subset_tsupport f hr,rfl⟩

theorem compact_vertical_slice {f : SplitPosition → ℝ} (hc : HasCompactSupport f) (r : PlanarPosition) :
    HasCompactSupport (fun z => f (r,z)) := by
  have hK := hc.image (continuous_snd : Continuous (Prod.snd : SplitPosition → ℝ))
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro z hz
  exact ⟨(r,z),subset_tsupport f hz,rfl⟩

def splitPlanarPartial (f : SplitPosition → ℝ) (a : Fin 2) (p : SplitPosition) : ℝ :=
  fderiv ℝ f p (planarAxis a,0)

def splitVerticalPartial (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  fderiv ℝ f p (0,1)

theorem splitPlanarPartial_eq {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (a : Fin 2) (r : PlanarPosition) (z : ℝ) :
    planarPartial (fun s => f (s,z)) (planarAxis a) r = splitPlanarPartial f a (r,z) := by
  have h := ((hf.differentiable (by norm_num)) (r,z)).hasFDerivAt.comp r
    ((hasFDerivAt_id (𝕜 := ℝ) r).prodMk (hasFDerivAt_const z r))
  unfold planarPartial splitPlanarPartial
  have he := congrArg (fun L => L (planarAxis a)) h.fderiv
  exact he

theorem splitVerticalPartial_eq {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (r : PlanarPosition) (z : ℝ) :
    deriv (fun s => f (r,s)) z = splitVerticalPartial f (r,z) := by
  have h := ((hf.differentiable (by norm_num)) (r,z)).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z r).prodMk (hasDerivAt_id z))
  exact h.deriv

theorem compact_directional_square_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (e : E) :
    Integrable (fun x => (fderiv ℝ f x e)^2) μ := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have he : Continuous (fun x => fderiv ℝ f x e) := hd.clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ f x e) := hc.fderiv_apply ℝ e
  exact (he.memLp_of_hasCompactSupport hs (p := 2) (μ := μ)).integrable_sq

theorem splitPlanarPartial_square_integrable {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (a : Fin 2) :
    Integrable (fun p => (splitPlanarPartial f a p)^2) :=
  compact_directional_square_integrable volume hf hc (planarAxis a,0)

theorem splitVerticalPartial_square_integrable {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun p => (splitVerticalPartial f p)^2) :=
  compact_directional_square_integrable volume hf hc (0,1)

end ContinuumCoulomb

end

end OAI
