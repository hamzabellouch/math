import OAI.Geometry.SurfaceImmersion.Whitney.RulingDirectionJet

namespace OAI

/-! Differential formulas for the actual straight-line homotopy of maps. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def linearMapHomotopy (f g : E → V) (t : ℝ) (x : E) : V := (1-t) • f x + t • g x

lemma linearMapHomotopy_smooth {f g : E → V} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (t : ℝ) : ContDiff ℝ ∞ (linearMapHomotopy f g t) :=
  (hf.const_smul _).add (hg.const_smul _)

lemma linearMapHomotopy_fderiv {f g : E → V} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (t : ℝ) (x : E) :
    fderiv ℝ (linearMapHomotopy f g t) x =
      (1-t) • fderiv ℝ f x + t • fderiv ℝ g x := by
  exact (((hf.differentiable (by simp) x).hasFDerivAt.const_smul (1-t)).add
    ((hg.differentiable (by simp) x).hasFDerivAt.const_smul t)).fderiv

lemma linearMapHomotopy_fderiv_continuous {f g : E → V} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    Continuous (fun z : ℝ × E => fderiv ℝ (linearMapHomotopy f g z.1) z.2) := by
  have he : (fun z : ℝ × E => fderiv ℝ (linearMapHomotopy f g z.1) z.2) =
      (fun z => (1-z.1) • fderiv ℝ f z.2 + z.1 • fderiv ℝ g z.2) :=
    funext fun z => linearMapHomotopy_fderiv hf hg _ _
  rw [he]
  exact ((continuous_const.sub continuous_fst).smul
    ((hf.continuous_fderiv (by simp)).comp continuous_snd)).add
      (continuous_fst.smul ((hg.continuous_fderiv (by simp)).comp continuous_snd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma linearMapHomotopy_fix {f g : E → V} {x : E} (h : g x = f x) (t : ℝ) :
    linearMapHomotopy f g t x = f x := by
  unfold linearMapHomotopy
  rw [h,← add_smul]
  simp

lemma linearMapHomotopy_direction {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) (b : Bool) :
    surfaceDirection (linearMapHomotopy f g t) b =
      linearMapHomotopy (surfaceDirection f b) (surfaceDirection g b) t := by
  funext z
  rw [surfaceDirection,linearMapHomotopy_fderiv hf hg]
  simp [linearMapHomotopy,surfaceDirection]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
