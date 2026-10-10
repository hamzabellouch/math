import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedTail
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalFinite

namespace OAI

/-! The published small-line formula equals the actual far-left series.
Every contour change is proved for the literal transform before summing. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticTransform_line_eq (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ A v : ℝ} (hσ : 0 < σ) (hA : σ ≤ A)
    (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    metaplecticTransform ℓ W σ v = metaplecticTransform ℓ W A v := by
  have he := metaplectic_transform_contour ℓ W hW hpos hsm
    (a := -A) (b := -σ) (by linarith) (by linarith) hv hm hp
  exact (congrArg (fun z : ℂ => ((1/(2*Real.pi):ℝ):ℂ)*z) he).symm

lemma metaplecticDualNorm_eq (nd : MetaplecticDualArgument × PrimaryArgument) :
    Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1) =
      metaplecticDualNorm nd := by
  rw [Complex.normSq_mul,map_pow]
  rfl

lemma metaplecticDualTerm_line_eq
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ A X : ℝ} (hσ : 0 < σ) (hA : σ ≤ A) (hX : 0 < X)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticDualTerm a r ℓ W σ X nd = metaplecticDualTerm a r ℓ W A X nd := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hD := metaplecticDualNorm_pos nd
  have hv : 0 < (2*Real.pi)^4*
      Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1)*X/(norm r)^2 := by
    rw [metaplecticDualNorm_eq]
    positivity
  unfold metaplecticDualTerm
  rw [metaplecticTransform_line_eq ℓ W hW hpos hsm hσ hA hv hm hp]

/-- Exact far-left Voronoi identity for the original norm-twisted
completed sum. Absolute convergence follows from the published small
line and the proved termwise contour identity. -/
theorem metaplectic_height_voronoi_far_line
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hs : Squarefree r) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X σ A : ℝ} (hX : 0 < X) (hσ : 0 < σ)
    (hσs : σ < 1/10000) (hA : σ ≤ A)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) (t : ℝ) :
    Summable (metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X) ∧
    metaplecticHeightCompleted r ℓ W X t = mellinPhase t X*
      (metaplecticMain r ℓ (fun x => W x*mellinPhase t x) X+
        metaplecticPrefactor r ℓ*∑' nd,
          metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd) := by
  have hWt := phaseWeight_compact hW t
  have hPt := phaseWeight_positive hpos t
  have hSt := phaseWeight_smooth hpos hsm t
  have hfun : metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) σ X =
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X := by
    funext nd
    exact metaplecticDualTerm_line_eq a hr ℓ _ hWt hPt hSt hσ hA hX hm hp nd
  have hsum := (hV.2 r hr hs ℓ _ hWt hPt hSt X hX σ hσ hσs).1
  have he := metaplectic_angular_voronoi hV hr hs ℓ _ hWt hPt hSt hX hσ hσs
  rw [hfun] at hsum he
  refine ⟨hsum,?_⟩
  rw [metaplecticHeightCompleted_twist r ℓ W hX t,he]

end CubicFirstMoment

end

end OAI
