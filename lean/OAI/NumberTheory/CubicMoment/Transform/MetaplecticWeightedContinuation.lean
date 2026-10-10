import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRegularMellin
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPoleCutoff
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticScaleMellin

namespace OAI

/-! A holomorphic regular part for the completed Dirichlet series
multiplied by the Mellin transform of any compact smooth test function.
It is constructed from the literal Voronoi asymptotic. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticWeightedRegular (r : Eisenstein) (W : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin (metaplecticRegularScale r W) (-s)+
    metaplecticCompletedResidue r*mellin W (5/6)*mellin metaplecticPoleCorrection (-s)

lemma metaplecticWeightedRegular_differentiableOn
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    DifferentiableOn ℂ (metaplecticWeightedRegular r W) {s : ℂ | 0 < s.re} :=
  (metaplecticRegularMellin_differentiableOn hV hr hsr W hW hpos hsm).add
    ((metaplecticPoleCorrection_mellin_entire.comp differentiable_neg).const_mul _).differentiableOn

theorem metaplecticWeightedRegular_eq
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {s : ℂ} (hs : 1 < s.re) :
    mellin W s*(metaplecticCompletionEuler r s*metaplecticGaussSeries r s) =
      metaplecticWeightedRegular r W s+
        (metaplecticCompletedResidue r*mellin W (5/6))/(s-5/6) := by
  let P : ℝ → ℂ := (Ioi (1:ℝ)).indicator (fun x => ((x^(5/6:ℝ):ℝ):ℂ))
  let C := metaplecticCompletedResidue r*mellin W (5/6)
  have hR := metaplecticRegularMellin_convergent hV hr hsr W hW hpos hsm
    (s := s) (by linarith)
  have hP : MellinConvergent P (-s) := metaplecticSharpPole_mellin_convergent (by linarith)
  have hC := metaplecticPoleCorrection_mellin_convergent (-s)
  have hsum := hasMellin_add hC hP
  have hscaled := hsum.1.const_smul C
  have htotal := hasMellin_add hR hscaled
  have he : metaplecticCompleted r 0 W = fun x =>
      metaplecticRegularScale r W x+C*(metaplecticPoleCorrection x+P x) := by
    funext x
    dsimp only [metaplecticRegularScale,metaplecticPoleCorrection,C,P]
    ring
  have hconst := mellin_const_smul (fun x => metaplecticPoleCorrection x+P x) (-s) C
  simp only [smul_eq_mul] at htotal hconst
  rw [←metaplectic_scale_mellin hr W hW hpos hsm.continuous hs,he,htotal.2,hconst,hsum.2]
  change _ = _
  rw [metaplecticSharpPole_mellin (by linarith)]
  dsimp only [metaplecticWeightedRegular,C]
  ring

end CubicFirstMoment

end

end OAI
