import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetRegularity
import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetDerivatives

namespace OAI

/-! Joint smoothness in position and a variation parameter for actual
higher-jet polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma jet_affine_joint_smooth {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => jet (fun p => G p + z.2 • H p) w a z.1) := by
  have he : (fun z : Base × ℝ => jet (fun p => G p + z.2 • H p) w a z.1) =
      fun z => jet G w a z.1 + z.2 * jet H w a z.1 := by
    funext z
    rw [jet_add hG (hH.const_smul z.2), jet_smul hH]
  rw [he]
  exact ((jet_smooth hG w a).comp contDiff_fst).add
    (contDiff_snd.mul ((jet_smooth hH w a).comp contDiff_fst))

lemma lowJet_affine_joint_smooth {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => lowJet (fun p => G p + z.2 • H p) z.1) := by
  have he : (fun z : Base × ℝ => lowJet (fun p => G p + z.2 • H p) z.1) =
      fun z => lowJet G z.1 + z.2 • variationLowJet H z.1 := by
    funext z
    exact lowJet_affine hG hH z.2 z.1
  rw [he]
  exact ((lowJet_smooth hG).comp contDiff_fst).add
    (contDiff_snd.smul ((variationLowJet_smooth hH).comp contDiff_fst))

namespace MixedExpression

lemma jet_varyBase_joint_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H)
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => jet (varyBase G H z.2 i) w a z.1) := by
  by_cases hi : i = 0
  · subst i
    simpa only [varyBase_base] using jet_affine_joint_smooth (hG 0) hH w a
  · simpa only [varyBase_other G H _ hi, Function.comp_def] using (jet_smooth (hG i) w a).comp contDiff_fst

/-- Global coefficient smoothness is obtained on the application compact set
by `Expression.exists_global_extension`. -/
theorem eval_varyBase_joint_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H)
    {e : MixedExpression} (he : e.SmoothCoeffs Set.univ) (θ : ℝ) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => e.eval (varyBase G H z.2) (z.1, θ)) := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c := contDiffOn_univ.mp (by simpa only [SmoothCoeffs, Set.univ_prod_univ] using he)
    have hh := hc.comp ((lowJet_affine_joint_smooth (hG 0) hH).prodMk (contDiff_const (c := θ)))
    simpa only [eval, varyBase_base, Function.comp_def] using hh
  | atom i w a e ih =>
    exact (jet_varyBase_joint_smooth hG hH i w a).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
