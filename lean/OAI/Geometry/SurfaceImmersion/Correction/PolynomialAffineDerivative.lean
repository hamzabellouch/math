import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAffineFamily

namespace OAI

/-! Actual polynomial variations at every point of an affine path, rather
than only at the parameter origin. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma varyBase_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H) (t : ℝ) :
    ∀ i, ContDiff ℝ ∞ (varyBase G H t i) := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [varyBase_base]
    exact (hG 0).add (hH.const_smul t)
  · rw [varyBase_other G H t hi]
    exact hG i

lemma varyBase_add (G : Fin 4 → Base → Space) (H : Base → Space) (t s : ℝ) :
    varyBase (varyBase G H t) H s = varyBase G H (t + s) := by
  funext i p
  by_cases hi : i = 0
  · simp only [varyBase, hi, ↓reduceIte, add_smul]
    abel
  · simp only [varyBase, hi, ↓reduceIte]

theorem differentiate_hasDerivAt_at {O : Set LowJet} (hO : IsOpen O)
    {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {e : MixedExpression} (he : e.SmoothCoeffs O) (j : Fin 3) (t : ℝ) (z : Base × ℝ)
    (hQ : lowJet (varyBase G (G j.succ) t 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (varyBase G (G j.succ) s) z)
      ((e.differentiate j).eval (varyBase G (G j.succ) t) z) t := by
  have hd := differentiate_hasDerivAt hO (varyBase_smooth hG (hG j.succ) t) he j z hQ
  rw [varyBase_other G (G j.succ) t (Fin.succ_ne_zero j)] at hd
  have hd' : HasDerivAt
      (fun s : ℝ => e.eval (varyBase (varyBase G (G j.succ) t) (G j.succ) s) z)
      ((e.differentiate j).eval (varyBase G (G j.succ) t) z) (t - t) := by
    simpa only [sub_self] using hd
  have hs := hd'.comp_sub_const t t
  convert hs using 1
  funext s
  rw [varyBase_add]
  congr 2
  ring

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
