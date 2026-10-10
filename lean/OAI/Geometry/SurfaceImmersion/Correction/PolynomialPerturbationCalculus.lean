import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialVariationDerivatives
import OAI.Geometry.SurfaceImmersion.Geometry.JetVariationLinearity

namespace OAI

/-! The perturbation operators and their actual first variations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {n : ℕ}

def eval (P : Fin n → Expression) (ε : ℝ) (G : Base → Space) (z : Base × ℝ) : ℝ :=
  ∑ l, ε ^ (l.val + 1) * (P l).eval G z

def variation (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space) (z : Base × ℝ) : ℝ :=
  ∑ l, ε ^ (l.val + 1) * (P l).variation G H z

theorem variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {P : Fin n → Expression} (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (z : Base × ℝ) (hQ : lowJet G z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => eval P ε (fun p => G p + s • H p) z)
      (variation P ε G H z) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((P l).variation_hasDerivAt hO hG hH (hP l) z hQ).const_mul (ε ^ (l.val + 1)))
  simpa only [eval, variation] using h

lemma variation_add (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (z : Base × ℝ) :
    variation P ε G (fun p => H p + K p) z = variation P ε G H z + variation P ε G K z := by
  simp only [variation, Expression.variation_add _ _ hH hK, mul_add, Finset.sum_add_distrib]

lemma variation_smul (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H : Base → Space} (hH : ContDiff ℝ ∞ H) (c : ℝ) (z : Base × ℝ) :
    variation P ε G (fun p => c • H p) z = c * variation P ε G H z := by
  simp only [variation, Expression.variation_smul _ _ hH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma eval_smooth {O : Set LowJet} {U : Set Base} {P : Fin n → Expression}
    (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O) :
    ContDiffOn ℝ ∞ (eval P ε G) (U ×ˢ Set.univ) := by
  exact ContDiffOn.sum (fun l _ => contDiffOn_const.mul ((P l).eval_smooth hG hQ (hP l)))

lemma variation_smooth {O : Set LowJet} (hO : IsOpen O) {U : Set Base}
    {P : Fin n → Expression} (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) :
    ContDiffOn ℝ ∞ (variation P ε G H) (U ×ˢ Set.univ) := by
  exact ContDiffOn.sum (fun l _ => contDiffOn_const.mul
    ((P l).variation_smooth hO hG hH hQ (hP l)))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
