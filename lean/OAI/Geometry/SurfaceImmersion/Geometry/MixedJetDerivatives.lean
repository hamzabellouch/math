import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetCalculus

namespace OAI

/-! Actual differentiation of mixed jet polynomials in the base-map slot. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

lemma jet_affine_hasDerivAt {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) (t : ℝ) :
    HasDerivAt (fun s : ℝ => jet (fun q => G q + s • H q) w a p)
      (jet H w a p) t := by
  have hpath : (fun s : ℝ => jet (fun q => G q + s • H q) w a p) =
      (fun s : ℝ => jet G w a p + s * jet H w a p) := by
    funext s
    rw [jet_add (H := fun q => s • H q) hG (ContDiff.const_smul s hH), jet_smul hH]
  rw [hpath]
  simpa only [one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (jet H w a p)).const_add (jet G w a p)

namespace MixedExpression

def varyBase (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ) : Fin 4 → Base → Space :=
  fun i p => if i = 0 then G 0 p + s • H p else G i p

lemma varyBase_zero (G : Fin 4 → Base → Space) (H : Base → Space) : varyBase G H 0 = G := by
  funext i p
  by_cases hi : i = 0 <;> simp [varyBase, hi]

lemma varyBase_base (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ) :
    varyBase G H s 0 = fun p => G 0 p + s • H p := by
  funext p
  simp only [varyBase, ↓reduceIte]

lemma varyBase_other (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ)
    {i : Fin 4} (hi : i ≠ 0) : varyBase G H s i = G i := by
  funext p
  simp only [varyBase, hi, ↓reduceIte]

/-- The syntactic derivative evaluates to the actual derivative, while the
three direction slots remain fixed. -/
theorem differentiate_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {e : MixedExpression} (he : e.SmoothCoeffs O) (j : Fin 3) (z : Base × ℝ)
    (hQ : lowJet (G 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (varyBase G (G j.succ) s) z)
      ((e.differentiate j).eval G z) 0 := by
  induction e with
  | coeff c =>
    have hd := Expression.variation_hasDerivAt hO (hG 0) (hG j.succ)
      (e := .coeff c) he z hQ
    simpa only [eval, varyBase_base, Expression.eval, Expression.variation,
      differentiate_coeff_eval] using hd
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      have hj := jet_affine_hasDerivAt (hG 0) (hG j.succ) w a z.1 0
      have hd := hj.fun_mul (ih he)
      simpa only [eval, varyBase_base, varyBase_zero, differentiate, ↓reduceIte,
        Pi.mul_apply, zero_smul, add_zero] using hd
    · have hj := (hasDerivAt_const (0 : ℝ) (jet (G i) w a z.1)).fun_mul (ih he)
      simpa only [eval, varyBase_other G (G j.succ) _ hi, varyBase_zero,
        differentiate, hi, ↓reduceIte, zero_mul, zero_add, Pi.mul_apply] using hj
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
