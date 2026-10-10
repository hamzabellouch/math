import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialIntegral

namespace OAI

/-! Linear operators in the angular variable preserve higher-jet polynomials.
This includes operators whose coefficients depend smoothly on the second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def liftOperator (T : LowJet → (ℝ → ℝ) → ℝ → ℝ) (e : Expression) : Expression :=
  e.mapCoeff (fun c z => T z.1 (fun t => c (z.1, t)) z.2)

lemma smoothCoeffs_liftOperator {O : Set LowJet} {T : LowJet → (ℝ → ℝ) → ℝ → ℝ}
    (hT : ∀ c : LowJet × ℝ → ℝ, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) →
      ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => T z.1 (fun t => c (z.1, t)) z.2)
        (O ×ˢ Set.univ)) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.liftOperator T).SmoothCoeffs O := smoothCoeffs_map e _ hT he

@[simp] lemma order_liftOperator (T : LowJet → (ℝ → ℝ) → ℝ → ℝ) (e : Expression) :
    (e.liftOperator T).order = e.order := order_mapCoeff _ _

@[simp] lemma loss_liftOperator (T : LowJet → (ℝ → ℝ) → ℝ → ℝ) (e : Expression) :
    (e.liftOperator T).loss = e.loss := loss_mapCoeff _ _

/-- This uses actual operator linearity, not an assumed polynomial representation. -/
lemma eval_liftOperator {O : Set LowJet} (hO : IsOpen O)
    (T : LowJet → (ℝ → ℝ) → ℝ → ℝ)
    (hadd : ∀ Q ∈ O, ∀ f g : ℝ → ℝ, Continuous f → Continuous g → ∀ t,
      T Q (fun s => f s + g s) t = T Q f t + T Q g t)
    (hsmul : ∀ Q ∈ O, ∀ a : ℝ, ∀ f : ℝ → ℝ, ∀ t,
      T Q (fun s => a * f s) t = a * T Q f t)
    {e : Expression} (he : e.SmoothCoeffs O) (G : Base → Space)
    {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (e.liftOperator T).eval G (p, t) = T (lowJet G p) (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * (e.liftOperator T).eval G (p, t) =
      T (lowJet G p) (fun s => jet G w a p * e.eval G (p, s)) t
    rw [hsmul _ hp, ih he]
  | add e f ihe ihf =>
    change (e.liftOperator T).eval G (p, t) + (f.liftOperator T).eval G (p, t) =
      T (lowJet G p) (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [hadd _ hp _ _ (eval_slice_smooth hO he.1 G hp).continuous
      (eval_slice_smooth hO he.2 G hp).continuous, ihe he.1, ihf he.2]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
