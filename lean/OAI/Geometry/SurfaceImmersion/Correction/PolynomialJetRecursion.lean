import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricForcing

namespace OAI

/-! Finite jet-order induction for the explicit periodic correction recursion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open Expression

/-- Low-jet longitudinal vector, including the velocity loop. -/
def longitudinal (X₀ : LowJet → R4) (V : LowJet → C(CovarianceCorrector.Period, R4)) :
    VectorExpression := fun a => .coeff (fun z => (X₀ z.1 + V z.1 (z.2 : CovarianceCorrector.Period)) a)

def transverse (Y : LowJet → R4) : VectorExpression := fun a => .coeff (fun z => Y z.1 a)

def initial (V : LowJet → C(CovarianceCorrector.Period, R4)) : VectorExpression := fun a =>
  (Expression.coeff (fun z => V z.1 (z.2 : CovarianceCorrector.Period) a)).fluct.primitive

/-- All forcing expressions are formed before the full correction is applied. -/
def step (Y C X₀ : LowJet → R4) (V : LowJet → C(CovarianceCorrector.Period, R4))
    (q : LowJet → ℝ) (dx dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : VectorExpression :=
  fun a => fullComponent Y C X₀ V q (EuclideanSpace.proj a) dy
    ((mixedForcing (longitudinal X₀ V) (transverse Y) dx dy U r).fluct.scale (-1))
    ((transverseForcing dy U r).fluct.scale (-1 / 2))
    ((longitudinalForcing (longitudinal X₀ V) dx U r).fluct.scale (-1))

def coefficients (Y C X₀ : LowJet → R4) (V : LowJet → C(CovarianceCorrector.Period, R4))
    (q : LowJet → ℝ) (dx dy : Fin 2) : ℕ → ℕ → VectorExpression
  | 0 => fun _ => initial V
  | n + 1 => Function.update (coefficients Y C X₀ V q dx dy n) (n + 1)
      (step Y C X₀ V q dx dy (coefficients Y C X₀ V q dx dy n) (n + 1))

lemma order_step {Y C X₀ : LowJet → R4} {V : LowJet → C(CovarianceCorrector.Period, R4)}
    {q : LowJet → ℝ} {dx dy : Fin 2} {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (a : Fin 4) :
    (step Y C X₀ V q dx dy U r a).order ≤ 2 * r + 2 := by
  have hs := forcing_orders hr hU
    (X := longitudinal X₀ V) (Y := transverse Y) (fun _ => le_refl 2) (fun _ => le_refl 2) dx dy
  let h := (mixedForcing (longitudinal X₀ V) (transverse Y) dx dy U r).fluct.scale (-1)
  let j := (transverseForcing dy U r).fluct.scale (-1 / 2)
  let e := (longitudinalForcing (longitudinal X₀ V) dx U r).fluct.scale (-1)
  have hh : h.order ≤ 2 * r + 1 := by simpa only [h, order_scale, order_fluct] using hs.1
  have hj : j.order ≤ 2 * r + 1 := by simpa only [j, order_scale, order_fluct] using hs.2.2
  have he : e.order ≤ 2 * r + 1 := by simpa only [e, order_scale, order_fluct] using hs.2.1
  have hb := fullComponent_bounds Y C X₀ V q (EuclideanSpace.proj a) dy h j e
    (2 * r + 1) (max h.loss (max j.loss e.loss)) (by omega) hh hj he
    (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  exact hb.1

/-- The expression for U_(i+1) uses jets of the base map through order 2i+2,
independently of how much further the finite recursion is continued. -/
theorem coefficients_order (Y C X₀ : LowJet → R4)
    (V : LowJet → C(CovarianceCorrector.Period, R4)) (q : LowJet → ℝ)
    (dx dy : Fin 2) (n i : ℕ) (a : Fin 4) :
    (coefficients Y C X₀ V q dx dy n i a).order ≤ 2 * i + 2 := by
  induction n generalizing i a with
  | zero =>
    change ((Expression.coeff _).fluct.primitive).order ≤ _
    simp only [order_primitive, order_fluct, order]
    omega
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst i
      rw [coefficients, Function.update_self]
      exact order_step (by omega) (fun j _ a => ih j a) a
    · rw [coefficients, Function.update_of_ne hi]
      exact ih i a

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
