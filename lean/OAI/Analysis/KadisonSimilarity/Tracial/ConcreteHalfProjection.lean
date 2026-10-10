import OAI.Analysis.KadisonSimilarity.Tracial.TracialHalfProjectionData
import OAI.Analysis.FactorGeneration.ProjectionLimits

namespace OAI

/-! A small projection in an actual diffuse tracial von Neumann algebra
can be completed to trace one half.  The only projection-existence step
is the proved exact-trace subprojection theorem. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

local instance : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

/-- The vector trace bundled only as the linear map needed by the
half-projection construction. -/
def concreteTraceLinear (τ : TracialRepresentation M) : M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun := τ.trace
  map_add' a b := inner_add_right _ _ _
  map_smul' c a := by
    change inner ℂ τ.vector (c • (a : H →L[ℂ] H) τ.vector) =
      c • inner ℂ τ.vector ((a : H →L[ℂ] H) τ.vector)
    exact inner_smul_right _ _ _

@[simp] theorem concreteTraceLinear_apply (τ : TracialRepresentation M)
    (a : M.toStarSubalgebra) : concreteTraceLinear τ a = τ.trace a := rfl

@[simp] theorem concreteTraceLinear_one (τ : TracialRepresentation M) :
    concreteTraceLinear τ 1 = 1 := τ.trace_one

/-- Exact trace cutting in the orthogonal complement supplies the missing
part of a half-trace projection. -/
theorem exists_concreteHalfTraceProjectionData (τ : TracialRepresentation M)
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (e : M.toStarSubalgebra) (he : IsStarProjection e)
    {t : ℝ} (hetrace : τ.trace e = (t : ℂ)) (ht : t ≤ 1 / 2) :
    Nonempty (HalfTraceProjectionData (concreteTraceLinear τ) e) := by
  have hcomplement : τ.trace (1 - e) = (1 - t : ℝ) := by
    change concreteTraceLinear τ (1 - e) = _
    rw [map_sub, concreteTraceLinear_one, concreteTraceLinear_apply, hetrace]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
  have hr : 0 ≤ 1 / 2 - t := sub_nonneg.mpr ht
  have hrp : 1 / 2 - t ≤ (τ.trace (1 - e)).re := by
    rw [hcomplement, Complex.ofReal_re]
    linarith
  obtain ⟨q, hq, hleft, _, hqtrace⟩ :=
    Generator.Tracial.exists_exact_trace_subprojection τ hdiff (1 - e) he.one_sub
      (1 / 2 - t) hr hrp
  have heq : e * q = 0 := by
    have h : q - e * q = q := by simpa only [sub_mul, one_mul] using hleft
    exact sub_eq_self.mp h
  refine ⟨halfTraceProjectionDataOfOrthogonal (concreteTraceLinear τ) he hq heq
    hetrace ?_⟩
  change τ.trace q = 1 / 2 - (t : ℂ)
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using hqtrace

/-- A concrete choice of the half projection used to make the centered
reflection in the finite-factor argument. -/
def concreteHalfTraceProjectionData (τ : TracialRepresentation M)
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (e : M.toStarSubalgebra) (he : IsStarProjection e)
    {t : ℝ} (hetrace : τ.trace e = (t : ℂ)) (ht : t ≤ 1 / 2) :
    HalfTraceProjectionData (concreteTraceLinear τ) e :=
  Classical.choice (exists_concreteHalfTraceProjectionData τ hdiff e he hetrace ht)

end KadisonSimilarity

end

end OAI
