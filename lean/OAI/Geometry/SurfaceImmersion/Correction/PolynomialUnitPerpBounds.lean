import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerpBounds

namespace OAI

/-! Quantitative bounds for the actual unit perpendicular vector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The only denominator parameter is an upper bound for the reciprocal
squared length of the perpendicular product. -/
theorem weighted_unitPerp (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
    ∀ {s C K : ℝ} {X Y B : E → RVec 4}, 0 < s → 0 ≤ C → 1 ≤ K →
      ContDiffOn ℝ ∞ X U → ContDiffOn ℝ ∞ Y U → ContDiffOn ℝ ∞ B U →
      WeightedBound U s m C X → WeightedBound U s m C Y → WeightedBound U s m C B →
      (∀ x ∈ U, 0 < NormalFrame.perpProduct (X x) (Y x) (B x) ⬝ᵥ
        NormalFrame.perpProduct (X x) (Y x) (B x)) →
      (∀ x ∈ U, (NormalFrame.perpProduct (X x) (Y x) (B x) ⬝ᵥ
        NormalFrame.perpProduct (X x) (Y x) (B x))⁻¹ ≤ K) →
      WeightedBound U s m
        (2^m*((m.factorial : ℝ)*D*K^(m+1)*(1+dotBudget m (perpBudget m C))^m)*perpBudget m C)
        (fun x => NormalFrame.unitPerp (X x) (Y x) (B x)) := by
  obtain ⟨D,hD,hroot⟩ := weighted_inverse_sqrt (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s C K X Y B hs hC hK hX hY hB bX bY bB hpos hi
  let P : E → RVec 4 := fun x => NormalFrame.perpProduct (X x) (Y x) (B x)
  have hP : ContDiffOn ℝ ∞ P U := contDiffOn_perpProduct hX hY hB
  have bP : WeightedBound U s m (perpBudget m C) P :=
    weighted_perpProduct hU hs hC hX hY hB bX bY bB
  have hPn := perpBudget_nonneg m hC
  have hS := contDiffOn_dot_real hP hP
  have bS : WeightedBound U s m (1+dotBudget m (perpBudget m C)) (fun x => P x ⬝ᵥ P x) :=
    (bP.dot_real hU hs.le hPn hPn hP hP bP).mono_const (by
      change dotBudget m (perpBudget m C) ≤ 1+dotBudget m (perpBudget m C)
      linarith)
  have hS1 : 1 ≤ 1+dotBudget m (perpBudget m C) := by
    have hh := dotBudget_nonneg m hPn
    linarith
  have br := hroot hU hs hS1 hK hS hpos hi bS
  have hrootSmooth := (hS.sqrt (fun x hx => (hpos x hx).ne')).inv
    (fun x hx => (Real.sqrt_pos.mpr (hpos x hx)).ne')
  exact br.smul_real_pi hU hs (by positivity) hPn hrootSmooth hP bP

end ClosedSurfaceR4.RealModes

end

end OAI
