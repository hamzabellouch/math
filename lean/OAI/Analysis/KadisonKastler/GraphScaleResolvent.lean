import OAI.Analysis.KadisonKastler.TomitaClosedOperator
import OAI.Analysis.KadisonKastler.TomitaResolventFaithful

namespace OAI

/-! # Resolvents under a change of graph scale

Scaling the second graph coordinate gives an exact algebraic relation
between every graph resolvent and the resolvent at scale one. This
relation is obtained from orthogonal projection, before using spectral
calculus or an unbounded modular operator.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphCoordinateScale (c : ℝ) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
  tomitaProductCoordinates.symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.id ℂ H).prodMap ((c : ℂ) • ContinuousLinearMap.id ℂ H)) ∘L
      tomitaProductCoordinates.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp] theorem graphCoordinateScale_zero (c : ℝ) (v : TomitaGraphHilbert H) :
    graphCoordinateScale c v 0 = v 0 := rfl

omit [CompleteSpace H] in
@[simp] theorem graphCoordinateScale_one (c : ℝ) (v : TomitaGraphHilbert H) :
    graphCoordinateScale c v 1 = (c : ℂ) • v 1 := rfl

theorem graphCoordinateScale_vector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c d : ℝ)
    (a : H →L[ℂ] H) :
    graphCoordinateScale c (rescaledGraphVector J Ω d a) =
      rescaledGraphVector J Ω (c * d) a := by
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · change (c : ℂ) • (d • J (star a Ω)) = (c * d) • J (star a Ω)
    rw [Complex.coe_smul, smul_smul]

theorem graphCoordinateScale_mem (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c d : ℝ)
    {v : TomitaGraphHilbert H} (hv : v ∈ rescaledGraphSubspace M J Ω d) :
    graphCoordinateScale c v ∈ rescaledGraphSubspace M J Ω (c * d) := by
  have hc : IsClosed {v : TomitaGraphHilbert H |
      graphCoordinateScale c v ∈ rescaledGraphSubspace M J Ω (c * d)} :=
    (Submodule.isClosed_topologicalClosure _).preimage (graphCoordinateScale c).continuous
  apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω d)) ?_ hc hv
  rintro _ ⟨a, rfl⟩
  change graphCoordinateScale c (rescaledGraphVector J Ω d a.val) ∈
    rescaledGraphSubspace M J Ω (c * d)
  rw [graphCoordinateScale_vector]
  exact rescaledGraphVector_mem M J Ω (c * d) a

omit [CompleteSpace H] in
private theorem scaled_residual_inner (c : ℝ) (x : H) (v w : TomitaGraphHilbert H) :
    inner ℂ (Generator.tupleSingle 0 (v 0 + (c : ℂ) ^ 2 • (x - v 0)) -
      graphCoordinateScale c v) (graphCoordinateScale c w) =
      (c : ℂ) ^ 2 * inner ℂ (Generator.tupleSingle 0 x - v) w := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two]
  change inner ℂ ((v 0 + (c : ℂ) ^ 2 • (x - v 0)) - v 0) (w 0) +
    inner ℂ (0 - (c : ℂ) • v 1) ((c : ℂ) • w 1) =
    (c : ℂ) ^ 2 * (inner ℂ (x - v 0) (w 0) + inner ℂ (0 - v 1) (w 1))
  rw [add_sub_cancel_left]
  simp only [inner_smul_left, inner_smul_right, zero_sub, inner_neg_left,
    map_pow, Complex.conj_ofReal]
  ring

theorem graphScale_projection_identity (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : H) :
    let p := rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 x)
    rescaledGraphProjection M J Ω c
      (Generator.tupleSingle 0 (p 0 + (c : ℂ) ^ 2 • (x - p 0))) =
      graphCoordinateScale c p := by
  intro p
  let P := rescaledGraphSubspace M J Ω c
  apply P.eq_starProjection_of_mem_of_inner_eq_zero
  · have hm := graphCoordinateScale_mem J Ω c 1
      ((rescaledGraphSubspace M J Ω 1).starProjection_apply_mem (Generator.tupleSingle 0 x))
    simpa only [P, p, rescaledGraphProjection, mul_one] using hm
  · intro w hw
    have hc : IsClosed {w : TomitaGraphHilbert H |
        inner ℂ (Generator.tupleSingle 0 (p 0 + (c : ℂ) ^ 2 • (x - p 0)) -
          graphCoordinateScale c p) w = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω c)) ?_ hc hw
    rintro _ ⟨a, rfl⟩
    change inner ℂ (Generator.tupleSingle 0 (p 0 + (c : ℂ) ^ 2 • (x - p 0)) -
      graphCoordinateScale c p) (rescaledGraphVector J Ω c a.val) = 0
    have he : rescaledGraphVector J Ω c a.val =
        graphCoordinateScale c (rescaledGraphVector J Ω 1 a.val) := by
      simpa only [mul_one] using (graphCoordinateScale_vector J Ω c 1 a.val).symm
    rw [he, scaled_residual_inner]
    have ho := (rescaledGraphSubspace M J Ω 1).starProjection_inner_eq_zero
      (Generator.tupleSingle 0 x) (rescaledGraphVector J Ω 1 a.val)
        (rescaledGraphVector_mem M J Ω 1 a)
    change inner ℂ (Generator.tupleSingle 0 x - p) (rescaledGraphVector J Ω 1 a.val) = 0 at ho
    rw [ho, mul_zero]

/-- The positive denominator relating the rescaled graph resolvents. -/
def graphScaleDenominator (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →L[ℂ] H :=
  graphResolvent M J Ω 1 + (c : ℂ) ^ 2 • (1 - graphResolvent M J Ω 1)

theorem graphResolvent_mul_scaleDenominator (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    graphResolvent M J Ω c * graphScaleDenominator M J Ω c = graphResolvent M J Ω 1 := by
  ext x
  have h := congrArg (fun v : TomitaGraphHilbert H => v 0)
    (graphScale_projection_identity (M := M) J Ω c x)
  exact h

end

end KadisonKastler

end OAI
