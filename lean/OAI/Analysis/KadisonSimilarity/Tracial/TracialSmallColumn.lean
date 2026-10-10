import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation

namespace OAI

/-! The small vectors in propagation are actual left compressions of the
completed base space. Scalar freeness gives their exact norm, first on
algebra vectors and then throughout the completion by density. -/

noncomputable section
namespace KadisonSimilarity

namespace ScalarFree

variable {P : Type*} [Ring P] [Algebra ℂ P] [StarRing P] [StarModule ℂ P]
  {τ : P →ₗ[ℂ] ℂ} {D A : StarSubalgebra ℂ P}

/-- Centered freeness gives the product trace formula for arbitrary letters
from the two algebras. -/
theorem trace_product (hf : ScalarFree τ D A) (hτ : τ 1 = 1)
    {x y : P} (hx : x ∈ D) (hy : y ∈ A) : τ (x * y) = τ x * τ y := by
  have h := trace_centered_mul_of_free τ hτ hf
    (traceCentered_mem τ D hx) (traceCentered_trace τ hτ x) hy
  simpa only [traceCentered, sub_mul, smul_mul_assoc, one_mul,
    map_sub, map_smul, smul_eq_mul, sub_eq_zero] using h

end ScalarFree

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The actual small-column map is left multiplication by the projection,
restricted to the completed base Hilbert space. -/
def tracialSmallColumn (q : P) : G.baseSpace A →L[ℂ] H :=
  (G.left q).comp (G.baseInclusion A).toContinuousLinearMap

@[simp] theorem tracialSmallColumn_apply (q : P) (v : G.baseSpace A) :
    G.tracialSmallColumn A q v = G.left q (v : H) := rfl

@[simp] theorem tracialSmallColumn_vector (q : P) (b : A) :
    G.tracialSmallColumn A q (G.baseVector A b) = G.vector (q * (b : P)) :=
  G.left_vector q (b : P)

/-- The exact inner-product scaling on bounded base-algebra vectors follows
from the projection identity, traciality, and scalar freeness. -/
theorem tracialSmallColumn_inner_base (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D) (b c : A) :
    inner ℂ (G.tracialSmallColumn A q (G.baseVector A b))
      (G.tracialSmallColumn A q (G.baseVector A c)) =
        G.trace q * inner ℂ (G.baseVector A b) (G.baseVector A c) := by
  rw [G.tracialSmallColumn_vector, G.tracialSmallColumn_vector, G.inner_vector]
  have hprod : star (q * (b : P)) * (q * (c : P)) = star (b : P) * (q * (c : P)) := by
    rw [star_mul, hq.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc q q (c : P), hq.isIdempotentElem.eq]
  have hbstar : star (b : P) ∈ A := star_mem b.property
  have hcb : (c : P) * star (b : P) ∈ A := A.mul_mem c.property hbstar
  rw [hprod, G.tracial (star (b : P)) (q * (c : P)), mul_assoc,
    hf.trace_product hτ hqD hcb,
    G.tracial (c : P) (star (b : P)), G.baseVector_inner]

/-- The inner-product formula extends from bounded algebra vectors to the
entire completed base space. -/
theorem tracialSmallColumn_inner (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D) (v w : G.baseSpace A) :
    inner ℂ (G.tracialSmallColumn A q v) (G.tracialSmallColumn A q w) =
      G.trace q * inner ℂ v w := by
  refine (G.baseVector_dense A).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  exact (G.baseVector_dense A).induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop))
    (G.tracialSmallColumn_inner_base A D hf hτ q hq hqD b)

/-- The small vectors have the exact square-root trace scaling. This is a
consequence of freeness and density, not an additional word-model field. -/
theorem norm_tracialSmallColumn (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D)
    {a : ℝ} (ha : 0 ≤ a) (htrace : G.trace q = (a : ℂ)) (v : G.baseSpace A) :
    ‖G.tracialSmallColumn A q v‖ = Real.sqrt a * ‖v‖ := by
  have hsq : ‖G.tracialSmallColumn A q v‖ ^ 2 = a * ‖v‖ ^ 2 := by
    calc
      _ = Complex.re (inner ℂ (G.tracialSmallColumn A q v)
          (G.tracialSmallColumn A q v)) := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = a * Complex.re (inner ℂ v v) := by
        rw [G.tracialSmallColumn_inner A D hf hτ q hq hqD, htrace]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = _ := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
        rfl
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg v))).mp
  rw [mul_pow, Real.sq_sqrt ha]
  exact hsq

/-- The small column is supported by its defining projection. -/
theorem tracialSmallColumn_support (q : P) (hq : IsStarProjection q) :
    (G.left q).comp (G.tracialSmallColumn A q) = G.tracialSmallColumn A q := by
  ext v
  change (G.left q * G.left q) (v : H) = G.left q (v : H)
  rw [← map_mul, hq.isIdempotentElem.eq]

/-- Commutation with the projection transfers the base action to the small
column, giving the level-zero identity required by propagation. -/
theorem tracialSmallColumn_intertwines (q : P) (Y : H →L[ℂ] H)
    (B₀ : G.baseSpace A →L[ℂ] G.baseSpace A)
    (hbase : Y.comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp B₀)
    (hcomm : Y.comp (G.left q) = (G.left q).comp Y) :
    Y.comp (G.tracialSmallColumn A q) = (G.tracialSmallColumn A q).comp B₀ := by
  change Y.comp ((G.left q).comp (G.baseInclusion A).toContinuousLinearMap) =
    ((G.left q).comp (G.baseInclusion A).toContinuousLinearMap).comp B₀
  rw [← ContinuousLinearMap.comp_assoc, hcomm, ContinuousLinearMap.comp_assoc,
    hbase, ← ContinuousLinearMap.comp_assoc]

/-- Invariance of the actual base subspace identifies the level-zero
operator with the actual compression of the ambient operator. -/
theorem tracialSmallColumn_level_zero (q : P) (Y : H →L[ℂ] H)
    (hbase : ∀ v ∈ G.baseSpace A, Y v ∈ G.baseSpace A)
    (hcomm : Y.comp (G.left q) = (G.left q).comp Y) (v : G.baseSpace A) :
    Y (G.tracialSmallColumn A q v) =
      G.tracialSmallColumn A q (G.baseOperator A Y v) := by
  exact congrArg (fun T : G.baseSpace A →L[ℂ] H => T v)
    (G.tracialSmallColumn_intertwines A q Y (G.baseOperator A Y)
      (G.baseOperator_intertwines A Y hbase) hcomm)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
