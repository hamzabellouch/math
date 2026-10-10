import Mathlib
import OAI.Analysis.FreeWords.FactorCorners
import OAI.Analysis.FreeWords.TupleHull

namespace OAI

noncomputable section

namespace KKConcreteCorner

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport KKFactorSupport KKUltraTrace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

private theorem closure_convexHull_subset_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) {s : Set E}
    (hs : s ⊆ {v | T v = 0}) : closure (convexHull ℝ s) ⊆ {v | T v = 0} :=
  closure_minimal (convexHull_min hs T.ker.convex)
    (isClosed_eq T.continuous continuous_const)

private def cornerOperator {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (p a : ConcreteAlgebra M) : TupleSpace τ (ι := Bool) →L[ℂ] (tracePositive τ).GNS :=
  ((tracePositive τ).gnsStarAlgHom a).comp (PiLp.proj 2 _ false) -
    ((tracePositive τ).gnsStarAlgHom p).comp (PiLp.proj 2 _ true)

private theorem cornerOperator_orbit {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (p a : ConcreteAlgebra M) (hcentral : ∀ y : ConcreteAlgebra M, a*y*p=p*y*a) :
    tupleOrbit τ (fun b : Bool => if b then a else p) ⊆
      {v | cornerOperator τ p a v = 0} := by
  rintro _ ⟨u,rfl⟩
  change (tracePositive τ).gnsStarAlgHom a (gnsVector (tracePositive τ) (algebraConj u p)) -
    (tracePositive τ).gnsStarAlgHom p (gnsVector (tracePositive τ) (algebraConj u a))=0
  rw [gnsStarAlgHom_vector,gnsStarAlgHom_vector,sub_eq_zero]
  congr 1
  simp only [algebraConj_apply,← mul_assoc]
  rw [hcentral]

private theorem cornerOperator_hull {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (p a : ConcreteAlgebra M) (hcentral : ∀ y : ConcreteAlgebra M, a*y*p=p*y*a) :
    tupleHull τ (fun b : Bool => if b then a else p) ⊆
      {v | cornerOperator τ p a v = 0} :=
  closure_convexHull_subset_zero ((cornerOperator τ p a).restrictScalars ℝ)
    (cornerOperator_orbit τ p a hcentral)

private theorem cornerOperator_trace_zero {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hF : KKFreeLiftFrontier.IsFactor M) (p a : ConcreteAlgebra M)
    (hcentral : ∀ y : ConcreteAlgebra M, a*y*p=p*y*a) :
    cornerOperator τ p a
      (tupleVector τ (fun b : Bool => τ.map (if b then a else p) • 1)) = 0 :=
  cornerOperator_hull τ p a hcentral (tuple_trace_in_hull τ hF _)

open scoped ComplexOrder in
private theorem gnsStarAlgHom_smul_one {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (a : A) (c : ℂ) :
    τ.gnsStarAlgHom a (gnsVector τ (c • 1)) = gnsVector τ (c • a) := by
  rw [gnsStarAlgHom_vector, mul_smul_comm, mul_one]

private theorem cornerOperator_trace_value {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (p a : ConcreteAlgebra M) :
    cornerOperator τ p a
      (tupleVector τ (fun b : Bool => τ.map (if b then a else p) • 1)) =
      gnsVector (tracePositive τ) (τ.map p • a) -
        gnsVector (tracePositive τ) (τ.map a • p) := by
  change (tracePositive τ).gnsStarAlgHom a (gnsVector (tracePositive τ) (τ.map p • 1)) -
    (tracePositive τ).gnsStarAlgHom p (gnsVector (tracePositive τ) (τ.map a • 1)) = _
  exact congrArg₂ (· - ·)
    (gnsStarAlgHom_smul_one (tracePositive τ) a (τ.map p))
    (gnsStarAlgHom_smul_one (tracePositive τ) p (τ.map a))

private theorem corner_trace_smul_eq {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hF : KKFreeLiftFrontier.IsFactor M) (p a : ConcreteAlgebra M)
    (hcentral : ∀ y : ConcreteAlgebra M, a*y*p=p*y*a) :
    τ.map p • a = τ.map a • p := by
  apply gnsVector_injective τ
  apply sub_eq_zero.mp
  exact (cornerOperator_trace_value τ p a).symm.trans (cornerOperator_trace_zero τ hF p a hcentral)

theorem corner_central_scalar {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (hF : KKFreeLiftFrontier.IsFactor M)
    (p a : ConcreteAlgebra M) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hcentral : ∀ y : ConcreteAlgebra M, a*y*p=p*y*a) :
    ∃ c : ℂ, a=c • p := by
  have he' := corner_trace_smul_eq τ hF p a hcentral
  have hpτ := trace_projection_ne_zero τ hp hp0
  refine ⟨(τ.map p)⁻¹*τ.map a,?_⟩
  have h := congrArg (fun z : ConcreteAlgebra M => (τ.map p)⁻¹ • z) he'
  simpa only [smul_smul,inv_mul_cancel₀ hpτ,one_smul] using h

end

end KKConcreteCorner
end

end OAI
