import Mathlib
import OAI.Analysis.BoundedHochschild.PathWords

namespace OAI

/-! Self-adjoint and exponential lifts in tracial ultrapowers. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
namespace HochschildUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a*b)=τ (b*a))

 

theorem exists_selfAdjoint_lift (h : selfAdjoint (Ultrapower τ h1 ω htr)) :
    ∃ a : selfAdjoint (ℕ →ᵇ A), quotientHom τ h1 ω htr (a : ℕ →ᵇ A) = (h : Ultrapower τ h1 ω htr) := by
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (h : Ultrapower τ h1 ω htr)
  refine ⟨selfAdjointPart ℝ x,?_⟩
  change quotientHom τ h1 ω htr x = (h : Ultrapower τ h1 ω htr) at hx
  rw [selfAdjointPart_apply_coe,← Complex.coe_smul,map_smul,map_add,map_star,hx,h.property]
  simp only [← two_smul ℂ,smul_smul,← Complex.ofReal_ofNat,← Complex.ofReal_mul,
    invOf_mul_self,Complex.ofReal_one,one_smul]

 

theorem exists_expUnitary_lift (h : selfAdjoint (Ultrapower τ h1 ω htr)) :
    ∃ u : unitary (ℕ →ᵇ A), quotientHom τ h1 ω htr (u : ℕ →ᵇ A) =
      (selfAdjoint.expUnitary h : Ultrapower τ h1 ω htr) := by
  obtain ⟨a,ha⟩ := exists_selfAdjoint_lift τ h1 ω htr h
  refine ⟨selfAdjoint.expUnitary a,?_⟩
  let : NormedAlgebra ℚ (ℕ →ᵇ A) := .restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (Ultrapower τ h1 ω htr) := .restrictScalars ℚ ℂ _
  rw [selfAdjoint.expUnitary_coe,selfAdjoint.expUnitary_coe,
    NormedSpace.map_exp _ ?_,map_smul,ha]
  exact map_continuous (quotientHom τ h1 ω htr)

 
def sequenceEval (j : ℕ) : (ℕ →ᵇ A) →⋆ₐ[ℂ] A where
  toFun a := a j
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

 

theorem exists_expUnitary_coordinates {D : Type*}
    (h : D → selfAdjoint (Ultrapower τ h1 ω htr)) :
    ∃ u : ℕ → D → unitary A, ∀ d,
      quotientFamily τ h1 ω htr (fun j => FreeGroup.lift (u j)) (FreeGroup.of d) =
        (selfAdjoint.expUnitary (h d) : Ultrapower τ h1 ω htr) := by
  choose v hv using fun d => exists_expUnitary_lift τ h1 ω htr (h d)
  let u : ℕ → D → unitary A := fun j d =>
    Unitary.map { (sequenceEval (A := A) j).toMonoidHom with
      map_star' := fun _ => rfl } (v d)
  refine ⟨u,fun d => ?_⟩
  rw [← hv d]
  apply congrArg (quotientHom τ h1 ω htr)
  ext j
  simp only [boundedHom_apply,FreeGroup.lift_apply_of,u,Unitary.coe_map]
  rfl

end HochschildUltrapower

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPaths
open HochschildUltrapower HochschildRare
variable {M C D : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

 

theorem simultaneous_paths_of_free_exponentials
    (v : C → unitary M) (h : D → selfAdjoint (Ultrapower τ h1 ω htr))
    (B : Subalgebra ℂ (Ultrapower τ h1 ω htr)) (b : C → Bˣ)
    (hb : ∀ c, ((b c : B) : Ultrapower τ h1 ω htr)=constant τ h1 ω htr (v c : M))
    (hu : ∀ g : FreeGroup D, g ≠ 1 →
      quotientTrace τ h1 ω htr
        (freshEvaluation (fun d => Unitary.toUnits (selfAdjoint.expUnitary (h d))) g)=0)
    (hfree : HochschildFreeMoments.FreeCoefficients B
      (freshEvaluation (fun d => Unitary.toUnits (selfAdjoint.expUnitary (h d))))
      (quotientTrace τ h1 ω htr).toLinearMap)
    {T : Type*} [Finite T] (r n : T → ℕ)
    (w : ∀ t, Fin (r t) × Fin (n t) → (C ⊕ D) × Bool)
    (q : ∀ t, FreeGroup (Fin (r t))) (hq : ∀ t, q t ≠ 1)
    (hletters : ∀ t, ∃ (s : Fin (r t) → Fin (n t)) (a : Fin (r t) → D),
      (∀ i, (w t (i,s i)).1=Sum.inr (a i)) ∧
      (∀ i z, (w t z).1=Sum.inr (a i) → z=(i,s i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : D → unitary M, ∀ t,
      ‖τ (FreeGroup.lift (pathValue (Sum.elim v u) (w t)) (q t) : M)‖ < ε := by
  obtain ⟨u,hu'⟩ := exists_expUnitary_coordinates τ h1 ω htr h
  have he : freshUnits τ h1 ω htr u =
      fun d => Unitary.toUnits (selfAdjoint.expUnitary (h d)) := by
    funext d
    apply Units.ext
    exact hu' d
  have hhu : ∀ g : FreeGroup D, g ≠ 1 →
      quotientTrace τ h1 ω htr (freshEvaluation (freshUnits τ h1 ω htr u) g)=0 := by
    simpa only [he] using hu
  have hhfree : HochschildFreeMoments.FreeCoefficients B
      (freshEvaluation (freshUnits τ h1 ω htr u))
      (quotientTrace τ h1 ω htr).toLinearMap := by
    simpa only [he] using hfree
  obtain ⟨j,hj⟩ := simultaneous_paths_of_free_lifts τ h1 ω htr v u B b hb
    hhu hhfree r n w q hq hletters ε hε
  exact ⟨u j,hj⟩

end HochschildPaths
end

end OAI
