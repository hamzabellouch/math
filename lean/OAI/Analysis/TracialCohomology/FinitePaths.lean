import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.ResidualFilling

namespace OAI

/-! Finite paths for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace MissingFinitePaths
open BoundedHochschild HochschildDiffuse HochschildRare
universe u

def Factor (M : Type u) [CStarAlgebra M] : Prop :=
  ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b = c • (1 : M)

def FactorProducerGoal : Prop :=
  ∀ (M X : Type u) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ),
      TraceInPredual e τ → τ 1 = 1 →
      (∀ a b : M, τ (a*b) = τ (b*a)) →
      (∀ a : M, τ (star a*a) = 0 → a = 0) →
      Factor M → NoMinimalProjections M → FinitePathTests τ

end MissingFinitePaths

open scoped ComplexOrder
namespace PopaPatching
open HochschildRare HochschildPaths
variable {C D M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def pathCoefficients (v : C → unitary M) (x : C × Bool) : M := (signedValue v x:M)
def pathDegrees : Option (D × Bool) → FreeGroup D
  | none => 1
  | some (d,b) => signed (FreeGroup.of d) b

def pathEncode : (C ⊕ D) × Bool → Letter (C × Bool) (Option (D × Bool))
  | (.inl c,b) => .inl (c,b)
  | (.inr d,b) => .inr (some (d,b))

omit [PartialOrder M] [StarOrderedRing M] in
lemma pathCoefficients_norm (v : C → unitary M) (x) : ‖pathCoefficients v x‖≤1 := by
  have hh := CStarRing.norm_coe_unitary_mul (signedValue v x) (1:M)
  simpa only [mul_one,pathCoefficients] using hh.le.trans (IsStarProjection.one M).norm_le

lemma pathEncode_degree (l : List ((C ⊕ D) × Bool)) :
    degree pathDegrees (l.map pathEncode)=freshProjection (FreeGroup.mk l) := by
  simp only [degree,List.map_map,freshProjection,FreeGroup.lift_mk]
  congr 2
  funext x
  rcases x with ⟨c|d,b⟩ <;> cases b <;>
    simp [pathEncode,letterDegree,pathDegrees,signed]

omit [PartialOrder M] [StarOrderedRing M] in
lemma pathEncode_evaluate (a : C → unitary M) (v : Rep (FreeGroup D) M) (hv : v.support=1)
    (l : List ((C ⊕ D) × Bool)) :
    evaluate (pathCoefficients a) pathDegrees v (l.map pathEncode)=
      (FreeGroup.lift (Sum.elim a (fun d => v.toUnitary hv (FreeGroup.of d))) (FreeGroup.mk l):M) := by
  simp only [evaluate,List.map_map,FreeGroup.lift_mk]
  change _ = (unitary M).subtype ((l.map _).prod)
  rw [map_list_prod,List.map_map]
  congr 2
  funext x
  rcases x with ⟨c|d,b⟩ <;> cases b <;>
    simp [pathEncode,letterValue,pathCoefficients,signedValue,pathDegrees,signed,
      Rep.toUnitary]
  exact v.inv (FreeGroup.of d)

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem produced_finite_paths (hdiff : HochschildDiffuse.NoMinimalProjections M) :
    FinitePathTests τ := by
  classical
  intro C D T _ _ _ _ a r n w q hq hw η hη
  let g : T → FreeGroup (C ⊕ D) := fun t => pathHom (w t) (q t)
  let l : T → List (Letter (C × Bool) (Option (D × Bool))) := fun t => (g t).toWord.map pathEncode
  let L : ℕ := Finset.univ.sup (fun t => (l t).length)
  obtain ⟨v,hv,hgood⟩ := finite_unitary_moments e τ hτ htr hfaith h1 hfactor hdiff
    (pathCoefficients a) (pathCoefficients_norm a) (pathDegrees (D:=D)) none rfl L η hη
  refine ⟨fun d => v.toUnitary hv (FreeGroup.of d),fun t => ?_⟩
  have hlen : (l t).length≤L := Finset.le_sup (f:=fun t => (l t).length) (Finset.mem_univ t)
  have hdeg : degree pathDegrees (l t) ≠ 1 := by
    dsimp [l]
    rw [pathEncode_degree,FreeGroup.mk_toWord]
    obtain ⟨s,b,hpos,huniq⟩ := hw t
    exact freshProjection_pathHom_ne_one (w t) s b hpos huniq (q t) (hq t)
  have hh := hgood (l t) hlen hdeg
  dsimp [l] at hh
  rw [pathEncode_evaluate a v hv,FreeGroup.mk_toWord] at hh
  rw [lift_pathValue_formal]
  exact hh

theorem factorProducerGoal : MissingFinitePaths.FactorProducerGoal := by
  intro M X _ _ _ _ _ _ _ e τ hτ h1 htr hfaith hfactor hdiff
  exact produced_finite_paths e τ hτ htr hfaith h1 hfactor hdiff
end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching HochschildRare HochschildPaths
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem produced_finite_paths (hII : PopaTypeII.NoAbelianCorners M) :
    FinitePathTests τ := by
  classical
  intro C D T _ _ _ _ a r n w q hq hw η hη
  let g : T → FreeGroup (C ⊕ D) := fun t => pathHom (w t) (q t)
  let l : T → List (Letter (C × Bool) (Option (D × Bool))) := fun t => (g t).toWord.map pathEncode
  let L : ℕ := Finset.univ.sup (fun t => (l t).length)
  obtain ⟨v,hv,hgood⟩ := finite_unitary_moments e τ hτ htr hfaith h1 hII
    (pathCoefficients a) (pathCoefficients_norm a) (pathDegrees (D:=D)) none rfl L η hη
  refine ⟨fun d => v.toUnitary hv (FreeGroup.of d),fun t => ?_⟩
  have hlen : (l t).length≤L := Finset.le_sup (f:=fun t => (l t).length) (Finset.mem_univ t)
  have hdeg : degree pathDegrees (l t) ≠ 1 := by
    dsimp [l]
    rw [pathEncode_degree,FreeGroup.mk_toWord]
    obtain ⟨s,b,hpos,huniq⟩ := hw t
    exact freshProjection_pathHom_ne_one (w t) s b hpos huniq (q t) (hq t)
  have hh := hgood (l t) hlen hdeg
  dsimp [l] at hh
  rw [pathEncode_evaluate a v hv,FreeGroup.mk_toWord] at hh
  rw [lift_pathValue_formal]
  exact hh

end PopaCenter

end

end OAI
