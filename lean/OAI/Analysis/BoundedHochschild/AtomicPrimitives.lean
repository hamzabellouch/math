import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.FiniteFactorPrimitives
import OAI.Analysis.BoundedHochschild.CornerCochains
import OAI.Analysis.BoundedHochschild.AtomicResolution

namespace OAI

/-! Bounded primitives over an atomic finite center. -/

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildAtomic HochschildCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_atomic_finite
    (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hatomic : AtomicCenter M)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ (12+n)*‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  classical
  let I := {p : M // CentralAtom p}
  have hex (p : I) : ∃ g : Cochain (Corner p.val p.property.1) n,
      ‖g‖≤12*‖f‖ ∧ ∀ x, differentialValue g x=cornerRestrict p.val p.property.1 p.property.2.1 f x := by
    let ec := cornerPredualEquiv p.val p.property.1 e
    let tc := cornerTrace p.val p.property.1 τ
    obtain ⟨g,hg,he⟩ := primitive_of_finite_factor ec tc
      (cornerTrace_normal p.val p.property.1 e τ hτ)
      (cornerTrace_one p.val p.property.1 τ hfaith p.property.2.2.1)
      (cornerTrace_tracial p.val p.property.1 τ htr)
      (cornerTrace_faithful p.val p.property.1 τ hfaith p.property.2.2.1)
      (central_atom_corner_factor e p.property)
      (cornerRestrict p.val p.property.1 p.property.2.1 f)
      (fun x => by rw [differential_cornerRestrict,hf,map_zero])
    exact ⟨g,hg.trans (mul_le_mul_of_nonneg_left
      (cornerRestrict_norm p.val p.property.1 p.property.2.1 f) (by norm_num)),he⟩
  choose g hg he using hex
  let b : I → Cochain M n := fun p => cornerExtend p.val p.property.1 p.property.2.1 (g p)
  obtain ⟨G,hG,hGF⟩ := primitive_of_central_cut_primitives e
    (HochschildSakai.mul_hasPreadjoint e) (fun p : I => p.val)
    (fun p => p.property.1) (fun p a => (p.property.2.1 a).eq)
    (fun p q hne => central_atoms_orthogonal p.property q.property
      (fun heq => hne (Subtype.ext heq)))
    (fun x hx => central_atoms_total e τ hτ htr hfaith hatomic x (fun p hp => hx ⟨p,hp⟩))
    f hf b (fun p x => cornerExtend_support p.val p.property.1 p.property.2.1 (g p) x)
    (fun p => cornerExtend_primitive p.val p.property.1 p.property.2.1 f (g p) (he p))
    (12*‖f‖) (by positivity)
    (fun p => (cornerExtend_norm p.val p.property.1 p.property.2.1 (g p)).trans (hg p))
  exact ⟨G,by simpa only [add_mul] using hG,hGF⟩

end BoundedHochschild

end

end OAI
