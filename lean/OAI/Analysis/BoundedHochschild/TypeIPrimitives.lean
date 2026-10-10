import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CommutativePrimitives
import OAI.Analysis.BoundedHochschild.AtomicPrimitives
import OAI.Analysis.BoundedHochschild.TypeIResolution

namespace OAI

/-!
# Bounded primitives for finite type-I algebras with arbitrary center

For an algebra admitting a faithful normal trace, homogeneous central blocks supply local
bounded primitives. Gluing these primitives gives the degree-dependent norm bound without
an atomicity assumption on the center.
-/

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTypeILocal HochschildCorners HochschildAtomic FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_finite_typeI
    (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hI : TypeICentralSummand (1:M))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ (1+n)*‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  classical
  obtain ⟨s,hs,horth,htotal⟩ := exists_homogeneous_resolution e τ hτ htr hfaith hI
  let I := s
  let Z (p : I) := (hs p.val p.property).central
  have hex (p : I) : ∃ g : Cochain (Corner p.val (Z p).1) n,
      ‖g‖≤‖f‖ ∧ ∀ x, differentialValue g x=cornerRestrict p.val (Z p).1 (Z p).2 f x := by
    obtain ⟨d,E,i,hp⟩ := (hs p.val p.property).matrix
    obtain ⟨g,hg,he⟩ := primitive_of_abelian_matrix_diagonal (cornerPredualEquiv p.val (Z p).1 e)
      E i hp (cornerRestrict p.val (Z p).1 (Z p).2 f)
      (fun x => by rw [differential_cornerRestrict,hf,map_zero])
    exact ⟨g,hg.trans (cornerRestrict_norm p.val (Z p).1 (Z p).2 f),he⟩
  choose g hg he using hex
  let b : I → Cochain M n := fun p => cornerExtend p.val (Z p).1 (Z p).2 (g p)
  obtain ⟨G,hG,hGF⟩ := primitive_of_central_cut_primitives e
    (HochschildSakai.mul_hasPreadjoint e) (fun p : I => p.val)
    (fun p => (Z p).1) (fun p a => ((Z p).2 a).eq)
    (fun p q hne => horth p.property q.property (fun heq => hne (Subtype.ext heq)))
    (fun x hx => htotal x (fun p hp => hx ⟨p,hp⟩))
    f hf b (fun p x => cornerExtend_support p.val (Z p).1 (Z p).2 (g p) x)
    (fun p => cornerExtend_primitive p.val (Z p).1 (Z p).2 f (g p) (he p))
    ‖f‖ (norm_nonneg _)
    (fun p => (cornerExtend_norm p.val (Z p).1 (Z p).2 (g p)).trans (hg p))
  exact ⟨G,by simpa only [add_mul,one_mul] using hG,hGF⟩

end BoundedHochschild

end

end OAI
