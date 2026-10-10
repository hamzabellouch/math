import Mathlib
import OAI.Analysis.Commutator.FreeActionGroup

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable {G : Type*} [Group G] (α : G → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)
  (h1 : ∀ i a, α 1 i a=a)
  (hmul : ∀ g h i a, α (g*h) i a=α g i (α h i a))

include h1 hmul in
lemma action_inv (g : G) (x : t.functional.GNS) :
    action t S (α g⁻¹) (hmem g⁻¹) (hτ g⁻¹) hfree hgen
      (action t S (α g) (hmem g) (hτ g) hfree hgen x)=x := by
  have h := congrArg (fun T : t.functional.GNS →ₗᵢ[ℂ] t.functional.GNS => T x)
    (action_mul t S hfree hgen α hmem hτ hmul g⁻¹ g)
  rw [inv_mul_cancel,action_one t S hfree hgen α hmem hτ h1] at h
  exact h.symm

def equiv (g : G) : t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS where
  toLinearEquiv :=
    { (action t S (α g) (hmem g) (hτ g) hfree hgen).toLinearMap with
      invFun := action t S (α g⁻¹) (hmem g⁻¹) (hτ g⁻¹) hfree hgen
      left_inv := action_inv t S hfree hgen α hmem hτ h1 hmul g
      right_inv := by
        intro x
        change action t S (α g) (hmem g) (hτ g) hfree hgen
          (action t S (α g⁻¹) (hmem g⁻¹) (hτ g⁻¹) hfree hgen x)=x
        simpa only [inv_inv] using action_inv t S hfree hgen α hmem hτ h1 hmul g⁻¹ x }
  norm_map' := (action t S (α g) (hmem g) (hτ g) hfree hgen).norm_map

@[simp] lemma equiv_apply (g : G) (x : t.functional.GNS) :
    equiv t S hfree hgen α hmem hτ h1 hmul g x=
      action t S (α g) (hmem g) (hτ g) hfree hgen x := rfl

def representation : G →* (t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS) where
  toFun := equiv t S hfree hgen α hmem hτ h1 hmul
  map_one' := by
    ext x
    change action t S (α 1) (hmem 1) (hτ 1) hfree hgen x=x
    rw [action_one t S hfree hgen α hmem hτ h1]
    rfl
  map_mul' g h := by
    ext x
    change action t S (α (g*h)) (hmem (g*h)) (hτ (g*h)) hfree hgen x=
      action t S (α g) (hmem g) (hτ g) hfree hgen
        (action t S (α h) (hmem h) (hτ h) hfree hgen x)
    rw [action_mul t S hfree hgen α hmem hτ hmul]
    rfl

@[simp] lemma representation_apply (g : G) (x : t.functional.GNS) :
    representation t S hfree hgen α hmem hτ h1 hmul g x=
      action t S (α g) (hmem g) (hτ g) hfree hgen x := rfl

lemma representation_continuous [TopologicalSpace G]
    (hc : ∀ i a, Continuous fun g => α g i a) (x : t.functional.GNS) :
    Continuous fun g => representation t S hfree hgen α hmem hτ h1 hmul g x :=
  action_continuous t S α hmem hτ hc hfree hgen x

end Kadison.FreeWordAction

end

end
end

end OAI
