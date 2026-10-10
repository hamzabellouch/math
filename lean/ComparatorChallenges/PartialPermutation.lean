import Mathlib

namespace OAI

open scoped Classical BigOperators ComplexConjugate MonoidAlgebra
namespace PartialPermutation
noncomputable section

def IsUnitary {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ρ : Representation ℂ G V) : Prop :=
  ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
def hsNormSq (A : Module.End ℂ V) : ℝ :=
  (LinearMap.trace ℂ V (LinearMap.adjoint A * A)).re

end

def complexFourier {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℂ) : Module.End ℂ V := ∑ g, f g • ρ g

section
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
noncomputable def componentSimple (c : isotypicComponents ℂ[G] ρ.asModule) :
    Submodule ℂ[G] ρ.asModule := c.property.choose

instance components_finite : Finite (isotypicComponents ℂ[G] ρ.asModule) := by
  let : IsNoetherian ℂ[G] ρ.asModule := isNoetherian_of_tower ℂ inferInstance
  infer_instance

end

section
variable (G : Type*) [Group G] [Fintype G]
def regularRep : Representation ℂ G (EuclideanSpace ℂ G) where
  toFun g :=
    { toFun := fun f => WithLp.toLp 2 (fun h => f (g⁻¹ * h))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f h; simp
  map_mul' := by
    intro x y
    ext f h
    change f ((x * y)⁻¹ * h) = f (y⁻¹ * (x⁻¹ * h))
    simp [mul_assoc]

end

section
variable {G : Type*} [Group G] [Fintype G]
abbrev IrreducibleIndex (G : Type*) [Group G] [Fintype G] :=
  isotypicComponents ℂ[G] (regularRep G).asModule

noncomputable instance irreducibleIndex_fintype : Fintype (IrreducibleIndex G) :=
  Fintype.ofFinite _

abbrev irreducibleSpace (c : IrreducibleIndex G) :=
  (Subrepresentation.ofSubmodule' (componentSimple (regularRep G) c)).toSubmodule

abbrev irreducibleDegree (c : IrreducibleIndex G) := Module.finrank ℂ (irreducibleSpace c)

end

def mass {G : Type*} [Fintype G] (f : G → ℝ) : ℝ := ∑ g, f g

def LeftCosetCap {G : Type*} [Group G] [Fintype G]
    (f : G → ℝ) (H : Subgroup G) (B : ℝ) : Prop :=
  by classical exact ∀ g, ∑ h : H, f (g * h) ≤ B / H.index

def blockSubgroup {X : Type*} (M : Set X) : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ x, x ∉ M → g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x hx
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Equiv.Perm.mul_apply, hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    exact ((Equiv.eq_symm_apply g).mpr (hg x hx)).symm

def inverseDegreeSum (G : Type*) [Group G] [Fintype G] (u : ℝ) : ℝ :=
  ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ)^(-u)

def symmetricInverseDegreeSum (n : ℕ) (u : ℝ) : ℝ :=
  inverseDegreeSum (Equiv.Perm (Fin n)) u

def symmetricDegreeConstant (u : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = symmetricInverseDegreeSum n u}

def ComplementaryCosetsFiniteStatement : Prop :=
  ∀ (X : Type*) [Fintype X] [DecidableEq X] (b : ℕ) (_ : 0 < b) (M : Fin b → Set X),
    (∀ i, (M i).Nonempty) →
    Pairwise (fun i j => Disjoint (M i) (M j)) → (⋃ i, M i) = Set.univ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm X) V),
      Representation.IsIrreducible ρ → IsUnitary ρ →
      ∀ (f : Equiv.Perm X → ℝ) (B u : ℝ),
      (∀ g, 0 ≤ f g) → mass f ≤ 1 → 0 < u →
      (∀ i, LeftCosetCap f (blockSubgroup (M i)) B) →
      (hsNormSq (complexFourier ρ (fun g => f g)) ≤
        b * B * symmetricDegreeConstant u *
          (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b : ℝ))) ∧
      (‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => f g))‖^2 ≤
        b * B * symmetricDegreeConstant u *
          (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b : ℝ)))

theorem complementaryCosets_finite : ComplementaryCosetsFiniteStatement := by
  sorry

end
end PartialPermutation

end OAI
