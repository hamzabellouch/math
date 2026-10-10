import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Plancherel

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]
def trivialSubmoduleEquiv (G : Type*) [Group G] : Subrepresentation (Representation.trivial ℂ G ℂ) ≃o Submodule ℂ ℂ where
  toFun := Subrepresentation.toSubmodule
  invFun S := ⟨S, fun g x hx => by simpa only [Representation.trivial_apply] using hx⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

instance trivial_rep_irreducible (G : Type*) [Group G] : Representation.IsIrreducible (Representation.trivial ℂ G ℂ) :=
  (OrderIso.isSimpleOrder_iff (trivialSubmoduleEquiv G)).mpr inferInstance

omit [Fintype G] in
@[simp] lemma trivial_character (g : G) : (Representation.trivial ℂ G ℂ).character g = 1 := by
  simp [Representation.character, Representation.trivial]

def trivialIndex (G : Type*) [Group G] [Fintype G] : IrreducibleIndex G :=
  (irreducibleRep_complete (Representation.trivial ℂ G ℂ)).choose

lemma trivialIndex_equiv :
    Nonempty (Representation.Equiv (irreducibleRep (trivialIndex G))
      (Representation.trivial ℂ G ℂ)) :=
  (irreducibleRep_complete (Representation.trivial ℂ G ℂ)).choose_spec.1

lemma trivialIndex_unique (c : IrreducibleIndex G) :
    Nonempty (Representation.Equiv (Representation.trivial ℂ G ℂ) (irreducibleRep c)) ↔
      c = trivialIndex G := by
  constructor
  · rintro ⟨e⟩
    exact (irreducibleRep_complete (Representation.trivial ℂ G ℂ)).choose_spec.2 c ⟨e.symm⟩
  · rintro rfl
    obtain ⟨e⟩ := trivialIndex_equiv (G := G)
    exact ⟨e.symm⟩

@[simp] lemma irreducibleDegree_trivial : irreducibleDegree (trivialIndex G) = 1 := by
  obtain ⟨e⟩ := trivialIndex_equiv (G := G)
  simpa [irreducibleDegree] using e.toLinearEquiv.finrank_eq

@[simp] lemma irreducibleRep_trivial_apply (g : G) :
    irreducibleRep (trivialIndex G) g = 1 := by
  obtain ⟨e⟩ := trivialIndex_equiv (G := G)
  apply LinearMap.ext
  intro x
  apply e.toLinearEquiv.injective
  simpa using LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x

lemma complexFourier_trivial (a : G → ℂ) :
    complexFourier (irreducibleRep (trivialIndex G)) a = (∑ g, a g) • 1 := by
  simp only [complexFourier, irreducibleRep_trivial_apply, Finset.sum_smul]

lemma complexFourier_uniform (c : IrreducibleIndex G) :
    complexFourier (irreducibleRep c) (fun _ => (Fintype.card G : ℂ)⁻¹) =
      if c = trivialIndex G then 1 else 0 := by
  have hk : centralCharacterKernel (Representation.trivial ℂ G ℂ) =
      fun _ => (Fintype.card G : ℂ)⁻¹ := by
    funext g
    simp [centralCharacterKernel, trivial_character]
  rw [← hk, centralCharacterKernel_fourier, trivialIndex_unique]
  split_ifs <;> rfl

lemma complexFourier_centered (a : G → ℂ) (z : ℂ) (c : IrreducibleIndex G) :
    complexFourier (irreducibleRep c) (fun g => a g - z / Fintype.card G) =
      complexFourier (irreducibleRep c) a -
        z • (if c = trivialIndex G then 1 else 0) := by
  rw [← complexFourier_uniform]
  simp only [complexFourier, Finset.smul_sum,
    smul_smul, div_eq_mul_inv]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  exact sub_smul (R := ℂ) (M := Module.End ℂ (irreducibleSpace c))
    (a g) (z * (Fintype.card G : ℂ)⁻¹) ((irreducibleRep c) g)

end
end PartialPermutation
end

end OAI
