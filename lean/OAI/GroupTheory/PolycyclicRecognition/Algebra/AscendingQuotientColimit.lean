import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationColimit

namespace OAI

/-! # The concrete colimit of an ascending sequence of invariant relations

Every element is represented in the initial quotient. A class vanishes in the
quotient by the union precisely when it vanishes at a finite stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G] (A : Rep.{0} ℤ G)

abbrev RepresentationInvariant (N : Submodule ℤ A) : Prop :=
  ∀ g, N ≤ N.comap (A.ρ g)

def invariantQuotientMap {N M : Submodule ℤ A}
    (hN : RepresentationInvariant A N) (hM : RepresentationInvariant A M) (h : N ≤ M) :
    Rep.quotient A N hN ⟶ Rep.quotient A M hM :=
  Rep.ofHom ⟨N.mapQ M LinearMap.id h, fun g => by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl⟩

def ascendingQuotientDiagram (N : ℕ → Submodule ℤ A)
    (hN : ∀ n, RepresentationInvariant A (N n)) (hmono : Monotone N) :
    SequentialRepresentationDiagram G where
  obj n := Rep.quotient A (N n) (hN n)
  map _ _ h := invariantQuotientMap A _ _ (hmono h)
  map_id n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  map_comp i j k hij hjk := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

def ascendingQuotientColimit (N : ℕ → Submodule ℤ A)
    (hN : ∀ n, RepresentationInvariant A (N n)) (hmono : Monotone N)
    (M : Submodule ℤ A) (hM : RepresentationInvariant A M)
    (hNM : ∀ n, N n ≤ M) (hcover : ∀ x ∈ M, ∃ n, x ∈ N n) :
    (ascendingQuotientDiagram A N hN hmono).ColimitCocone (Rep.quotient A M hM) where
  ι n := invariantQuotientMap A (hN n) hM (hNM n)
  comm i j hij := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  surj x := by
    obtain ⟨y, rfl⟩ := M.mkQ_surjective x
    exact ⟨0, (N 0).mkQ y, rfl⟩
  zero_exact i x hx := by
    obtain ⟨y, rfl⟩ := (N i).mkQ_surjective x
    have hy : y ∈ M := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨n, hn⟩ := hcover y hy
    refine ⟨max i n, Nat.le_max_left _ _, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hmono (Nat.le_max_right i n) hn)

end PolycyclicRecognition

end

end OAI
