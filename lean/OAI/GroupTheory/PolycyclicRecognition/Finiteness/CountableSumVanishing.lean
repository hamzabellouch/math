import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableSumPrefixes

namespace OAI

/-! # Countable sums of vanishing coefficients under FP-infinity -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
attribute [local instance 2300] Submodule.module
variable {G : Type} [Group G]

def sumPrefixGenerator (A : ℕ → Rep.{0} ℤ G) (n : ℕ) (i : Fin n) :
    A i ⟶ sumPrefixRepresentation A n := by
  classical
  let f := integralRepresentationSumInclusion A i.val
  exact Rep.ofHom ⟨{
    toFun x := ⟨f.hom x, by
      intro j hj
      exact integralRepresentationSumInclusion_ne A i.val j (by omega) x⟩
    map_add' x y := by apply Subtype.ext; exact map_add f.hom x y
    map_smul' r x := by apply Subtype.ext; exact f.hom.toLinearMap.map_smul r x }, fun g => by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact Rep.hom_comm_apply f g x⟩

def sumPrefixFromFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    integralRepresentationSum (fun i : Fin n => A i) ⟶ sumPrefixRepresentation A n :=
  integralRepresentationSumDesc _ _ (sumPrefixGenerator A n)

def sumPrefixToFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixRepresentation A n ⟶ integralRepresentationSum (fun i : Fin n => A i) :=
  Rep.ofHom ⟨{
    toFun x := DFinsupp.comapDomain Fin.val Fin.val_injective x.val
    map_add' x y := DFinsupp.comapDomain_add Fin.val Fin.val_injective x.val y.val
    map_smul' r x := DFinsupp.comapDomain_smul Fin.val Fin.val_injective r x.val }, fun g => by
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro i
      rfl⟩

theorem sumPrefixToFinite_injective (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    Function.Injective (sumPrefixToFinite A n).hom := by
  intro x y h
  apply Subtype.ext
  apply DFinsupp.ext
  intro i
  by_cases hi : i < n
  · exact congrArg (fun z => z ⟨i, hi⟩) h
  · exact (x.property i (by omega)).trans (y.property i (by omega)).symm

theorem sumPrefixGenerator_toFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) (i : Fin n) :
    sumPrefixGenerator A n i ≫ sumPrefixToFinite A n =
      integralRepresentationSumInclusion (fun j : Fin n => A j) i := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change DFinsupp.comapDomain Fin.val Fin.val_injective
    ((integralRepresentationSumInclusion A i.val).hom x) =
      (integralRepresentationSumInclusion (fun j : Fin n => A j) i).hom x
  rw [integralRepresentationSumInclusion_apply, integralRepresentationSumInclusion_apply]
  exact DFinsupp.comapDomain_single (β := fun j => (A j).V) Fin.val Fin.val_injective i x

theorem sumPrefixFromFinite_toFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixFromFinite A n ≫ sumPrefixToFinite A n =
      𝟙 (integralRepresentationSum (fun i : Fin n => A i)) := by
  apply integralRepresentationSum_hom_ext
  intro i
  change integralRepresentationSumInclusion (fun i : Fin n => A i) i ≫
    (integralRepresentationSumDesc _ _ (sumPrefixGenerator A n) ≫ sumPrefixToFinite A n) = _
  rw [← Category.assoc, integralRepresentationSumInclusion_desc,
    sumPrefixGenerator_toFinite, Category.comp_id]

def sumPrefixFiniteIso (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixRepresentation A n ≅ integralRepresentationSum (fun i : Fin n => A i) := by
  let : Mono (sumPrefixToFinite A n) :=
    (Rep.mono_iff_injective _).mpr (sumPrefixToFinite_injective A n)
  exact {
    hom := sumPrefixToFinite A n
    inv := sumPrefixFromFinite A n
    inv_hom_id := sumPrefixFromFinite_toFinite A n
    hom_inv_id := by
      apply (cancel_mono (sumPrefixToFinite A n)).mp
      rw [Category.assoc, sumPrefixFromFinite_toFinite, Category.comp_id, Category.id_comp] }

theorem sumPrefix_completeCohomology (A : ℕ → Rep.{0} ℤ G) (p n : ℕ)
    (hA : ∀ i, Subsingleton (ShiftedCompletedCohomology p (A i))) :
    Subsingleton (ShiftedCompletedCohomology p (sumPrefixRepresentation A n)) := by
  have hfinite := finiteSum_completeCohomology (fun i : Fin n => A i) p (fun i => hA i)
  let e := (shiftedCompletedCohomologyFunctor p).mapIso (sumPrefixFiniteIso A n)
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p (sumPrefixRepresentation A n))
  intro x
  apply e.toLinearEquiv.injective
  exact hfinite.elim _ _

theorem TypeFPInfinity.countableSum_completeCohomology (hG : TypeFPInfinity G)
    (A : ℕ → Rep.{0} ℤ G) (p : ℕ)
    (hA : ∀ i, Subsingleton (ShiftedCompletedCohomology p (A i))) :
    Subsingleton (ShiftedCompletedCohomology p (integralRepresentationSum A)) :=
  hG.shiftedCompleteCohomology_colimit_subsingleton p (sumPrefixDiagram A)
    (integralRepresentationSum A) (sumPrefixColimit A)
    (fun n => sumPrefix_completeCohomology A p n hA)

end PolycyclicRecognition

end

end OAI
