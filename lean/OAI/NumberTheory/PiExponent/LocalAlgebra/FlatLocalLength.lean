import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B]

theorem simple_baseChange_of_map_maximalIdeal
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    IsSimpleModule B (B ⊗[A] M) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := A) (M := M)).mp inferInstance
  have hJmax : J = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hJ
  subst J
  have : IsSimpleModule B (B ⧸ IsLocalRing.maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal))
  let eB : (B ⊗[A] M) ≃ₗ[B] (B ⧸ IsLocalRing.maximalIdeal B) :=
    (e.baseChange A B M (A ⧸ IsLocalRing.maximalIdeal A)).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (IsLocalRing.maximalIdeal A)).toLinearEquiv.symm.trans
        (Submodule.quotEquivOfEq _ _ hmax))
  exact IsSimpleModule.congr eB

theorem length_baseChange_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) = Module.length A M := by
  induction hM with
  | of_subsingleton =>
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    have : IsSimpleModule B (B ⊗[A] (M ⧸ N)) :=
      simple_baseChange_of_map_maximalIdeal hmax
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hinj : Function.Injective (N.subtype.baseChange B) :=
      Module.Flat.lTensor_preserves_injective_linearMap N.subtype
        (Submodule.subtype_injective N)
    have hsurj : Function.Surjective (N.mkQ.baseChange B) :=
      LinearMap.lTensor_surjective B (Submodule.mkQ_surjective N)
    have hbaseexact : Function.Exact (N.subtype.baseChange B) (N.mkQ.baseChange B) :=
      Module.Flat.lTensor_exact B hexact
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hB := Module.length_eq_add_of_exact (N.subtype.baseChange B)
      (N.mkQ.baseChange B) hinj hsurj hbaseexact
    calc
      Module.length B (B ⊗[A] M) =
          Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) := hB
      _ = Module.length A N + Module.length A (M ⧸ N) := by
        rw [ih, Module.length_eq_one B (B ⊗[A] (M ⧸ N)),
          Module.length_eq_one A (M ⧸ N)]
      _ = Module.length A M := hA.symm

theorem finiteLength_baseChange_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    IsFiniteLength B (B ⊗[A] M) := by
  apply Module.length_ne_top_iff.mp
  rw [length_baseChange_of_flat_local hmax hM]
  exact Module.length_ne_top_iff.mpr hM

theorem length_quotient_map_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  calc
    Module.length B (B ⧸ I.map (algebraMap A B)) =
        Module.length B (B ⊗[A] (A ⧸ I)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq
    _ = Module.length A (A ⧸ I) := length_baseChange_of_flat_local hmax hI

end PiExponentJets.W25

end

end OAI
