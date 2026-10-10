import Mathlib
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.BooneHigman.Contracted
import OAI.GroupTheory.SimpleOvergroups.TruncatedAlgebra

namespace OAI


namespace SimpleFInftyOvergroups.SemanticEncoding
noncomputable section
open FiniteAlgebraicEnvelopes
open scoped Classical

structure NormalPresentation (M K : Type*) [Monoid M] [MonoidWithZero K] where
  q : M →* K
  surjective : Function.Surjective q
  normal : M → M
  omega : M
  zero : q omega = 0
  complete : ∀ u v, q u = q v ↔ normal u = normal v
  idempotent : ∀ u, normal (normal u) = normal u
  fixesZero : normal omega = omega

namespace NormalPresentation
variable {M K : Type*} [Monoid M] [MonoidWithZero K] (P : NormalPresentation M K)
variable (k : Type*) [CommRing k]

 theorem q_normal (w : M) : P.q (P.normal w) = P.q w :=
  (P.complete _ _).mpr (P.idempotent w)

 theorem normal_eq_zero_iff (w : M) : P.normal w = P.omega ↔ P.q w = 0 := by
  rw [← P.fixesZero, ← P.complete, P.zero]

def representative (h : K) : M := P.normal (P.surjective h).choose

 theorem representative_q (w : M) : P.representative (P.q w) = P.normal w := by
  apply (P.complete _ _).mp
  exact (P.surjective _).choose_spec

 theorem q_representative (h : K) : P.q (P.representative h) = h :=
  (P.q_normal _).trans (P.surjective h).choose_spec

 theorem representative_injective : Function.Injective P.representative := by
  intro a b h
  simpa only [P.q_representative] using congrArg P.q h

def algebraMap : MonoidAlgebra k M →ₐ[k] Contracted.Algebra k K :=
  (Contracted.quotient k K).comp (MonoidAlgebra.mapDomainAlgHom k k P.q)

@[simp] theorem algebraMap_single (w : M) (c : k) :
    P.algebraMap k (MonoidAlgebra.single w c) = Contracted.basis k K (P.q w) c := by
  simp [algebraMap, Contracted.basis]

def sectionMap : Contracted.Algebra k K →ₗ[k] MonoidAlgebra k M :=
  (Contracted.monoidBasis (k:=k) (H:=K)).constr k
    (fun h => MonoidAlgebra.single (P.representative h.val) 1)

 theorem sectionMap_basis (h : K) (c : k) :
    P.sectionMap k (Contracted.basis k K h c) =
      if h = 0 then 0 else MonoidAlgebra.single (P.representative h) c := by
  by_cases hh : h = 0
  · simp [hh]
  · have he : Contracted.basis k K h c = c • Contracted.basis k K h 1 := by
      simp only [Contracted.basis, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [he, map_smul, ite_eq_right hh]
    have hb := (Contracted.monoidBasis (k:=k) (H:=K)).constr_basis
      k (fun h => MonoidAlgebra.single (P.representative h.val) (1:k)) ⟨h,hh⟩
    rw [Contracted.monoidBasis_apply] at hb
    change P.sectionMap k (Contracted.basis k K h 1) = _ at hb
    rw [hb]
    simp

 theorem algebraMap_section (x : Contracted.Algebra k K) :
    P.algebraMap k (P.sectionMap k x) = x := by
  have he : (P.algebraMap k).toLinearMap.comp (P.sectionMap k) = LinearMap.id := by
    apply (Contracted.monoidBasis (k:=k) (H:=K)).ext
    intro h
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Contracted.monoidBasis_apply, P.sectionMap_basis, ite_eq_right h.property,
      P.algebraMap_single, P.q_representative, LinearMap.id_apply]
  exact LinearMap.congr_fun he x

 theorem sectionMap_injective : Function.Injective (P.sectionMap k) :=
  Function.LeftInverse.injective (P.algebraMap_section k)

 theorem algebraMap_surjective : Function.Surjective (P.algebraMap k) :=
  Function.RightInverse.surjective (P.algebraMap_section k)

 theorem section_algebraMap_single (w : M) (c : k) :
    P.sectionMap k (P.algebraMap k (MonoidAlgebra.single w c)) =
      if P.normal w = P.omega then 0 else MonoidAlgebra.single (P.normal w) c := by
  rw [P.algebraMap_single, P.sectionMap_basis, P.representative_q, P.normal_eq_zero_iff]

 theorem section_algebraMap {m : ℕ} (C : BoundedEncoding.WordCalculus M m)
    (hn : C.normal = P.normal) (hz : C.omega = P.omega) (a : MonoidAlgebra k M) :
    P.sectionMap k (P.algebraMap k a) = C.collect k a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single w c => simp only [P.section_algebraMap_single, C.collect_single, hn, hz]

 theorem algebraMap_eq_iff_collect {m : ℕ} (C : BoundedEncoding.WordCalculus M m)
    (hn : C.normal = P.normal) (hz : C.omega = P.omega) (a b : MonoidAlgebra k M) :
    P.algebraMap k a = P.algebraMap k b ↔ C.collect k a = C.collect k b := by
  rw [← P.section_algebraMap k C hn hz a, ← P.section_algebraMap k C hn hz b]
  exact P.sectionMap_injective k |>.eq_iff.symm

end NormalPresentation
end
end SimpleFInftyOvergroups.SemanticEncoding

end OAI
