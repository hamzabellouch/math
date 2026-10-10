import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarHomogeneous
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Module.Submodule.Equiv

namespace OAI

/-! # Homogeneous list chains are the ordinary finite-tuple bar chains -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

def tupleBarToList (n : ℕ) : ((Fin n → A) →₀ ℤ) →ₗ[ℤ] ListBarChain A :=
  Finsupp.lmapDomain ℤ ℤ List.ofFn

@[simp] theorem tupleBarToList_single (n : ℕ) (v : Fin n → A) (z : ℤ) :
    tupleBarToList n (Finsupp.single v z) = Finsupp.single (List.ofFn v) z := by
  simp only [tupleBarToList, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tupleBarToList_injective (n : ℕ) : Function.Injective (tupleBarToList (A := A) n) :=
  Finsupp.mapDomain_injective List.ofFn_injective

theorem tupleBarToList_range (n : ℕ) :
    LinearMap.range (tupleBarToList (A := A) n) = listBarGrade n := by
  have hr : Set.range (List.ofFn : (Fin n → A) → List A) = {v | v.length = n} := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact List.length_ofFn
    · intro hv
      change v.length = n at hv
      subst n
      exact ⟨v.get, List.ofFn_get v⟩
  have he := Finsupp.lmapDomain_supported ℤ ℤ
    (List.ofFn : (Fin n → A) → List A) Set.univ
  simpa only [Finsupp.supported_univ, Submodule.map_top, Set.image_univ, hr,
    tupleBarToList, listBarGrade] using he

def tupleBarListEquiv (n : ℕ) : ((Fin n → A) →₀ ℤ) ≃ₗ[ℤ] listBarGrade (A := A) n :=
  (LinearEquiv.ofInjective (tupleBarToList n) (tupleBarToList_injective n)).trans
    (LinearEquiv.ofEq _ _ (tupleBarToList_range n))

@[simp] theorem tupleBarListEquiv_val (n : ℕ) (z : (Fin n → A) →₀ ℤ) :
    (tupleBarListEquiv n z).val = tupleBarToList n z := rfl

end PolycyclicRecognition

end

end OAI
