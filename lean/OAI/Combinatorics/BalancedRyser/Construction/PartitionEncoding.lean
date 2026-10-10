import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

def encodeAssignment {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x : X) : Fin r → Fin n :=
  fun i => eL (eG.symm i) (label (eG.symm i) x)

@[simp] theorem encodeAssignment_apply_index
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x : X) (g : G) :
    encodeAssignment eG eL label x (eG g) = eL g (label g x) := by
  exact congrArg (fun g => eL g (label g x)) (eG.symm_apply_apply g)

theorem encodeAssignment_eq_iff
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x y : X) :
    encodeAssignment eG eL label x = encodeAssignment eG eL label y ↔
      (fun g => label g x) = (fun g => label g y) := by
  constructor
  · intro h
    funext g
    apply (eL g).injective
    simpa using congrFun h (eG g)
  · intro h
    funext i
    exact congrArg (eL (eG.symm i)) (congrFun h (eG.symm i))

theorem encodeAssignment_injective
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (h : Function.Injective (fun x g => label g x)) :
    Function.Injective (encodeAssignment eG eL label) := by
  intro x y hxy
  exact h ((encodeAssignment_eq_iff eG eL label x y).mp hxy)

theorem encodeAssignment_agree_iff
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x y : X) :
    (∃ i, encodeAssignment eG eL label x i = encodeAssignment eG eL label y i) ↔
      ∃ g, label g x = label g y := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨eG.symm i, (eL (eG.symm i)).injective hi⟩
  · rintro ⟨g, hg⟩
    exact ⟨eG g, by simpa using congrArg (eL g) hg⟩

def encodeLabel {G : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n) :
    Sigma Label ≃ Fin r × Fin n :=
  (Equiv.sigmaCongr eG eL).trans (Equiv.sigmaEquivProd (Fin r) (Fin n))

@[simp] theorem encodeLabel_apply
    {G : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n) (g : G) (l : Label g) :
    encodeLabel eG eL ⟨g, l⟩ = (eG g, eL g l) := rfl

theorem encodeAssignment_covered_iff
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x : X)
    (C : Finset (Fin r × Fin n)) :
    (∃ i, (i, encodeAssignment eG eL label x i) ∈ C) ↔
      ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈
        C.map (encodeLabel eG eL).symm.toEmbedding := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨eG.symm i, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨(i, encodeAssignment eG eL label x i), hi, ?_⟩
    apply (encodeLabel eG eL).injective
    simp [encodeAssignment]
  · rintro ⟨g, hg⟩
    rcases Finset.mem_map.mp hg with ⟨v, hv, hvg⟩
    have heq : v = (eG g, eL g (label g x)) := by
      have h := congrArg (encodeLabel eG eL) hvg
      simpa using h
    refine ⟨eG g, ?_⟩
    simpa [heq] using hv

end Balanced

end OAI
