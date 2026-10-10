import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.Young
open Module Representation Finset

section Permutation
variable {K G X Y : Type*} [Field K] [Group G]
  [Fintype X] [Fintype Y] [MulAction G X] [MulAction G Y]

def permRep (K G X : Type*) [Field K] [Group G] [MulAction G X] :
    Representation K G (X → K) where
  toFun g := LinearMap.pi fun x => LinearMap.proj (g⁻¹ • x)
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

omit [Fintype X] in
@[simp] lemma permRep_apply (g : G) (f : X → K) (x : X) :
    permRep K G X g f x = f (g⁻¹ • x) := rfl

omit [Fintype X] in
@[simp] lemma permRep_single [DecidableEq X] (g : G) (x : X) (r : K) :
    permRep K G X g (Pi.single x r) = Pi.single (g • x) r := by
  ext y
  by_cases h : y = g • x
  · subst y
    simp
  · have h' : g⁻¹ • y ≠ x := by
      intro he
      apply h
      have hh := congrArg (fun z => g • z) he
      simpa using hh
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

def matrixInvariants (K G X Y : Type*) [Field K] [Group G]
    [MulAction G X] [MulAction G Y] : Submodule K (Matrix Y X K) where
  carrier := {M | ∀ g : G, ∀ y x, M (g • y) (g • x) = M y x}
  zero_mem' := by intro g y x; rfl
  add_mem' := by intro M N hM hN g y x; exact congrArg₂ (· + ·) (hM g y x) (hN g y x)
  smul_mem' := by intro r M hM g y x; exact congrArg (r * ·) (hM g y x)

omit [Fintype Y] in
lemma matrix_intertwining_iff [DecidableEq X] [DecidableEq Y] (M : Matrix Y X K) :
    (∀ g : G, (Matrix.toLin' M).comp (permRep K G X g) =
      (permRep K G Y g).comp (Matrix.toLin' M)) ↔ M ∈ matrixInvariants K G X Y := by
  constructor
  · intro h g y x
    have hh := congrFun (LinearMap.congr_fun (h g) (Pi.single x 1)) (g • y)
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using hh
  · intro h g
    apply LinearMap.toMatrix'.injective
    ext y x
    simp only [LinearMap.toMatrix'_apply, LinearMap.comp_apply, permRep_single,
      permRep_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    simpa using h g (g⁻¹ • y) x

def intertwinerMatrix [DecidableEq X] [DecidableEq Y] :
    (permRep K G X).IntertwiningMap (permRep K G Y) ≃ₗ[K] matrixInvariants K G X Y where
  toFun f := ⟨LinearMap.toMatrix' f.toLinearMap,
    (matrix_intertwining_iff (LinearMap.toMatrix' f.toLinearMap)).mp (by
      simpa using f.isIntertwining')⟩
  invFun M := ⟨Matrix.toLin' M.val, (matrix_intertwining_iff M.val).mpr M.property⟩
  left_inv f := by ext x; simp
  right_inv M := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; simp
  map_smul' r f := by apply Subtype.ext; simp

end Permutation

section Quotient
variable {K G Z : Type*} [Field K] [Group G] [MulAction G Z]

def orbitFunctions (K G Z : Type*) [Field K] [Group G] [MulAction G Z] :
    Submodule K (Z → K) where
  carrier := {f | ∀ g : G, ∀ z, f (g • z) = f z}
  zero_mem' := by intro g z; rfl
  add_mem' := by intro f h hf hh g z; exact congrArg₂ (· + ·) (hf g z) (hh g z)
  smul_mem' := by intro r f hf g z; exact congrArg (r * ·) (hf g z)

def orbitFunctionsEquiv : orbitFunctions K G Z ≃ₗ[K] (MulAction.orbitRel.Quotient G Z → K) where
  toFun f := Quotient.lift f.val (by
    intro x y h
    obtain ⟨g,hg⟩ := h
    rw [← hg]
    exact f.property g y)
  invFun f := ⟨fun z => f (Quotient.mk (MulAction.orbitRel G Z) z), by
    intro g z
    apply congrArg f
    exact Quotient.sound (show MulAction.orbitRel G Z (g • z) z from ⟨g,rfl⟩)⟩
  left_inv f := rfl
  right_inv f := by funext q; induction q using Quotient.inductionOn; rfl
  map_add' f h := by funext q; induction q using Quotient.inductionOn; rfl
  map_smul' r f := by funext q; induction q using Quotient.inductionOn; rfl

end Quotient

section OrbitGram
variable {K G X Y : Type*} [Field K] [Group G]
  [Fintype X] [Fintype Y] [MulAction G X] [MulAction G Y]

def matrixOrbitEquiv : matrixInvariants K G X Y ≃ₗ[K] orbitFunctions K G (Y × X) where
  toFun M := ⟨fun z => M.val z.1 z.2, fun g z => M.property g z.1 z.2⟩
  invFun f := ⟨fun y x => f.val (y,x), fun g y x => f.property g (y,x)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem perm_hom_finrank :
    finrank K ((permRep K G X).IntertwiningMap (permRep K G Y)) =
      Nat.card (MulAction.orbitRel.Quotient G (Y × X)) := by
  classical
  let e := (intertwinerMatrix (K := K) (G := G) (X := X) (Y := Y)).trans
    (matrixOrbitEquiv.trans orbitFunctionsEquiv)
  rw [e.finrank_eq]
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient G (Y × X))
  simp [Nat.card_eq_fintype_card]

end OrbitGram
end Foulkes.Young

end

end OAI
