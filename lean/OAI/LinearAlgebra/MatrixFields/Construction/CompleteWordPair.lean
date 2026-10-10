import Mathlib

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.PermutationMatching

variable {C : Type*} {P X Y : C → Type*}

structure CompleteWordPair (P X Y : C → Type*) where
  left : ∀ c, P c → X c
  right : ∀ c, P c → Y c

abbrev HalfClassPermutations (P : C → Type*) :=
  (∀ c, Equiv.Perm (P c)) × (∀ c, Equiv.Perm (P c))

instance completeWordPairMulAction :
    MulAction (HalfClassPermutations P) (CompleteWordPair P X Y) where
  smul g w :=
    { left := fun c i => w.left c ((g.1 c).symm i)
      right := fun c i => w.right c ((g.2 c).symm i) }
  one_smul w := by cases w; rfl
  mul_smul g h w := rfl

@[simp] theorem smul_completeWordPair_left (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) (c : C) (i : P c) :
    (g • w).left c i = w.left c ((g.1 c).symm i) := rfl

@[simp] theorem smul_completeWordPair_right (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) (c : C) (i : P c) :
    (g • w).right c i = w.right c ((g.2 c).symm i) := rfl

end MatrixMultiplication.PermutationMatching

end MatrixAllFields

end OAI
