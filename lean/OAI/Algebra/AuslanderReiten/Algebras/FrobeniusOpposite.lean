import OAI.Algebra.AuslanderReiten.Algebras.TensorFrobenius

namespace OAI

noncomputable section

namespace ArExplicit.FrobeniusTrace

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
variable (τ : FrobeniusTrace k R)
variable (hsym : ∀ a b, τ.trace (a * b) = τ.trace (b * a))

def opposite : FrobeniusTrace k Rᵐᵒᵖ where
  trace :=
    { toFun := fun a => τ.trace a.unop
      map_add' a b := τ.trace.map_add a.unop b.unop
      map_smul' a b := τ.trace.map_smul a b.unop }
  separates a ha := by
    apply MulOpposite.unop_injective
    change a.unop = 0
    apply τ.separates
    intro b
    rw [hsym]
    exact ha (MulOpposite.op b)

@[simp] theorem opposite_trace (a : Rᵐᵒᵖ) : (opposite τ hsym).trace a = τ.trace a.unop := rfl

theorem opposite_symmetric (a b : Rᵐᵒᵖ) :
    (opposite τ hsym).trace (a * b) = (opposite τ hsym).trace (b * a) :=
  hsym b.unop a.unop

end ArExplicit.FrobeniusTrace

namespace ArExplicit

variable (k : Type*) [Field k] (q : k)

def AOppositeFrobeniusTrace : FrobeniusTrace k (A k q)ᵐᵒᵖ :=
  (AFrobeniusTrace k q).opposite (A_trace_symmetric k q)

instance : Module.Injective (A k q)ᵐᵒᵖ (A k q)ᵐᵒᵖ :=
  (AOppositeFrobeniusTrace k q).regular_injective

open scoped TensorProduct

def AEnvelopingFrobeniusTrace : FrobeniusTrace k (A k q ⊗[k] (A k q)ᵐᵒᵖ) :=
  (AFrobeniusTrace k q).tensor (AOppositeFrobeniusTrace k q)

theorem AEnveloping_trace_symmetric (a b : A k q ⊗[k] (A k q)ᵐᵒᵖ) :
    (AEnvelopingFrobeniusTrace k q).trace (a * b) = (AEnvelopingFrobeniusTrace k q).trace (b * a) :=
  FrobeniusTrace.tensorTrace_mul_comm _ _ (A_trace_symmetric k q)
    ((AFrobeniusTrace k q).opposite_symmetric (A_trace_symmetric k q)) a b

end ArExplicit

end

end OAI
