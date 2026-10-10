import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensor

namespace OAI

namespace ArExplicit.BalancedTensor

open TensorProduct

variable {k R F M S : Type*} [CommRing k] [Ring R] [Ring S]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

theorem smul_mem_relations (s : S) {z : F ⊗[k] M}
    (hz : z ∈ balancingRelations k R F M) : s • z ∈ balancingRelations k R F M := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨f, r, m, rfl⟩ := hz
      rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_comm s]
      exact Submodule.subset_span ⟨s • f, r, m, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [smul_add] using (balancingRelations k R F M).add_mem ihx ihy
  | smul c z hz ih =>
      rw [← smul_comm c s z]
      exact (balancingRelations k R F M).smul_mem c ih

def relationsAsLeft : Submodule S (F ⊗[k] M) where
  __ := (balancingRelations k R F M).toAddSubmonoid
  smul_mem' := fun s _ hz => smul_mem_relations s hz

instance (priority := 100) : Module S (BalancedTensor k R F M) :=
  Submodule.Quotient.module (relationsAsLeft (k := k) (R := R) (S := S) (F := F) (M := M))

@[simp] theorem smul_tmul (s : S) (f : F) (m : M) :
    s • tmul (k := k) (R := R) f m = tmul (s • f) m := rfl

variable [Algebra k S] [IsScalarTower k S F]

instance : IsScalarTower k S (BalancedTensor k R F M) where
  smul_assoc c s z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
        change Submodule.Quotient.mk ((c • s) • z) =
          (Submodule.Quotient.mk (c • s • z) : BalancedTensor k R F M)
        rw [smul_assoc]

instance : SMulCommClass k S (BalancedTensor k R F M) where
  smul_comm c s z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
        change Submodule.Quotient.mk (c • s • z) =
          (Submodule.Quotient.mk (s • c • z) : BalancedTensor k R F M)
        rw [smul_comm]

end ArExplicit.BalancedTensor

end OAI
