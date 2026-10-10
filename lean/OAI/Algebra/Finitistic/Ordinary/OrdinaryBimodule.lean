import OAI.Algebra.Finitistic.Ordinary.OrdinaryCompression
import Mathlib.Algebra.Algebra.Opposite

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
abbrev Enveloping (k B : Type u) [Field k] [Ring B] [Algebra k B] := B ⊗[k] Bᵐᵒᵖ

/-- O from the genuine dg B-bimodule, as an ordinary finite sum of its terms. -/
def BimoduleO (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ) := Compression P a l

namespace BimoduleO
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
instance : AddCommGroup (BimoduleO P a l) := inferInstanceAs (AddCommGroup (Compression P a l))
instance : Module k (BimoduleO P a l) := inferInstanceAs (Module k (Compression P a l))
instance : Module (Enveloping k B) (BimoduleO P a l) := inferInstanceAs (Module (Enveloping k B) (Compression P a l))
instance : IsScalarTower k (Enveloping k B) (BimoduleO P a l) := inferInstanceAs (IsScalarTower k (Enveloping k B) (Compression P a l))
instance : Module B (BimoduleO P a l) :=
  Module.compHom (Compression P a l) (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := Bᵐᵒᵖ)).toRingHom
instance : Module Bᵐᵒᵖ (BimoduleO P a l) :=
  Module.compHom (Compression P a l) (Algebra.TensorProduct.includeRight (R := k) (A := B)).toRingHom
instance : Module (ChainAlgebra k l) (BimoduleO P a l) :=
  inferInstanceAs (Module (ChainAlgebra k l) (Compression P a l))
instance : IsScalarTower k (ChainAlgebra k l) (BimoduleO P a l) :=
  inferInstanceAs (IsScalarTower k (ChainAlgebra k l) (Compression P a l))

instance : SMulCommClass (ChainAlgebra k l) (Enveloping k B) (BimoduleO P a l) :=
  inferInstanceAs (SMulCommClass (ChainAlgebra k l) (Enveloping k B) (Compression P a l))

instance towerLeft : IsScalarTower k B (BimoduleO P a l) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c v
  change (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := Bᵐᵒᵖ) ((algebraMap k B) c)) •
    (v : Compression P a l) = c • v
  rw [AlgHom.commutes]
  exact algebraMap_smul (Enveloping k B) c v

instance towerRight : IsScalarTower k Bᵐᵒᵖ (BimoduleO P a l) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c v
  change (Algebra.TensorProduct.includeRight (R := k) (A := B) ((algebraMap k Bᵐᵒᵖ) c)) •
    (v : Compression P a l) = c • v
  rw [AlgHom.commutes]
  exact algebraMap_smul (Enveloping k B) c v

instance commuteLeftRight : SMulCommClass B Bᵐᵒᵖ (BimoduleO P a l) where
  smul_comm b r v := by
    change ((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) : Enveloping k B) •
      (((1:B) ⊗ₜ[k] r) • (v : Compression P a l)) =
      ((1:B) ⊗ₜ[k] r) • ((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) • (v : Compression P a l))
    rw [← mul_smul, ← mul_smul]
    simp [Algebra.TensorProduct.tmul_mul_tmul]

instance commuteChainLeft : SMulCommClass (ChainAlgebra k l) B (BimoduleO P a l) where
  smul_comm x b v := by
    change x • (((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) : Enveloping k B) • (v : Compression P a l)) =
      ((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) : Enveloping k B) • (x • (v : Compression P a l))
    exact smul_comm _ _ _

instance commuteChainRight : SMulCommClass (ChainAlgebra k l) Bᵐᵒᵖ (BimoduleO P a l) where
  smul_comm x b v := by
    change x • ((((1:B) ⊗ₜ[k] b) : Enveloping k B) • (v : Compression P a l)) =
      (((1:B) ⊗ₜ[k] b) : Enveloping k B) • (x • (v : Compression P a l))
    exact smul_comm _ _ _

/-- The left B tensor C action takes values in actual right-B-linear maps. -/
def leftAction : (B ⊗[k] ChainAlgebra k l) →ₐ[k] Module.End Bᵐᵒᵖ (BimoduleO P a l) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k Bᵐᵒᵖ (BimoduleO P a l))
    (Algebra.lsmul k Bᵐᵒᵖ (BimoduleO P a l)) (by
      intro b x
      ext v
      exact (smul_comm x b v).symm)

instance leftModule : Module (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) :=
  Module.compHom (BimoduleO P a l) (leftAction P a l).toRingHom

instance towerTensor : IsScalarTower k (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) where
  smul_assoc c x v := by
    change leftAction P a l (c • x) v = c • leftAction P a l x v
    rw [map_smul]
    rfl

instance commuteTensorRight : SMulCommClass (B ⊗[k] ChainAlgebra k l) Bᵐᵒᵖ (BimoduleO P a l) where
  smul_comm x b v := (leftAction P a l x).map_smul b v

instance finiteDimensional [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (BimoduleO P a l) := inferInstanceAs (FiniteDimensional k (Compression P a l))
end BimoduleO
end LittleFinitistic.OrdinarySimulation

end

end OAI
