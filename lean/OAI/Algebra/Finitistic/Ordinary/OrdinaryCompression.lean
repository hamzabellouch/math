import OAI.Algebra.Finitistic.Ordinary.OrdinaryCochain
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.TensorProduct.Maps

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Forgetting to k uses the actual restriction-of-scalars functor on complexes. -/
abbrev underlyingComplex (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (.up ℤ)).obj P

/-- Ordinary finite compression of the actual dg A-module P on [a,a+l].
Take A=B tensor Bᵐᵒᵖ for a genuine dg B-bimodule. -/
def Compression (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ) :=
  ∀ i : Fin (l+1), P.X (a + (i.val : ℤ))

namespace Compression
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)
instance : AddCommGroup (Compression P a l) :=
  inferInstanceAs (AddCommGroup (∀ i : Fin (l+1), P.X (a + (i.val : ℤ))))
instance : Module k (Compression P a l) :=
  inferInstanceAs (Module k (OrdinaryTerms (intervalTerms (underlyingComplex (k := k) P) a l)))
instance : Module A (Compression P a l) :=
  inferInstanceAs (Module A (∀ i : Fin (l+1), P.X (a + (i.val : ℤ))))
instance : Module (ChainAlgebra k l) (Compression P a l) :=
  cochainModule (underlyingComplex (k := k) P) a l
instance : IsScalarTower k (ChainAlgebra k l) (Compression P a l) :=
  OrdinaryTerms.scalarTower _ _ (intervalDifferential_square (underlyingComplex (k := k) P) a l)

instance scalarTowerA : IsScalarTower k A (Compression P a l) where
  smul_assoc c r v := by
    funext i
    change (c • r) • v i = (algebraMap k A c) • r • v i
    rw [Algebra.smul_def, mul_smul]

instance : SMulCommClass (ChainAlgebra k l) A (Compression P a l) where
  smul_comm x r v := by
    let (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k A)
    let (n : ℤ) : IsScalarTower k A (P.X n) := IsScalarTower.of_compHom k A (P.X n)
    let (i : Fin (l+1)) : Module A (intervalTerms (underlyingComplex (k := k) P) a l i) := inferInstanceAs (Module A (P.X (a + (i.val : ℤ))))
    let (i : Fin (l+1)) : SMulCommClass k A (intervalTerms (underlyingComplex (k := k) P) a l i) := inferInstanceAs (SMulCommClass k A (P.X (a + (i.val : ℤ))))
    change OrdinaryTerms.action (intervalTerms (underlyingComplex (k := k) P) a l) (intervalDifferential (underlyingComplex (k := k) P) a l) x (r • v) = r • OrdinaryTerms.action (intervalTerms (underlyingComplex (k := k) P) a l) (intervalDifferential (underlyingComplex (k := k) P) a l) x v
    apply OrdinaryTerms.action_commutes
    intro i j r v
    exact (P.d (a + (i.val : ℤ)) (a + (j.val : ℤ))).hom.map_smul r v

/-- The commuting actions give the actual tensor-algebra representation. -/
def tensorAction : (A ⊗[k] ChainAlgebra k l) →ₐ[k] Module.End k (Compression P a l) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k (Compression P a l))
    (Algebra.lsmul k k (Compression P a l)) (by
      intro r x
      ext v
      change r • (x • v) = x • (r • v)
      exact (smul_comm x r v).symm)

@[simp] theorem tensorAction_tmul (r : A) (x : ChainAlgebra k l) (v : Compression P a l) :
    tensorAction (k := k) P a l (r ⊗ₜ[k] x) v = r • (x • v) := rfl

instance finiteDimensional [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (Compression P a l) :=
  inferInstanceAs (FiniteDimensional k (∀ i : Fin (l+1), (underlyingComplex (k := k) P).X (a+(i.val:ℤ))))
end Compression
end LittleFinitistic.OrdinarySimulation

end

end OAI
