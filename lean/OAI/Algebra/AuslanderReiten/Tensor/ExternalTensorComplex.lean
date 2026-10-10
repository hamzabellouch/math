import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorFunctor
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Data.Finset.NatAntidiagonal

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

instance hasTotal : HomologicalComplex.HasMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) :=
  fun _ => inferInstance

abbrev complex : ChainComplex (ModuleCat.{u} (A ⊗[k] B)) ℕ :=
  HomologicalComplex.mapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ)

abbrev Diagonal (n : ℕ) := {p : ℕ × ℕ // p.1 + p.2 = n}

instance (n : ℕ) : Fintype (Diagonal n) :=
  Fintype.ofFinset (Finset.antidiagonal n) (by intro p; exact Finset.mem_antidiagonal)

abbrev summands (n : ℕ) (p : Diagonal n) : ModuleCat.{u} (A ⊗[k] B) :=
  moduleObject k A B (P.X p.val.1) (Q.X p.val.2)

def termDirectSumEquiv (n : ℕ) :
    (complex k A B P Q).X n ≃ₗ[A ⊗[k] B] (Π₀ p : Diagonal n, summands k A B P Q n p) :=
  CategoryTheory.Iso.toLinearEquiv (ModuleCat.coprodIsoDirectSum (summands k A B P Q n))

def termPiEquiv (n : ℕ) :
    (complex k A B P Q).X n ≃ₗ[A ⊗[k] B] (∀ p : Diagonal n, summands k A B P Q n p) :=
  (termDirectSumEquiv k A B P Q n).trans DFinsupp.linearEquivFunOnFintype

variable [Module.Finite k A] [Module.Finite k B]
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]

theorem term_finite (n : ℕ) : Module.Finite (A ⊗[k] B) ((complex k A B P Q).X n) := by
  let (index : ℕ) : Module.Finite k (P.X index) := Module.Finite.trans A (P.X index)
  let (index : ℕ) : Module.Finite k (Q.X index) := Module.Finite.trans B (Q.X index)
  let (index : Diagonal n) : Module.Finite (A ⊗[k] B) (summands k A B P Q n index) :=
    Module.Finite.of_restrictScalars_finite k (A ⊗[k] B) _
  exact Module.Finite.equiv (termPiEquiv k A B P Q n).symm

variable [∀ n, Module.Projective A (P.X n)] [∀ n, Module.Projective B (Q.X n)]

omit [Module.Finite k A] [Module.Finite k B] in
theorem term_projective (n : ℕ) : Module.Projective (A ⊗[k] B) ((complex k A B P Q).X n) := by
  let (index : Diagonal n) : Module.Projective (A ⊗[k] B) (summands k A B P Q n index) :=
    projective k A B
  exact Module.Projective.of_equiv (termDirectSumEquiv k A B P Q n).symm

end ArExplicit.ExternalTensor

end

end OAI
