import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicChain
import OAI.Algebra.AuslanderReiten.Cones.TwoConeRestriction

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)
variable (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.d (n+1) n = Q.d (n+4) (n+3) ≫ r n)

abbrev twoConeData : TwoCone.Data (A ⊗[k] B) where
  term := (complex k A B P Q).X
  d n := ((complex k A B P Q).d (n+1) n).hom
  first := firstCubic k A B P Q p
  second := secondCubic k A B P Q r
  square n := congrArg ModuleCat.Hom.hom ((complex k A B P Q).d_comp_d (n+2) (n+1) n)
  first_comm := firstCubic_chain k A B P Q p hp
  second_comm := secondCubic_chain k A B P Q r hr
  comparisons_comm := cubic_commute k A B P Q p r

end ArExplicit.ExternalTensor

end

end OAI
