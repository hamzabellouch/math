import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialValidated
import OAI.Combinatorics.SharpRamsey.Geometry.QuotientHeaderGaps
import OAI.Combinatorics.SharpRamsey.Learning.SizeHeader

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Validated (q P H : ℝ) (r : ℕ)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (n t : ℕ) (τ : ℝ) : Prop :=
  ∃ F : Finset (Finset (Projectivization K V)),
    (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤100000*q^r/t) ∧
    (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
      (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
      ∃ W∈F,(99/100:ℝ)*n≤(S∩W).card) ∧
    log ((F.card:ℝ)+1)≤H*q*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)

lemma quotient_product {q b : ℝ} (hq : 0<q) (r : ℕ) :
    q^(r+3)*exp (-(b+log 4))=q^(r+4)*exp (-b)/(4*q) := by
  have he : exp (-(b+log 4))=exp (-b)/4 := by
    simp only [neg_add,exp_add,exp_neg,exp_log (by norm_num : (0:ℝ)<4),div_eq_mul_inv]
  rw [he,show r+4=(r+3)+1 by omega,pow_succ q (r+3)]
  field_simp

end
end SharpLogRamsey.GeometricCover

end

end OAI
