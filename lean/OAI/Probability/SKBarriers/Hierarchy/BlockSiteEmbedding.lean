import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.AverageMeanVariance
import OAI.Probability.SKBarriers.Hierarchy.WeightedBlockMass

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def blockSiteEmbedding (D N r k : ℕ) (i : Fin N) (j : Fin ((k+1)*r)) :
    Fin (blockDimension D (N*r) k) :=
  fieldIndex D (N*r) k (finProdFinEquiv.symm j).1
    (finProdFinEquiv (i,(finProdFinEquiv.symm j).2))

theorem blockSiteEmbedding_apply (D N r k : ℕ) (i : Fin N) (b : Fin (k+1)) (u : Fin r) :
    blockSiteEmbedding D N r k i (finProdFinEquiv (b,u))=
      fieldIndex D (N*r) k b (finProdFinEquiv (i,u)) := by
  simp only [blockSiteEmbedding,Equiv.symm_apply_apply]

theorem blockSiteEmbedding_strictMono (D N r k : ℕ) (i : Fin N) :
    StrictMono (blockSiteEmbedding D N r k i) := by
  intro a b hab
  obtain ⟨⟨ba,ua⟩,rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨bb,ub⟩,rfl⟩ := finProdFinEquiv.surjective b
  rw [blockSiteEmbedding_apply,blockSiteEmbedding_apply]
  change D+ba.val*(N*r)+(ua.val+r*i.val)<D+bb.val*(N*r)+(ub.val+r*i.val)
  change ua.val+r*ba.val<ub.val+r*bb.val at hab
  have hN : 0<N := Nat.zero_lt_of_lt i.isLt
  have hba : ba.val ≤ bb.val := by
    by_contra h
    have hmul := Nat.mul_le_mul_left r (show bb.val+1 ≤ ba.val by omega)
    nlinarith [ub.isLt]
  by_cases he : ba.val=bb.val
  · rw [he] at hab ⊢
    omega
  · have hmul := Nat.mul_le_mul_right (N*r) (show ba.val+1 ≤ bb.val by omega)
    have hrN : r ≤ N*r := Nat.le_mul_of_pos_left r hN
    nlinarith [ua.isLt]

def blockSiteOwner {D N r k : ℕ} (i₀ : Fin N) : Fin (blockDimension D (N*r) k) → Fin N :=
  Fin.addCases (fun _ => i₀) (fun t => (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1)

theorem blockSiteOwner_embedding {D N r k : ℕ} (i₀ i : Fin N) (j : Fin ((k+1)*r)) :
    blockSiteOwner (D:=D) (r:=r) (k:=k) i₀ (blockSiteEmbedding D N r k i j)=i := by
  unfold blockSiteEmbedding
  rw [fieldIndex_eq_natAdd]
  simp only [blockSiteOwner,Fin.addCases_right,Equiv.symm_apply_apply]

def siteBlockMass (r k : ℕ) (w : Fin (k+1) → ℝ) (j : Fin ((k+1)*r)) : ℝ :=
  ∑ l, if l<(finProdFinEquiv.symm j).1 then w l else 0

theorem blockSiteEmbedding_mass (D N r k : ℕ) (w : Fin (k+1) → ℝ)
    (i : Fin N) (j : Fin ((k+1)*r)) :
    weightedBlockMass D (N*r) k w (blockSiteEmbedding D N r k i j)=siteBlockMass r k w j := by
  exact weightedBlockMass_at_field D (N*r) k w _ _

end SK.Analytic

end
end

end OAI
