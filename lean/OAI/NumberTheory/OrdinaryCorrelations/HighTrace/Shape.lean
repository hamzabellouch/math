import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GrowsSingleton
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SizedSet

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

structure Shape (w : ClosedLine h ℓ) where
  top : ↥(treeVertices w)
  edges : ↥((shapes w top.val).erase ∅)

def shapeEquiv (w : ClosedLine h ℓ) :
    Shape w ≃ ((v : ↥(treeVertices w)) × ↥((shapes w v.val).erase ∅)) where
  toFun Q := ⟨Q.top,Q.edges⟩
  invFun Q := ⟨Q.1,Q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (w : ClosedLine h ℓ) : Fintype (Shape w) := Fintype.ofEquiv _ (shapeEquiv w).symm
instance (w : ClosedLine h ℓ) : DecidableEq (Shape w) := Classical.decEq _

lemma sum_shapes (w : ClosedLine h ℓ) (f : Finset (Fin ℓ) → ℝ) :
    (∑ Q : Shape w, f Q.edges.val) =
      ∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅, f E := by
  calc
    _ = ∑ Q : ((v : ↥(treeVertices w)) × ↥((shapes w v.val).erase ∅)), f Q.2.val :=
      (shapeEquiv w).sum_comp (fun Q => f Q.2.val)
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [sum_coe_sort]
      exact sum_coe_sort (treeVertices w) (fun v => ∑ E ∈ (shapes w v).erase ∅, f E)

lemma core_shape_sum {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (p : S.Index) (hp : S.IsCore p) :
    (∑ Q : Shape w, modifiedWeight w p Q.edges.val) ≤ bandDefect w betaC := by
  have hA : 0 ≤ A := (le_of_lt (Real.exp_pos _))
  have hb : 0 ≤ betaC := by unfold betaC; positivity
  have hunit : betaC*(1+A)=1 := inv_mul_cancel₀ (by unfold A; positivity)
  have hr := numerical_subtree_sum_le w A betaC hA hb hunit
  rw [sum_shapes]
  simpa only [modifiedWeight,hp,ite_true,subtreeUnionWeight,amplitude,beta_eq_core p hp] using hr

lemma center_shape_sum {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index) (hp : ¬S.IsCore p) :
    (∑ Q : Shape w, modifiedWeight w p Q.edges.val) ≤ bandDefect w betaZ +
      (-theta/2*(goodEdges w).card + theta*(badEdges w).card) := by
  rw [sum_shapes]
  linarith only [modified_center_subtree_sum w hh p hp]

@[reducible] def TokenType (w : ClosedLine h ℓ) := Bool × Shape w

def tokenWeight {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (pC pZ : S.Index) (t : TokenType w) : ℝ :=
  modifiedWeight w (if t.1 then pC else pZ) t.2.edges.val

def tokenMass (w : ClosedLine h ℓ) (vC vZ : ℝ) (t : TokenType w) : ℝ :=
  if t.1 then vC else vZ

lemma tokenWeight_nonneg {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (pC pZ : S.Index) (t : TokenType w) :
    0 ≤ tokenWeight w pC pZ t := modifiedWeight_nonneg w _ _

lemma total_token_exponent {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (hh : 0 < h) (pC pZ : S.Index)
    (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) (vC vZ : ℝ) (hvC : 0 ≤ vC) (hvZ : 0 ≤ vZ) :
    (∑ t : TokenType w, tokenMass w vC vZ t * tokenWeight w pC pZ t) ≤
      vC*bandDefect w betaC + vZ*bandDefect w betaZ +
        vZ*(-theta/2*(goodEdges w).card + theta*(badEdges w).card) := by
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [tokenMass,tokenWeight,ite_true,ite_false,Bool.false_eq_true]
  rw [← mul_sum,← mul_sum]
  have hc := mul_le_mul_of_nonneg_left (core_shape_sum w pC hpC) hvC
  have hz := mul_le_mul_of_nonneg_left (center_shape_sum w hh pZ hpZ) hvZ
  nlinarith only [hc,hz]

theorem untagged_exponential_bound {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (hh : 0 < h) (pC pZ : S.Index)
    (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) (vC vZ : ℝ) (hvC : 0 ≤ vC) (hvZ : 0 ≤ vZ)
    (N : TokenType w → ℕ) :
    Real.exp (-vC*bandDefect w betaC-vZ*bandDefect w betaZ) *
      (∑ j : ∀ t : TokenType w, Fin (N t),
        ∏ t : TokenType w,
          (tokenMass w vC vZ t * tokenWeight w pC pZ t)^(j t).val / (j t).val.factorial) ≤
      Real.exp (-theta/2*vZ*(goodEdges w).card + theta*vZ*(badEdges w).card) := by
  let x := fun t : TokenType w => tokenMass w vC vZ t * tokenWeight w pC pZ t
  have hx : ∀ t, 0 ≤ x t := by
    intro t
    apply mul_nonneg
    · dsimp only [tokenMass]
      split_ifs <;> assumption
    · exact tokenWeight_nonneg w pC pZ t
  have hm := OrdinaryCorrelations.FactorialAssignments.multiplicity_sum_bound x hx N
  have he := total_token_exponent w hh pC pZ hpC hpZ vC vZ hvC hvZ
  calc
    _ ≤ Real.exp (-vC*bandDefect w betaC-vZ*bandDefect w betaZ) * Real.exp (∑ t, x t) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (-vC*bandDefect w betaC-vZ*bandDefect w betaZ+∑ t, x t) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      dsimp only [x]
      nlinarith only [he]

lemma tokenWeight_representative {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (p q : S.Index) (hpq : S.IsCore p ↔ S.IsCore q)
    (E : Finset (Fin ℓ)) : modifiedWeight w p E = modifiedWeight w q E := by
  have ha : S.amplitude p = S.amplitude q := by simp only [amplitude,hpq]
  have hb : S.beta p = S.beta q := by simp only [beta,ha]
  simp only [modifiedWeight,subtreeUnionWeight,ha,hb,hpq]

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
