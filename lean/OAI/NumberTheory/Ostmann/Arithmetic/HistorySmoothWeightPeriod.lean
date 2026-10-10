import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightAtoms
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightDepth

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState.StateExpr
open Construction Characters.RationalHistory HistorySymbolicStep HistorySymbolicCost HistorySymbolicEncoding
variable {ι : Type*} {a : State}

def periodExpr (e : StateExpr a ι) (outside : List ℕ) : Expr ι :=
  .mul (.fixed (outsideProduct outside)) (.mul e.plus (.mul e.minus (product (List.ofFn e.small))))

@[simp] theorem periodExpr_realEval (e : StateExpr a ι) (outside : List ℕ) (x : ι → ℝ) :
    (e.periodExpr outside).realEval x = e.realPeriod outside x := rfl

theorem periodExpr_logSize (e : StateExpr a ι) (outside : List ℕ) :
    (e.periodExpr outside).logSize = stateCost e := by
  rw [logSize_eq_atomCount]
  simp only [periodExpr,Expr.atomCount,product_atomCount,List.map_ofFn,
    List.sum_ofFn,Function.comp_def,stateCost,slotCost]
  omega

theorem periodExpr_depth (e : StateExpr a ι) (outside : List ℕ) (d : ℕ)
    (he : StateDepth d e) : (e.periodExpr outside).cancellationDepth ≤ d := by
  have hp : (product (List.ofFn e.small)).cancellationDepth ≤ 0 := by
    apply product_cancellationDepth_le
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact (he.2.2 i).le
  have hplus := he.1
  have hminus := he.2.1
  simp only [periodExpr,Expr.cancellationDepth]
  omega

theorem periodExpr_relativeControl (e : StateExpr a ι) (outside : List ℕ) (x : ι → ℝ) (K : ℝ)
    (he : e.plus.RelativeControl x K ∧ e.minus.RelativeControl x K)
    (hsmall : StateSmallAtoms e) (hx : ∀ i, 0 < x i) (houtside : ∀ q ∈ outside, 0 < q) :
    (e.periodExpr outside).RelativeControl x K := by
  have hd : (outsideProduct outside:ℝ) ≠ 0 := by exact_mod_cast (List.prod_pos houtside).ne'
  refine ⟨hd,he.1,he.2,product_relativeControl _ x K ?_⟩
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  obtain ⟨j,hj⟩ := hsmall i
  rw [hj]
  exact (hx j).ne'

theorem periodExpr_budget_le (e : StateExpr a ι) (outside : List ℕ) (B d : ℕ) {K : ℝ}
    (hK : 1 ≤ K) (hcost : stateCost e ≤ B) (hdepth : StateDepth d e) :
    (e.periodExpr outside).logBudget K ≤ (B:ℝ) * K^d := by
  unfold Expr.logBudget
  rw [periodExpr_logSize]
  exact mul_le_mul (by exact_mod_cast hcost)
    (pow_le_pow_right₀ hK (e.periodExpr_depth outside d hdepth))
    (pow_nonneg (zero_le_one.trans hK) _) (Nat.cast_nonneg B)

end Ostmann.Arithmetic.HistorySymbolicState.StateExpr

end

end OAI
