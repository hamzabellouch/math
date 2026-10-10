import OAI.MeasureTheory.Falconer.Estimates.ScalarSumsetLogBound

namespace OAI

/-! The scalar projection gain in the weak Frostman regime required by
 the planar application. Only the coefficient Frostman constant is fixed. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_weak_block_projection {κ K : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hK : 0 < K) :
    ∃ B copies : ℕ, ∃ η : ℝ, 0 < B ∧ 0 < copies ∧ 0 < η ∧
      ∀ M : ℕ, 0 < M → ∀ K0 Kadd : ℝ, 0 < K0 → 0 < Kadd →
      Real.log K0 ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160 →
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*Kadd) ≤
        (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ∀ L : Finset (CellPath 1), L ⊆ cubePaths 1 (B*M) → L.Nonempty →
      Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells ((1/2:ℝ)^(B*M))
        (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
        Kadd*(scalarCells ((1/2:ℝ)^(B*M)) (L.image scalarPathCenter)).card →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass (L.image scalarPathCenter) u t ≤
          K0*t^κ*((L.image scalarPathCenter).card:ℝ)) →
      ∀ A : Finset ℝ, A.Nonempty → (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) →
      ∃ t ∈ A, Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
        ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
          (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  obtain ⟨P,B,C,hP,hC,hCB,hB,hmargin,hbudget,hloss⟩ := scalar_block_parameters hκ K
  refine ⟨B,scalarBinaryCopies B C,κ*(P:ℝ)/25,by omega,?_,by positivity,?_⟩
  · unfold scalarBinaryCopies scalarBinaryBranchCount
    positivity
  intro M hM K0 Kadd hK0 hKadd hweak hcost L hL hne hsize hadd hpoint A hA hAb hball
  have hscale := scalar_weak_prefix_budget hκ.le hB hweak
  have hsum := scalar_sumset_log_bound (by positivity) hKadd
    (L.image scalarPathCenter) (hne.image _) hadd (scalarBinaryCopies B C)
  rw [scalar_leaf_center_card L hL] at hsum
  have hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by nlinarith
  simpa only [div_mul_eq_mul_div,mul_assoc] using
    scalar_initial_projection_growth hC hCB hP hM L hL hne hκ hκ1 hK hK0
      hbudget hB hmargin hloss hscale hsmall hpoint A hA hAb hball

end Falconer.Regularization

end OAI
