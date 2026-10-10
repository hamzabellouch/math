import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialGrowth

namespace OAI

/-! A quantitative scalar sum-product alternative with all block parameters
 chosen. The input and output concern the original dyadic leaf set. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_block_sum_product {κ K K0 : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hK : 0 < K) (hK0 : 0 < K0) :
    ∃ B copies M0 : ℕ, ∃ η : ℝ, 0 < B ∧ 0 < copies ∧ 0 < M0 ∧ 0 < η ∧
      ∀ M : ℕ, M0 ≤ M → ∀ L : Finset (CellPath 1),
      L ⊆ cubePaths 1 (B*M) → L.Nonempty →
      Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass (L.image scalarPathCenter) u t ≤
          K0*t^κ*((L.image scalarPathCenter).card:ℝ)) →
      ∀ A : Finset ℝ, A.Nonempty → (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) →
      Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
        ((scalarCells ((1/2:ℝ)^(B*M)) (copies • L.image scalarPathCenter)).card:ℝ) ∨
      ∃ t ∈ A, Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
        ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
          (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  obtain ⟨P,B,C,hP,hC,hCB,hB,hmargin,hbudget,hloss⟩ := scalar_block_parameters hκ K
  have hBpos : 0 < B := by omega
  have hPpos : (0:ℝ) < (P:ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hcoef : 0 < (κ*(B:ℝ)-2*(P:ℝ))*κ*Real.log 2 := by
    exact mul_pos (mul_pos (by linarith) hκ) (Real.log_pos (by norm_num))
  obtain ⟨M0,hM0⟩ := exists_nat_gt (max 1
    (40*Real.log K0/((κ*(B:ℝ)-2*(P:ℝ))*κ*Real.log 2)))
  have hM0pos : 0 < M0 := by
    have hh : (1:ℝ) < M0 := (le_max_left _ _).trans_lt hM0
    exact_mod_cast (show (0:ℝ) < M0 by linarith)
  have hscale0 : 40*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ hcoef).1 ((le_max_right _ _).trans_lt hM0)
    nlinarith
  let η := min (κ*(B:ℝ)/4) (κ*(P:ℝ)/25)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨B,scalarBinaryCopies B C,M0,η,hBpos,?_,hM0pos,hη,?_⟩
  · unfold scalarBinaryCopies scalarBinaryBranchCount
    positivity
  intro M hM L hL hne hsize hpoint A hA hAb hball
  have hMpos : 0 < M := hM0pos.trans_le hM
  have hscale : 40*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hM) hcoef.le
    nlinarith
  by_cases hs : Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
      ((scalarCells ((1/2:ℝ)^(B*M))
        (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ)
  · exact Or.inl hs
  apply Or.inr
  have hLpos : (0:ℝ) < (L.card:ℝ) := by exact_mod_cast hne.card_pos
  have hsumne : (scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).Nonempty := by
    exact ((hne.image scalarPathCenter).nsmul).image _
  have hsumpos : (0:ℝ) < ((scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ) := by
    exact_mod_cast hsumne.card_pos
  have hlog := Real.log_le_log hsumpos (le_of_not_gt hs)
  rw [Real.log_mul (Real.exp_pos _).ne' hLpos.ne',Real.log_exp] at hlog
  have hηB := mul_le_mul_of_nonneg_right (min_le_left (κ*(B:ℝ)/4) (κ*(P:ℝ)/25))
    (show 0 ≤ (M:ℝ)*Real.log 2 by positivity)
  have hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by nlinarith
  obtain ⟨t,ht,hgain⟩ := scalar_initial_projection_growth hC hCB hP hMpos L hL hne
    hκ hκ1 hK hK0 hbudget hB hmargin hloss hscale hsmall hpoint A hA hAb hball
  refine ⟨t,ht,lt_of_le_of_lt ?_ hgain⟩
  apply mul_le_mul_of_nonneg_right _ hLpos.le
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (min_le_right (κ*(B:ℝ)/4) (κ*(P:ℝ)/25))
    (show 0 ≤ (M:ℝ)*Real.log 2 by positivity)
  nlinarith

end Falconer.Regularization

end OAI
