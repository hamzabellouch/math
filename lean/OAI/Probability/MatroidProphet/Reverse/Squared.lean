import OAI.Probability.MatroidProphet.Reverse.LowHazard

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def exitHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then reverseHazard M hE κ D G q d h k S else 0

noncomputable def squareHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0

lemma exitHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) m k S =
      reverseMeanCost M hE κ D G n q (exitCost d h) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hd : d ∈ R h
    · simp only [exitHazardCost, hd, ite_true, bitsExpectation_const, exitCost, true_and]
      exact reverseHazard_eq_step M hE κ D G n hG q d h hh l R
    · simp only [exitHazardCost, hd, ite_false, bitsExpectation_const, exitCost, false_and]
  · exact closed

theorem reverse_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h)
        (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
  let η : ℝ := ((2:ℝ)^12)⁻¹
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hpoint (k : ℤ) (S S' : ℕ → Set α) :
      η * exitHazardCost M hE κ D G q d h k S S' ≤
        squareHazardCost M hE κ D G q d h k S S' + η * lowHazardCost M hE κ D G q d h η k S S' := by
    by_cases hs : d ∈ S h
    · by_cases hp : reverseHazard M hE κ D G q d h k S < η
      · simp only [exitHazardCost, squareHazardCost, lowHazardCost, hs, hp, true_and, ite_true]
        nlinarith [sq_nonneg (reverseHazard M hE κ D G q d h k S)]
      · have hp' : η ≤ reverseHazard M hE κ D G q d h k S := le_of_not_gt hp
        have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h k S
        simp only [exitHazardCost, squareHazardCost, lowHazardCost, hs, hp, true_and, ite_true, ite_false, mul_zero, add_zero]
        nlinarith
    · simp [exitHazardCost, squareHazardCost, lowHazardCost, hs]
  have hmean :
      η * reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) +
      η * reverseMeanCost M hE κ D G n q (lowHazardCost M hE κ D G q d h η) (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
    rw [← reverseMeanCost_mul, ← reverseMeanCost_mul, ← reverseMeanCost_add]
    unfold reverseMeanCost
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact reverseCost_mono M hE κ D G n _ _ hpoint _ _ _ C
  rw [exitHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ _
    (reverseClosed_univ M hE κ D (-1)), reverse_exit_total_one M hE κ D G n hG q d hd h hh,
    mul_one] at hmean
  have hlow := reverse_low_hazard_lt_half M hE κ D G n hG q hq0 hq1 d h hh
    (pathHorizon h+1) (-1) (fun _ => Set.univ) (reverseClosed_univ M hE κ D (-1))
  change η / 2 ≤ reverseMeanCost M hE κ D G n q _ _ _ _
  change reverseMeanCost M hE κ D G n q (lowHazardCost M hE κ D G q d h η) _ _ _ < _ at hlow
  have hmul := mul_le_mul_of_nonneg_left hlow.le hη
  have hsub := (sub_le_iff_le_add).mpr (hmean.trans (add_le_add le_rfl hmul))
  calc
    η / 2 = η - η * (1 / 2) := by ring
    _ ≤ _ := hsub

end MatroidProphet

end OAI
