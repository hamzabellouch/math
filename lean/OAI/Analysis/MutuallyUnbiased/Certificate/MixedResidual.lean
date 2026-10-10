import OAI.Analysis.MutuallyUnbiased.MixedData.Expression

namespace OAI

namespace MUB6.Certificate.MixedData

def residualTail : Integer.Sparse (Fin 3237) := targetRow23.tail

theorem residualBound0 (x : Fin 3237 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1) :
    Integer.Sparse.eval targetRow23 x ≤ -3431846511326182440960 := by
  have h := Integer.Sparse.eval_le_abs_sum residualTail x hx
  have ha : (residualTail.map (fun p => |(p.2 : ℝ)|)).sum = 129038594601492817920 := by
    norm_num [residualTail, targetRow23]
  rw [ha] at h
  have heq : targetRow23 = (0, (-3560885105927675258880 : ℤ)) :: residualTail := rfl
  rw [heq, Integer.Sparse.eval_cons, hzero]
  norm_num only [Int.cast_neg, Int.cast_ofNat, mul_one]
  linarith

theorem residualBound1 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow24 x ≤ 57809244737470464000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow24 x hx
  have ha : (targetRow24.map (fun p => |(p.2 : ℝ)|)).sum = 57809244737470464000 := by
    norm_num [targetRow24]
  rw [ha] at h
  exact h

theorem residualBound2 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow25 x ≤ 208460565551960064000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow25 x hx
  have ha : (targetRow25.map (fun p => |(p.2 : ℝ)|)).sum = 208460565551960064000 := by
    norm_num [targetRow25]
  rw [ha] at h
  exact h

theorem residualBound3 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow26 x ≤ 342451535685706137600 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow26 x hx
  have ha : (targetRow26.map (fun p => |(p.2 : ℝ)|)).sum = 342451535685706137600 := by
    norm_num [targetRow26]
  rw [ha] at h
  exact h

theorem residualBound4 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow27 x ≤ 57870913835040768000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow27 x hx
  have ha : (targetRow27.map (fun p => |(p.2 : ℝ)|)).sum = 57870913835040768000 := by
    norm_num [targetRow27]
  rw [ha] at h
  exact h

theorem residualBound5 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow28 x ≤ 247845907767951360000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow28 x hx
  have ha : (targetRow28.map (fun p => |(p.2 : ℝ)|)).sum = 247845907767951360000 := by
    norm_num [targetRow28]
  rw [ha] at h
  exact h

theorem residualNegative (x : Fin 3237 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1) :
    Integer.Combination.eval targetRows x residualCombination < 0 := by
  have h0 := residualBound0 x hx hzero
  have h1 := residualBound1 x hx
  have h2 := residualBound2 x hx
  have h3 := residualBound3 x hx
  have h4 := residualBound4 x hx
  have h5 := residualBound5 x hx
  change (Integer.Sparse.eval targetRow23 x +
    (Integer.Sparse.eval targetRow24 x + Integer.Sparse.eval targetRow25 x)) +
    (Integer.Sparse.eval targetRow26 x +
    (Integer.Sparse.eval targetRow27 x + Integer.Sparse.eval targetRow28 x)) < 0
  linarith

end MUB6.Certificate.MixedData

end OAI
