import OAI.NumberTheory.DukePrimeDegree.Geometry.DistanceCutBounds

namespace OAI

/-! # Exponential size control for cuts on increasing quotient balls -/

noncomputable section
namespace DukePrimeDegree

theorem distanceCut_size_exponential {n : ℕ} (hn : 0 < n)
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K > 0, ∃ C ≥ 0, ∀ m : ℕ,
      quotientNetBound n (A*(m:ℝ)+R₀) (Real.log (1+a*Real.exp (-B*(m:ℝ)))/4) *
        (48/Real.log (1+a*Real.exp (-B*(m:ℝ)))) ≤ K*Real.exp (C*(m:ℝ)) := by
  let Q := 1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(R₀+1))/a
  let K := Q^(n*n)*(96/a)
  let C := ((n*n:ℕ):ℝ)*(2*A+B)+B
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hK : 0 < K := mul_pos (pow_pos hQ _) (div_pos (by norm_num) ha)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K,hK,C,hC,?_⟩
  intro m
  let r := a*Real.exp (-B*(m:ℝ))
  have hr : 0 < r := mul_pos ha (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    have he : Real.exp (-B*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) m)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans (by simpa using ha1)
  have hsize := distanceCut_size_bound hn
    (show 0 ≤ A*(m:ℝ)+R₀ by positivity) hr hr1
  apply hsize.trans
  have he₁ : Real.exp (2*(A*(m:ℝ)+R₀+1)) =
      Real.exp (2*(R₀+1))*Real.exp (2*A*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have he₂ : Real.exp ((2*A+B)*(m:ℝ)) =
      Real.exp (2*A*(m:ℝ))*Real.exp (B*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have he₃ : Real.exp (-B*(m:ℝ)) = (Real.exp (B*(m:ℝ)))⁻¹ := by
    rw [←Real.exp_neg]
    congr 1
    ring
  have hratio : 1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(A*(m:ℝ)+R₀+1))/r =
      Q*Real.exp ((2*A+B)*(m:ℝ)) := by
    dsimp [r,Q]
    rw [he₁,he₂,he₃]
    field_simp
  have hratio' : 96/r = (96/a)*Real.exp (B*(m:ℝ)) := by
    dsimp [r]
    rw [he₃]
    field_simp
  rw [hratio,hratio',mul_pow,←Real.exp_nat_mul]
  have he₄ : Real.exp (((n*n:ℕ):ℝ)*((2*A+B)*(m:ℝ)))*Real.exp (B*(m:ℝ)) =
      Real.exp (C*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [C]
    ring
  calc
    _ = K*(Real.exp (((n*n:ℕ):ℝ)*((2*A+B)*(m:ℝ)))*Real.exp (B*(m:ℝ))) := by
      dsimp [K]
      ring
    _ ≤ _ := by rw [he₄]

end DukePrimeDegree

end

end OAI
