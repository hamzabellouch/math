import OAI.MeasureTheory.Falconer.Angular.AngularGainFinite

namespace OAI

/-! Dyadic nearest-grid rounding preserves the slope interval used by the
recursive cell construction. The endpoints are actual points of the grid. -/
namespace Falconer

theorem lineGridRound_monotone {δ : ℝ} (hδ : 0 < δ) :
    Monotone (lineGridRound δ) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ hδ.le
  apply Int.cast_le.mpr
  rw [round_eq,round_eq]
  apply Int.floor_mono
  linarith only [div_le_div_of_nonneg_right hab hδ.le]

theorem lineGridRound_grid {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    lineGridRound δ (δ*(k:ℝ)) = δ*(k:ℝ) := by
  simp [lineGridRound,hδ.ne']

theorem lineGridRound_half_interval {δ : ℝ} (hδ : 0 < δ)
    (hk : ∃ k : ℤ, δ*(k:ℝ) = 1/2) {a : ℝ} (ha : |a| ≤ 1/2) :
    |lineGridRound δ a| ≤ 1/2 := by
  obtain ⟨k,hk⟩ := hk
  have hhi : lineGridRound δ (1/2) = 1/2 := by
    rw [← hk]
    exact lineGridRound_grid hδ k
  have hlo : lineGridRound δ (-(1/2)) = -(1/2) := by
    have he : δ*((-k:ℤ):ℝ) = -(1/2) := by simp only [Int.cast_neg,mul_neg,hk]
    rw [← he]
    exact lineGridRound_grid hδ (-k)
  rw [abs_le] at ha ⊢
  exact ⟨hlo ▸ lineGridRound_monotone hδ ha.1,
    hhi ▸ lineGridRound_monotone hδ ha.2⟩

theorem lineGridRound_dyadic_half (n : ℕ) {a : ℝ} (ha : |a| ≤ 1/2) :
    |lineGridRound (1/(2:ℝ)^(n+1)) a| ≤ 1/2 := by
  apply lineGridRound_half_interval (by positivity) _ ha
  refine ⟨(2:ℤ)^n,?_⟩
  push_cast
  rw [pow_succ]
  field_simp

theorem dyadic_local_mesh (a b : ℕ) (hab : a ≤ b) :
    (1/(2:ℝ)^b)/(4*(1/(2:ℝ)^a)) = 1/(2:ℝ)^(b-a+2) := by
  have hp : (2:ℝ)^b = (2:ℝ)^a*(2:ℝ)^(b-a) := by
    rw [← pow_add,Nat.add_sub_of_le hab]
  rw [hp,pow_add]
  norm_num
  field_simp

theorem dyadic_relative_mesh (a b : ℕ) (hab : a ≤ b) :
    (1/(2:ℝ)^b)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(b-a) := by
  have hp : (2:ℝ)^b = (2:ℝ)^a*(2:ℝ)^(b-a) := by
    rw [← pow_add,Nat.add_sub_of_le hab]
  rw [hp]
  field_simp

theorem lineGridRound_local_dyadic_half (a b : ℕ) (hab : a ≤ b)
    {x : ℝ} (hx : |x| ≤ 1/2) :
    |lineGridRound ((1/(2:ℝ)^b)/(4*(1/(2:ℝ)^a))) x| ≤ 1/2 := by
  rw [dyadic_local_mesh a b hab]
  exact lineGridRound_dyadic_half (b-a+1) hx

end Falconer

end OAI
