import OAI.MeasureTheory.Falconer.Radial.WeakRadialLocalBudget

namespace OAI

/-! # Compatible fixed losses for the local weak radial argument -/

namespace Falconer

theorem weak_radial_local_exponents {n : ℕ} (hn : 1 ≤ n) {e ζ : ℝ}
    (he : 0 < e) (hζ : 0 < ζ) :
    ∃ η τ u ε : ℝ, 0 < η ∧ 0 < τ ∧ 0 < u ∧ 0 < ε ∧
      0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u ∧ 0 < η*ζ-ε-u := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0:ℝ) < (n:ℝ)+1 := by positivity
  let η : ℝ := e/(8*(n:ℝ)*((n:ℝ)+1))
  let τ : ℝ := ((n:ℝ)+1)*e/(8*(n:ℝ))
  let u : ℝ := min τ (η*ζ/8)
  let ε : ℝ := η*ζ/8
  have hη : 0 < η := by dsimp [η]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hu : 0 < u := lt_min hτ hε
  refine ⟨η,τ,u,ε,hη,hτ,hu,hε,?_,?_⟩
  · have ht : (n:ℝ)*τ = ((n:ℝ)+1)*e/8 := by
      dsimp [τ]
      field_simp
    have ha : η*(n:ℝ)*((n:ℝ)+1)^2 = ((n:ℝ)+1)*e/8 := by
      dsimp [η]
      field_simp
    have huτ : (n:ℝ)*u ≤ (n:ℝ)*τ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hN.le
    rw [ht] at huτ
    rw [ht,ha]
    nlinarith [mul_pos hD he]
  · have huε : u ≤ ε := min_le_right _ _
    dsimp [ε] at huε ⊢
    nlinarith [mul_pos hη hζ]

theorem weak_radial_bounded_exponents {n : ℕ} (hn : 1 ≤ n) {e ζ : ℝ}
    (he : 0 < e) (hζ : 0 < ζ) :
    ∃ η τ u ε : ℝ, 0 < η ∧ η ≤ 1/2 ∧ 0 < τ ∧ 0 < u ∧ 0 < ε ∧
      0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u ∧ 0 < η*ζ-ε-u := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0:ℝ) < (n:ℝ)+1 := by positivity
  let η₀ : ℝ := e/(8*(n:ℝ)*((n:ℝ)+1))
  let η : ℝ := min η₀ (1/2)
  let τ : ℝ := ((n:ℝ)+1)*e/(8*(n:ℝ))
  let u : ℝ := min τ (η*ζ/8)
  let ε : ℝ := η*ζ/8
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hu : 0 < u := lt_min hτ hε
  refine ⟨η,τ,u,ε,hη,min_le_right _ _,hτ,hu,hε,?_,?_⟩
  · have ht : (n:ℝ)*τ = ((n:ℝ)+1)*e/8 := by dsimp [τ]; field_simp
    have ha : η₀*(n:ℝ)*((n:ℝ)+1)^2 = ((n:ℝ)+1)*e/8 := by
      dsimp [η₀]
      field_simp
    have hηle : η*(n:ℝ)*((n:ℝ)+1)^2 ≤ η₀*(n:ℝ)*((n:ℝ)+1)^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hN.le) (sq_nonneg _)
    have hule : (n:ℝ)*u ≤ (n:ℝ)*τ := mul_le_mul_of_nonneg_left (min_le_left _ _) hN.le
    rw [ht] at hule
    rw [ha] at hηle
    rw [ht]
    nlinarith [mul_pos hD he]
  · have hule : u ≤ ε := min_le_right _ _
    dsimp [ε] at hule ⊢
    nlinarith [mul_pos hη hζ]

end Falconer

end OAI
