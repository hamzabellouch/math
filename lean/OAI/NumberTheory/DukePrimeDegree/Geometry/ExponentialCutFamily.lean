import OAI.NumberTheory.DukePrimeDegree.Geometry.ExponentialCutSize

namespace OAI

/-! # Actual distance-cut families with exponential size bounds -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_exponential_distance_cut_family {n : ℕ} (hn : 0 < n)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
    let τ := fun m => Real.log (1+r m)
    ∃ (N : ℕ → ℕ) (z : ∀ m, Fin (N m) → X n) (c : ∀ m, Fin (N m) → ℝ)
      (K C : ℝ), 0 < K ∧ 0 ≤ C ∧ ∀ m,
      ((N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) ∧
      (∀ i, τ m/3 < c m i ∧ c m i < τ m/2 ∧
        μ {x | quotientLogDistance (z m i) x=c m i}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z m i)) (c m i) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (48/τ m*(1/2:ℝ)^k)) ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ A*(m:ℝ)+R₀ →
        ∃ i, quotientLogDistance (z m i) x < c m i) ∧
      ∀ i, ∀ x, quotientLogDistance (z m i) x < c m i →
        ∀ y, quotientLogDistance (z m i) y < c m i →
        ∃ g ∈ matrixBall n (r m), rightAction x g=y := by
  classical
  let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
  let τ := fun m => Real.log (1+r m)
  have hr (m : ℕ) : 0 < r m := mul_pos ha (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    have he : Real.exp (-B*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) m)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans (by simpa using ha1)
  have hτ (m : ℕ) : 0 < τ m := Real.log_pos (by linarith [hr m])
  have hex (m : ℕ) := exists_controlled_distance_cuts hn μ
    (A*(m:ℝ)+R₀) (r m) (hr m) (hr1 m)
  choose N z c hN hcut hcover hsmall using hex
  obtain ⟨K,hK,C,hC,hsize⟩ := distanceCut_size_exponential hn hA hB hR₀ ha ha1
  refine ⟨N,z,c,K,C,hK,hC,?_⟩
  intro m
  refine ⟨?_,hcut m,hcover m,hsmall m⟩
  have hreal : (N m:ℝ)*(48/τ m) ≤ K*Real.exp (C*(m:ℝ)) :=
    (mul_le_mul_of_nonneg_right (hN m)
      (div_nonneg (by norm_num) (hτ m).le)).trans (hsize m)
  have H := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] at H

end DukePrimeDegree

end

end OAI
