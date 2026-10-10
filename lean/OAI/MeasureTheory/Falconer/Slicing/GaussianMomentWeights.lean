import OAI.MeasureTheory.Falconer.Slicing.GaussianPointCloseBound
import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseBound
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMass

namespace OAI

/-! # The dyadic weights of the actual point and direction pair moments -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianFrostmanFactor (h : ℕ) (s : ℝ) : ℝ :=
  1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-s))

theorem gaussian_point_moment_weight
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {Kt t C : ℝ} (hKt : 0 ≤ Kt) (ht : (h:ℝ) < t) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kt*(1/(2:ℝ)^j)^t))
    (hC : (4*gaussianVectorBandConstant)^h*Kt*gaussianFrostmanFactor h t ≤ C) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)).prod
        (gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)))
        {z | dist z.1 z.2 < 2*((1/(2:ℝ)^g)/2)} ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal (C*((2:ℝ)^g)^((h:ℝ)-t)) := by
  have hVC := gaussianVectorBandConstant_pos
  have hr : (2:ℝ)*((1/(2:ℝ)^g)/2) = 1/(2:ℝ)^g := by ring
  rw [hr]
  apply (gaussian_point_slice_close_frostman μ hKt ht g N hg hmass hball).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4*gaussianVectorBandConstant)^h)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((4*gaussianVectorBandConstant)^h*Kt*gaussianFrostmanFactor h t)*
      ((2:ℝ)^g)^((h:ℝ)-t) := by unfold gaussianFrostmanFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)

theorem gaussian_direction_moment_weight
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {Kq q C : ℝ} (hKq : 0 ≤ Kq) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Sphere d, ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d))
    (hC : (2*gaussianPairBandConstant)^h*Kq*gaussianFrostmanFactor h q ≤ C) :
    (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).prod
        (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)))
        {z | dist z.1 z.2 < 2*((1/(2:ℝ)^g)/2)} ∂gaussianRows d h) ≤
      ENNReal.ofReal (C*((2:ℝ)^g)^((h:ℝ)-q)) := by
  have hPC := gaussianPairBandConstant_pos
  have hr : (2:ℝ)*((1/(2:ℝ)^g)/2) = 1/(2:ℝ)^g := by ring
  rw [hr]
  apply (gaussian_direction_slice_close_frostman ν hKq hq g N hg hmass hball hchart).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*gaussianPairBandConstant)^h)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((2*gaussianPairBandConstant)^h*Kq*gaussianFrostmanFactor h q)*
      ((2:ℝ)^g)^((h:ℝ)-q) := by unfold gaussianFrostmanFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)

theorem gaussian_direction_total_moment_bound
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {Kq q C : ℝ} (hKq : 0 ≤ Kq) (hq : (h:ℝ) < q) (N : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Sphere d, ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d))
    (hC : (2*gaussianPairBandConstant)^h*(|Kq*gaussianFrostmanFactor h q|+1) ≤ C) :
    (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν (1/(2:ℝ)^N) A)^2
      ∂gaussianRows d h) ≤ ENNReal.ofReal C := by
  have hPC := gaussianPairBandConstant_pos
  apply (gaussian_direction_mass_second_moment ν hKq hq N hmass hball hchart).trans
  have hb : ENNReal.ofReal (Kq*gaussianFrostmanFactor h q)+1 ≤
      ENNReal.ofReal (|Kq*gaussianFrostmanFactor h q|+1) := by
    rw [ENNReal.ofReal_add (abs_nonneg _) zero_le_one,ENNReal.ofReal_one]
    exact add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl
  apply (mul_le_mul' le_rfl hb).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*gaussianPairBandConstant)^h)]
  exact ENNReal.ofReal_le_ofReal hC

end Falconer

end OAI
