import OAI.Analysis.LipschitzHilbert.Estimates.RealFiniteVariation
import OAI.Analysis.LipschitzHilbert.Estimates.LepingleIntervals

namespace OAI

/-! The exact finite, scalar, unweighted p=2, r=3 specialization of
Zorin-Kranich, Bernoulli 26 (2020), Theorem 1.1. The proof uses the
relative stopping-time construction of Section 2 and quadratic energy;
no weighted inequality or further published premise is needed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

omit m in
theorem variationCube_relative_energy (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    variationCube F N x^(2/3:ℝ)≤
      ENNReal.ofReal (2048*weightedRelativeExitEnergy F (N+1) x) := by
  rw [←scalar_finiteCubicVariation]
  rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (realVariationCube_two_thirds_bound F N x)

omit m in
theorem variationCube_freeze (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    variationCube (fun n => F (min n N)) N x=variationCube F N x := by
  classical
  unfold variationCube
  congr 1
  funext p
  split_ifs
  · apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [min_eq_left (Nat.le_of_lt_succ (p i.succ).isLt),
      min_eq_left (Nat.le_of_lt_succ (p i.castSucc).isLt)]
  · rfl

theorem martingale_variation_L2 (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (N : ℕ) :
    (∫⁻ x, variationCube F N x^(2/3:ℝ) ∂μ)≤(1024:ℝ≥0∞)*squareIntegral μ (F N) := by
  let G := fun n => F (min n N)
  have hG : Martingale G ℱ μ := martingale_freeze hF N
  have hG2 : ∀ n, MemLp (G n) 2 μ := fun n => hF2 (min n N)
  have hW := weightedRelativeExitEnergy_integrable hG hG2 (N+1)
  have hWn := weightedRelativeExitEnergy_nonneg G (N+1)
  have hWi := weightedRelativeExitEnergy_integral_le hG hG2 (N+1)
  have heW := ofReal_integral_eq_lintegral_ofReal hW (Filter.Eventually.of_forall hWn)
  have heF := ofReal_integral_eq_lintegral_ofReal (hF2 N).integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (F N x)))
  have heFn : (∫⁻ x, ENNReal.ofReal (F N x^2) ∂μ)=squareIntegral μ (F N) := by
    apply lintegral_congr
    intro x
    rw [←sq_abs,←Real.norm_eq_abs,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  calc
    _ = ∫⁻ x, variationCube G N x^(2/3:ℝ) ∂μ := by
      apply lintegral_congr
      intro x
      rw [variationCube_freeze]
    _ ≤ ∫⁻ x, ENNReal.ofReal (2048*weightedRelativeExitEnergy G (N+1) x) ∂μ :=
      lintegral_mono (variationCube_relative_energy G N)
    _ = ENNReal.ofReal (2048*(∫ x, weightedRelativeExitEnergy G (N+1) x ∂μ)) := by
      simp_rw [ENNReal.ofReal_mul (show (0:ℝ)≤2048 by norm_num)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←heW]
    _ ≤ ENNReal.ofReal (1024*(∫ x, F N x^2 ∂μ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh : (∫ x, weightedRelativeExitEnergy G (N+1) x ∂μ)≤(1/2)*(∫ x, F N x^2 ∂μ) := by
        simpa only [G,min_eq_right (Nat.le_succ N)] using hWi
      linarith
    _ = (1024:ℝ≥0∞)*squareIntegral μ (F N) := by
      rw [ENNReal.ofReal_mul (by norm_num),heF,heFn]
      norm_num

/-- The published input is discharged without adding assumptions. -/
theorem lepingleInput_proved : LepingleInput := by
  refine ⟨32,by norm_num,?_⟩
  intro Ω m μ hμ ℱ F hF hF2 N
  let : IsProbabilityMeasure μ := hμ
  convert martingale_variation_L2 hF hF2 N using 1; norm_num

end LipschitzHilbert

end

end OAI
