import OAI.Probability.FreeIsing.Ising.CopyResponseRowPaths
import OAI.Probability.FreeIsing.Ising.RootDoubleExponential

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingConditionalCopyBounds ConnectedHull
open IsingRootAttenuation IsingRootDoubleExponential TreeOrbitAverage
open IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem linearEnergy_eq_root_weight (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) :
    linearEnergy (μ := μ) hb t v =
      ∫ z, (fieldDifference beta (root d) t z) ^ 2 *
        rootAttenuation hb t v (observationCopy true z) ^ 2 ∂copies beta μ := rfl

theorem linearEnergy_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) (hn : 2 ≤ v.1.length)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * v.1.length)) :
    linearEnergy (μ := μ) hb t v ≤
      (∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ) *
        Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * v.1.length) +
      (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
        Real.exp (-(((d : ℝ) - 1) ^ ((v.1.length : ℝ) / 4)) /
          (2 * ((d : ℝ) - 1))) := by
  let n := v.1.length
  let k := n / 2 - 1
  let L := n - n / 2
  have hk : k + 1 = n / 2 := by dsimp [k, n]; omega
  have hsum : k + 1 + L = n := by dsimp [L]; omega
  let s : Extension ([] : List (Fin d)) (k + 1 + L) :=
    ⟨v.1, hsum.symm, by change v.1.IsChain (· ≠ ·); exact v.2⟩
  have hs : endpoint s = v := by apply Subtype.ext; rfl
  have hlevel : (n : ℝ) / 2 - 1 ≤ (k + 1 : ℕ) := by
    rw [hk]
    have hround : n ≤ 2 * (n / 2) + 1 := by omega
    have hr : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast hround
    linarith
  have htail : (n : ℝ) / 2 ≤ (L : ℝ) := by
    have hround : n ≤ 2 * L := by dsimp [L]; omega
    have hr : (n : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hround
    linarith
  have h := integral_root_weight_mul_sq_le_double_exp hμ hb hd hcritical ht true k L s
    hη0 (Nat.cast_nonneg n) hη hηlog hlevel htail hlength
  rw [hs, ← linearEnergy_eq_root_weight] at h
  simpa only [mul_comm (Real.exp _) (∫ z, (fieldDifference beta (root d) t z) ^ 2
    ∂copies beta μ)] using h

theorem exists_linear_energy_long_constants
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) :
    ∃ c a q C₀ : ℝ, 0 < c ∧ 0 < a ∧ 1 < q ∧ 0 < C₀ ∧
      ∀ (T t : ℝ≥0), 0 < t → t ≤ T → ∀ v : TreeVertex d,
        C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        linearEnergy (μ := μ) hb t v ≤
          (∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ) *
            Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length) +
          (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
            Real.exp (-a * q ^ v.1.length) := by
  let b : ℝ := (d : ℝ) - 1
  have hb1 : 1 < b := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [b]
    linarith
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  have hθ : 0 < Real.tanh beta := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (tanh_nonneg_of_beta_nonneg hb)
    simp [hz] at hcritical
  let γ := ComponentSignalAttenuation.lossCoefficient (Real.tanh beta)
  have hγ : 0 < γ := ComponentSignalAttenuation.lossCoefficient_pos hθ (Real.tanh_lt_one beta)
  let c := min (γ / 4) (Real.log b / 8)
  let a := 1 / (2 * b)
  let q := b ^ (1 / 4 : ℝ)
  let C₀ := max 2 (8 * Real.log 2 / γ)
  have hc : 0 < c := lt_min (div_pos hγ (by norm_num))
    (div_pos (Real.log_pos hb1) (by norm_num))
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 1 < q := Real.one_lt_rpow hb1 (by norm_num)
  have hC₀ : 0 < C₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨c, a, q, C₀, hc, ha, hq, hC₀, ?_⟩
  intro T t ht htT v hn
  let ω := min (Real.sqrt (t : ℝ)) 1
  have hω : 0 < ω := lt_min (Real.sqrt_pos.2 (show 0 < (t : ℝ) from ht)) zero_lt_one
  have hω1 : ω ≤ 1 := min_le_right _ _
  have hlarge : C₀ ≤ (v.1.length : ℝ) * ω := (div_le_iff₀ hω).mp hn
  have hnR : (2 : ℝ) ≤ v.1.length := by
    have hmul := mul_le_mul_of_nonneg_left hω1 (Nat.cast_nonneg v.1.length : (0 : ℝ) ≤ _)
    have htwo : (2 : ℝ) ≤ C₀ := le_max_left _ _
    nlinarith
  have hn2 : 2 ≤ v.1.length := by exact_mod_cast hnR
  have hlarge' : 8 * Real.log 2 / γ ≤ ω * (v.1.length : ℝ) :=
    (le_max_right _ _).trans (by simpa only [mul_comm] using hlarge)
  have hlength : 8 * Real.log 2 ≤ γ * (ω * v.1.length) := by
    have h := (div_le_iff₀ hγ).mp hlarge'
    nlinarith
  have h := linearEnergy_le_double_exp hμ hb hd hcritical ht v hn2 hc.le
    (min_le_left _ _) (min_le_right _ _) hlength
  have hpow : b ^ ((v.1.length : ℝ) / 4) = q ^ v.1.length := by
    rw [show (v.1.length : ℝ) / 4 = (1 / 4 : ℝ) * v.1.length by ring,
      Real.rpow_mul hb0.le, Real.rpow_natCast]
  have hexp : -b ^ ((v.1.length : ℝ) / 4) / (2 * b) = -a * q ^ v.1.length := by
    rw [hpow]
    dsimp [a]
    ring
  change linearEnergy (μ := μ) hb t v ≤ _ +
    (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
      Real.exp (-b ^ ((v.1.length : ℝ) / 4) / (2 * b)) at h
  rw [hexp] at h
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (by positivity)
  have htTR : (t : ℝ) ≤ T := htT
  linarith

end Problem367.IsingCopyResponseRowPaths

end

end OAI
