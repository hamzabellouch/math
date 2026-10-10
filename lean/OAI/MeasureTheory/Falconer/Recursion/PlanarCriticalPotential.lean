import OAI.MeasureTheory.Falconer.Recursion.FiniteCountingPotential
import OAI.MeasureTheory.Falconer.Recursion.CriticalTruncatedPotential

namespace OAI

/-! Critical finite planar potential with the exact linear depth loss.
This is used to control the distribution of cells along a selected tube. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_dyadic_critical_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K t : ℝ} (_hK : 0 ≤ K) (ht : 0 ≤ t)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^t)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^t)*
        (ENNReal.ofReal (K*(P.card:ℝ))+(N:ℝ≥0∞)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^t) := by
    rw [planarCountingMeasure_apply]
    have hr0 : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hj)
    have hr1 : 1/(2:ℝ)^j ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact one_le_pow₀ (by norm_num)
    have hs : P.filter (fun y => dist x y < 1/(2:ℝ)^j) ⊆
        P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j) := by
      intro y hy
      obtain ⟨hyP,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP,by simpa only [dist_comm] using hy.le⟩
    have hc := (show ((P.filter (fun y => dist x y < 1/(2:ℝ)^j)).card : ℝ) ≤
      (P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j)).card from by exact_mod_cast Finset.card_le_card hs)
    have hh := hc.trans (hball x _ hr0 hr1)
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^t = K*(1/(2:ℝ)^j)^t*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential_critical μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) ht 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^t)
  have hfar : (∫⁻ y in Aᶜ, F y ∂μ) ≤ P.card := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by measurability)
        intro y hy
        change ¬ dist x y < 1 at hy
        have hd : 1 ≤ max (dist x y) (1/(2:ℝ)^N) :=
          (le_of_not_gt hy).trans (le_max_left _ _)
        have hinv : 1/max (dist x y) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv ht).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

noncomputable def planarCriticalConstant (N : ℕ) (t : ℝ) : ℝ :=
  1+(2:ℝ)^t*(1+(N:ℝ)*(2:ℝ)^t)

theorem finite_dyadic_critical_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K t : ℝ} (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^t) ≤
      K*planarCriticalConstant N t*(P.card:ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh := finite_dyadic_critical_potential P x N hK0 ht hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity)] at hh
  have he : (P.card:ℝ≥0∞)+ENNReal.ofReal ((2:ℝ)^t)*
      (ENNReal.ofReal (K*(P.card:ℝ))+(N:ℝ≥0∞)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) =
      ENNReal.ofReal ((P.card:ℝ)+(2:ℝ)^t*(K*(P.card:ℝ)+(N:ℝ)*((K*(P.card:ℝ))*(2:ℝ)^t))) := by
    symm
    calc
      _ = ENNReal.ofReal (P.card:ℝ) + ENNReal.ofReal ((2:ℝ)^t) *
          (ENNReal.ofReal (K*(P.card:ℝ)) +
            ENNReal.ofReal (N:ℝ)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) := by
        conv_lhs =>
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity),
            ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      _ = _ := by simp only [ENNReal.ofReal_natCast]
  rw [he] at hh
  have hb := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hh
  have hc := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (α := ℝ) P.card)
  unfold planarCriticalConstant
  nlinarith only [hb,hc]

end Falconer

end OAI
