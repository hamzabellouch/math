import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds
import OAI.MeasureTheory.Falconer.Recursion.TruncatedScalarPotential
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

/-! The finite point potential needed by the elementary planar incidence bound. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def planarCountingMeasure (P : Finset (Space 2)) : Measure (Space 2) :=
  ∑ x ∈ P, Measure.dirac x

theorem planarCountingMeasure_apply (P : Finset (Space 2)) (A : Set (Space 2)) :
    planarCountingMeasure P A = (P.filter (fun x => x ∈ A)).card := by
  rw [planarCountingMeasure,Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

theorem planarCountingMeasure_lintegral (P : Finset (Space 2)) (f : Space 2 → ℝ≥0∞) :
    (∫⁻ x, f x ∂planarCountingMeasure P) = ∑ x ∈ P, f x := by
  rw [planarCountingMeasure,lintegral_finsetSum_measure]
  simp only [lintegral_dirac]

theorem finite_dyadic_truncated_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f)))) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^f) := by
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
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^f = K*(1/(2:ℝ)^j)^f*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) (mul_nonneg hK (Nat.cast_nonneg _)) hb hbf 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add,Real.one_rpow,mul_one] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)
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
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv hb).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

noncomputable def planarPotentialConstant (b f : ℝ) : ℝ :=
  1+(2:ℝ)^b*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f)))

theorem planarPotentialConstant_pos {b f : ℝ} (hbf : b < f) :
    0 < planarPotentialConstant b f := by
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  unfold planarPotentialConstant
  positivity

theorem finite_dyadic_truncated_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 1 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^b) ≤
      K*planarPotentialConstant b f*(P.card : ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  have hR : 0 ≤ (P.card : ℝ)+(2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by
    positivity
  have hh := finite_dyadic_truncated_potential P x N hK0 hb hbf hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity),
    ← ENNReal.ofReal_natCast P.card, ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity)] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff hR).mp hh
  apply hh'.trans
  unfold planarPotentialConstant
  have hC : 0 ≤ (2:ℝ)^b*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) P.card]

end Falconer

end OAI
