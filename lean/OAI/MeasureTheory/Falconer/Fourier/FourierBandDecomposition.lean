import OAI.MeasureTheory.Falconer.Shells.Shells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem fourier_band_split (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L H : ℝ} (hL : 0 ≤ L) (hLH : L ≤ H) :
    (∫ r in Icc (-H) H, ‖charFun μ r‖^2) =
      (∫ r in Icc (-L) L, ‖charFun μ r‖^2)+2*(∫ r in Icc L H, ‖charFun μ r‖^2) := by
  have hc : Continuous (fun r : ℝ => ‖charFun μ r‖^2) := continuous_charFun.norm.pow 2
  have hset (x y : ℝ) (hxy : x ≤ y) :
      (∫ r in Icc x y, ‖charFun μ r‖^2) = ∫ r in x..y, ‖charFun μ r‖^2 := by
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hxy]
  have heven (u : ℝ) :
      (∫ r in -u..0, ‖charFun μ r‖^2) = ∫ r in 0..u, ‖charFun μ r‖^2 := by
    have he := intervalIntegral.integral_comp_neg (f := fun r => ‖charFun μ r‖^2) (a := 0) (b := u)
    simpa only [fourier_energy_even,neg_zero] using he.symm
  have hband (u : ℝ) : (∫ r in -u..u, ‖charFun μ r‖^2) =
      2*(∫ r in 0..u, ‖charFun μ r‖^2) := by
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) (a := -u) (b := 0)) (hc.intervalIntegrable (μ := volume) (a := 0) (b := u))
    rw [heven] at he
    linarith
  rw [hset _ _ (by linarith),hset _ _ (by linarith),hset _ _ hLH,hband,hband]
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a := 0) (b := L)) (hc.intervalIntegrable (μ := volume) (a := L) (b := H))
  linarith

theorem fourier_dyadic_band_decomposition (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t : ℕ} (hat : a ≤ t) :
    (∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2) =
      (∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2)+
      2*∑ v ∈ Finset.Ioc a t,
        ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2 := by
  induction t,hat using Nat.le_induction with
  | base => simp
  | succ t hat ih =>
    rw [Finset.sum_Ioc_succ_top hat]
    have hs := fourier_band_split μ (L := (2:ℝ)^t) (H := (2:ℝ)^(t+1))
      (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ t))
    rw [ih] at hs
    have he : ((t+1:ℕ):ℝ)-1 = (t:ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
    linarith

theorem fourier_shell_le_band (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℕ) :
    (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤
      ∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun μ r‖^2 := by
  apply setIntegral_mono_set
    ((continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun r => sq_nonneg ‖charFun μ r‖)
  exact Filter.Eventually.of_forall (fun r hr => ⟨by linarith [hr.1,Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((v:ℝ)-1),pow_pos (by norm_num : (0:ℝ)<2) v],hr.2⟩)

theorem fourier_shell_le_expanded (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℕ) :
    (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤
      ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)), ‖charFun μ r‖^2 := by
  apply setIntegral_mono_set
    ((continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun r => sq_nonneg ‖charFun μ r‖)
  apply Filter.Eventually.of_forall
  intro r hr
  refine ⟨hr.1,hr.2.trans ?_⟩
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end PlanarFalconer

end OAI
