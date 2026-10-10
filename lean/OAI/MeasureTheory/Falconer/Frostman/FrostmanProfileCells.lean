import OAI.MeasureTheory.Falconer.Estimates.ProfileEnvelopes
import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking
import OAI.MeasureTheory.Falconer.Estimates.ClassPruning
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem dyadic_rpow_scale {N : ℕ} (hN : 0 < N) (n : ℕ) (s : ℝ) :
    ((2:ℝ)^N)^(-s*(n:ℝ)/(N:ℝ)) = (((2:ℝ)^n)^s)⁻¹ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*(-s*(n:ℝ)/(N:ℝ)) = -((n:ℝ)*s) := by field_simp
  rw [he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]

theorem dyadic_cell_frostman_profile_bound (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsFiniteMeasure μ] {s C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    {N : ℕ} (hN : 0 < N) (p : CellPath) :
    (μ (Q.descendant p).carrier).toReal ≤
      (C*(3*Q.side)^s)*((2:ℝ)^N)^(-s*(p.length:ℝ)/(N:ℝ)) := by
  have hb := dyadic_cell_frostman_bound Q hQ μ hball p
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hP : 0 < (Q.descendant p).side := Q.descendant_side_pos hQ p
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C*(3*(Q.descendant p).side)^s)] at hh
  apply hh.trans_eq
  rw [Q.descendant_side,dyadic_rpow_scale hN]
  rw [show 3*(Q.side/(2:ℝ)^p.length) = (3*Q.side)/(2:ℝ)^p.length by ring,
    Real.div_rpow (by positivity) (by positivity)]
  ring

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

theorem retained_label_real_mass_lower (Q : DyadicSquare) (μ : Measure Plane)
    [IsFiniteMeasure μ] {N B : ℕ} {p : CellPath} {lam : ℝ}
    (hp : regularizationLabel Q μ N B p ∈ retainedClassLabels Q μ N B
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    ((2:ℝ)^N)^(-lam) ≤ (classMeasure Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) univ).toReal := by
  have hm := retainedClass_mass_lower Q μ hp
  simp only [classMeasure,Measure.restrict_apply_univ] at hm ⊢
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^N)^(-lam))] using hh

theorem sourceProfile_envelope_from_frostman (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] {δ C lam : ℝ} (hC : 0 ≤ C)
    (hlam : 0 < lam) (hball : ∀ x : Plane, ∀ r > 0,
      μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀, ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ retainedClassLabels Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∀ n ≤ N, δ*(n:ℝ)/(N:ℝ)-5*lam ≤ sourceProfile Q μ N (N/H) p n-(n:ℝ)/(N:ℝ) ∧
        sourceProfile Q μ N (N/H) p n-(n:ℝ)/(N:ℝ) ≤ (n:ℝ)/(N:ℝ) := by
  obtain ⟨H,N₁,hH,hscales⟩ := exists_regularization_block_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(3*Q.side)^(1+δ))
  refine ⟨H,max N₁ N₂,hH,?_⟩
  intro N hN p hp hret n hn
  have hs := hscales N ((le_max_left _ _).trans hN)
  refine ⟨?_,sourceProfile_upper Q μ hs.1 hs.2.1 p (Nat.cast_nonneg n) (Nat.cast_le.mpr hn)⟩
  apply sourceProfile_frostman_lower Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
    (retained_label_real_mass_lower Q μ hret) _ hn
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound Q hQ μ hC hball hs.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN)) (by positivity))

end PlanarFalconer

end OAI
