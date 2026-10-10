import OAI.MeasureTheory.Falconer.Recursion.ProfileEnvelopes
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# Frostman lower envelopes for the constructed all-dimensional profiles

The enclosing-ball constant is 2*sqrt d, and the numerical choice of block
length is independent of dimension.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_rpow_scale {N : ℕ} (hN : 0 < N) (j : ℕ) (s : ℝ) :
    ((2:ℝ)^N)^(-s*(j:ℝ)/(N:ℝ)) = (((2:ℝ)^j)^s)⁻¹ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*(-s*(j:ℝ)/(N:ℝ)) = -((j:ℝ)*s) := by field_simp
  rw [he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]

theorem dyadic_cell_frostman_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {s C : ℝ}
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    (p : CellPath d) :
    μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(2*Real.sqrt d*(Q.descendant p).side)^s) := by
  have hside := Q.descendant_side_pos hQ p
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  apply (measure_mono (show (Q.descendant p).carrier ⊆
      ball (Q.descendant p).center (2*Real.sqrt d*(Q.descendant p).side) from ?_)).trans
    (hball _ _ (by positivity))
  intro x hx
  have hh := (Q.descendant p).dist_le hside.le hx ((Q.descendant p).center_mem hside)
  exact mem_ball.mpr (by nlinarith [mul_pos hsqrt hside])

theorem dyadic_cell_frostman_profile_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {s C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    {N : ℕ} (hN : 0 < N) (p : CellPath d) :
    (μ (Q.descendant p).carrier).toReal ≤
      (C*(2*Real.sqrt d*Q.side)^s)*((2:ℝ)^N)^(-s*(p.length:ℝ)/(N:ℝ)) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (dyadic_cell_frostman_bound hd Q hQ μ hball p)
  have hside := Q.descendant_side_pos hQ p
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C*(2*Real.sqrt d*(Q.descendant p).side)^s)] at hh
  apply hh.trans_eq
  rw [Q.descendant_side,dyadic_rpow_scale hN]
  rw [show 2*Real.sqrt d*(Q.side/(2:ℝ)^p.length) =
    (2*Real.sqrt d*Q.side)/(2:ℝ)^p.length by ring,
    Real.div_rpow (by positivity) (by positivity)]
  ring

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have ht : Filter.Tendsto (fun N : ℕ => ((2:ℝ)^N)^lam) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hlam).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop C))

theorem retained_label_real_mass_lower (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] {N B : ℕ} {p : CellPath d} {lam : ℝ}
    (hp : regularizationLabel Q μ N B p ∈ regularizationIndex Q μ N B
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    ((2:ℝ)^N)^(-lam) ≤ (classMeasure Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) univ).toReal := by
  have hm := regularizationSet_mass Q μ N B _ hp
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simpa only [classMeasure,Measure.restrict_apply_univ,regularizationSet,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^N)^(-lam))] using hh

theorem sourceProfile_frostman_envelope (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {s C lam : ℝ} (hC : 0 ≤ C)
    (hlam : 0 < lam) (hball : ∀ x : Space d, ∀ r > 0,
      μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀, ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N (N/H) p j := by
  obtain ⟨H,N₁,hH,hscales⟩ := PlanarFalconer.exists_regularization_block_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(2*Real.sqrt d*Q.side)^s)
  refine ⟨H,max N₁ N₂,hH,?_⟩
  intro N hN p hp hret j hj
  have hs := hscales N ((le_max_left _ _).trans hN)
  apply sourceProfile_frostman_lower Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
    (retained_label_real_mass_lower Q μ hret) _ hj
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound hd Q hQ μ hC hball hs.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN)) (by positivity))

end Falconer.Regularization

end OAI
