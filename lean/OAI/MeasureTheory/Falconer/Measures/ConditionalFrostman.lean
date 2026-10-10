import OAI.MeasureTheory.Falconer.Estimates.RescaledConditional
import OAI.MeasureTheory.Falconer.Angular.AllDimensionalAngularProfileSum

namespace OAI

/-! # Finite-scale Frostman bounds for the full rescaled conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def profileDrop (m : ℝ → ℝ) (N : ℕ) (s : ℝ) (p t : ℕ) : ℝ :=
  (m p-s*(p:ℝ)/N)-PlanarFalconer.intervalMin (fun n : ℕ => m n-s*(n:ℝ)/N) p t

theorem profileDrop_nonneg (m : ℝ → ℝ) (N : ℕ) (s : ℝ) {p t : ℕ} (hpt : p ≤ t) :
    0 ≤ profileDrop m N s p t := by
  exact sub_nonneg.mpr (PlanarFalconer.intervalMin_le _ le_rfl hpt)

theorem profile_drop_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (s E : ℝ)
    {p n t : ℕ} (hpn : p ≤ n) (hnt : n ≤ t) :
    ((2:ℝ)^N)^(m p-m n+E) ≤
      ((2:ℝ)^N)^(profileDrop m N s p t+E)*(1/(2:ℝ)^(n-p))^s := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hd : (1/(2:ℝ)^(n-p))^s = ((2:ℝ)^N)^(-s*(n-p:ℕ)/N) := by
    rw [one_div,Real.inv_rpow (by positivity),dyadic_power_rpow_as_R hN,
      ← Real.rpow_neg hR.le]
    congr 1
    ring
  rw [hd,← Real.rpow_add hR]
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  have hh := PlanarFalconer.intervalMin_le (fun k : ℕ => m k-s*(k:ℝ)/N) hpn hnt
  dsimp only [profileDrop]
  rw [Nat.cast_sub hpn]
  calc
    m p-m n+E ≤ m p-(PlanarFalconer.intervalMin
      (fun k : ℕ => m k-s*(k:ℝ)/N) p t+s*(n:ℝ)/N)+E := by linarith
    _ = _ := by ring

theorem sourceClass_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(profileDrop (sourceProfile Q μ N B p₀) N s p t+2*((d:ℝ)+1)*lam)*r^s) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let α := Measure.map (cellScaleMap p (Q.descendant P).center)
    (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hPpos
  have : IsFiniteMeasure α := by dsimp [α]; infer_instance
  let m := sourceProfile Q μ N B p₀
  let E := 2*((d:ℝ)+1)*lam
  let D : ℝ := ((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ)
  let R : ℝ := (2:ℝ)^N
  intro x r hr hr₁
  obtain ⟨j,hj,hrj,hjr⟩ := dyadic_radius_bracket hr hr₁
  have hn : p+j ≤ t := by omega
  have hball := sourceClass_rescaled_dyadic_ball Q hQ μ hN hB hwidth hlarge hp₀
    (Nat.le_add_right p j) (hn.trans htN) hP hPpos x (show (0:ℝ) ≤ 1 by norm_num)
  simp only [Nat.add_sub_cancel_left,mul_one] at hball
  have hmono : (α (ball x r)).toReal ≤ (α (ball x (1/(2:ℝ)^j))).toReal :=
    ENNReal.toReal_mono (measure_ne_top α _) (measure_mono (ball_subset_ball hrj))
  have hweight := profile_drop_weight m hN s E (Nat.le_add_right p j) hn
  simp only [Nat.add_sub_cancel_left] at hweight
  have hrpow : (1/(2:ℝ)^j)^s ≤ (2*r)^s :=
    Real.rpow_le_rpow (by positivity) hjr hs
  have hbound : (α (ball x r)).toReal ≤ D*(2:ℝ)^s*R^(profileDrop m N s p t+E)*r^s := by
    calc
      _ ≤ D*R^(m p-m ((p+j:ℕ):ℝ)+E) := hmono.trans hball
      _ ≤ D*(R^(profileDrop m N s p t+E)*(1/(2:ℝ)^j)^s) :=
        mul_le_mul_of_nonneg_left hweight (by dsimp [D]; positivity)
      _ ≤ D*(R^(profileDrop m N s p t+E)*(2*r)^s) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow (by positivity))
          (by dsimp [D]; positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith [hrj,hjr])]; ring
  change α (ball x r) ≤ _
  rw [← ENNReal.ofReal_toReal (measure_ne_top α _)]
  exact ENNReal.ofReal_le_ofReal hbound

end Falconer.Regularization

end OAI
