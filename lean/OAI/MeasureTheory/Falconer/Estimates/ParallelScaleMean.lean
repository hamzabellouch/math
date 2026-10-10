import OAI.MeasureTheory.Falconer.Estimates.ParallelNumerics

namespace OAI

/-! # The manuscript parallel-test mean at its actual width -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_parallel_scale_mean (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {sig s : ℝ} (hsig : 0 < sig) (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ sig*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^sig)
    (hroot : Real.sqrt d ≤ ((2:ℝ)^N)^(500*sig))
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath d} (hP : P.length = p)
    (ν : Measure (Sphere d)) (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^s)) :
    (∫⁻ w, (parallelTestCount Q (sourceClass Q μ N B p₀) g p P
      ((2*((2:ℝ)^N)^(500*sig))/(2:ℝ)^p) w : ℝ≥0∞) ∂ν) ≤
      1+ENNReal.ofReal ((2*(6:ℝ)^s*(parallelPackingConstant d:ℝ)*(1+(2:ℝ)^s*(p-g:ℕ)))*
        ((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p+
            (2*((d:ℝ)+1)+1+500*s)*sig)) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hp2 : (2:ℝ)^p ≤ R := pow_le_pow_right₀ (by norm_num) hpN
  have hscale : R^(-1:ℝ)*Real.sqrt d ≤ 3*((2*R^(500*sig))/(2:ℝ)^p) := by
    calc
      _ = Real.sqrt d/R := by rw [Real.rpow_neg_one]; ring
      _ ≤ R^(500*sig)/R := div_le_div_of_nonneg_right hroot hRp.le
      _ ≤ R^(500*sig)/(2:ℝ)^p := div_le_div_of_nonneg_left (by positivity) (by positivity) hp2
      _ ≤ _ := by
        have hh : 0 ≤ R^(500*sig)/(2:ℝ)^p := by positivity
        nlinarith [show 3*((2*R^(500*sig))/(2:ℝ)^p) = 6*(R^(500*sig)/(2:ℝ)^p) by ring]
  have hm := sourceClass_parallel_mean Q hQ μ hN hB hs hwidth hlarge hp₀ hgp hpN hP ν
    (by positivity : 0 ≤ R^(-1:ℝ)) (by positivity : 0 < (2*R^(500*sig))/(2:ℝ)^p)
    (Real.one_le_rpow hR hsig.le) hmass hscale hball
  rw [parallel_mean_scale_identity hRp] at hm
  exact hm

end Falconer.Regularization

end OAI
