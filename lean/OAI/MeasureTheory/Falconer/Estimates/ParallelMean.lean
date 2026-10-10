import OAI.MeasureTheory.Falconer.Estimates.ParallelGood
import OAI.MeasureTheory.Falconer.Angular.AngularTubeMean

namespace OAI

/-! # Parallel-test averages for the original regularized class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_center_difference_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (p q : CellPath d) :
    ‖(Q.descendant p).center-(Q.descendant q).center‖ ≤ Real.sqrt d*Q.side := by
  rw [← dist_eq_norm]
  exact Q.dist_le hQ.le
    (Q.descendant_subset p ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p)))
    (Q.descendant_subset q ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q)))

theorem sourceClass_parallel_mean (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath d} (hP : P.length = p)
    (ν : Measure (Sphere d)) {δ W L : ℝ} (hδ : 0 ≤ δ) (hW : 0 < W)
    (hL : 1 ≤ L) (hmass : ν univ ≤ 1) (hscale : δ*Real.sqrt d ≤ 3*W)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s)) :
    (∫⁻ w, (parallelTestCount Q (sourceClass Q μ N B p₀) g p P W w : ℝ≥0∞) ∂ν) ≤
      1+ENNReal.ofReal (2*L*(3*W)^s*((2:ℝ)^p)^s*(parallelPackingConstant d:ℝ)*
        (1+(2:ℝ)^s*(p-g:ℕ))*((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p+2*((d:ℝ)+1)*lam)) := by
  classical
  let S := parallelTestCells Q (sourceClass Q μ N B p₀) g p P
  let v := fun c => (Q.descendant c).center-(Q.descendant P).center
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hv (c : CellPath d) (hc : c ∈ S.erase P) : v c ≠ 0 := by
    have hc' := Finset.mem_of_mem_erase hc
    have hl := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hc').1
    have hh := Q.centers_separated hside hl hP (Finset.ne_of_mem_erase hc)
    intro hz
    have hz' : dist (Q.descendant c).center (Q.descendant P).center = 0 := by
      rw [dist_eq_norm]
      exact norm_eq_zero.mpr hz
    rw [hz'] at hh
    exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^p)) hh
  have hsc (c : CellPath d) (hc : c ∈ S.erase P) : δ ≤ 3*W/‖v c‖ := by
    apply (le_div_iff₀ (norm_pos_iff.mpr (hv c hc))).mpr
    have hh := dyadic_center_difference_bound Q hside c P
    rw [hQ,mul_one] at hh
    exact (mul_le_mul_of_nonneg_left hh hδ).trans hscale
  have hm := tube_mean_inverse_power S P v ν hW hL hs hmass hball hv hsc
  apply hm.trans
  apply add_le_add le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hi := sourceClass_parallel_inverse_power Q hQ μ hN hB hs hwidth hlarge hp₀ hgp hpN hP
  have hip := (div_le_iff₀ (by positivity : 0 < ((2:ℝ)^p)^s)).mp hi
  have hh := mul_le_mul_of_nonneg_left hip (by positivity : 0 ≤ 2*L*(3*W)^s)
  calc
    _ = 2*L*(3*W)^s * ∑ c ∈ (parallelTestCells Q (sourceClass Q μ N B p₀) g p P).erase P,
        (1/dist (Q.descendant c).center (Q.descendant P).center)^s := by
      simp only [S,v,dist_eq_norm]
    _ ≤ _ := hh
    _ = _ := by ring

theorem parallel_mean_width_cancellation {A s : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    (3*(A/(2:ℝ)^p))^s*((2:ℝ)^p)^s = (3*A)^s := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

end Falconer.Regularization

end OAI
