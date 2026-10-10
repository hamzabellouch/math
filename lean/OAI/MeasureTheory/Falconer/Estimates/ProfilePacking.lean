import OAI.MeasureTheory.Falconer.Estimates.ProfileEnvelopes
import OAI.MeasureTheory.Falconer.Estimates.OccupiedPacking

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

theorem sourceClass_local_count (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) (x : Plane) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ((occupiedCenterCells Q (sourceClass Q μ N B p₀) p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
      (4*(C₀/Q.side+1)^2)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ g+6*lam) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) := regularization_class_probability Q hQ μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  have hRp : 0 < R := by dsimp [R]; positivity
  have hh := occupied_center_count_le Q hQ (sourceClass Q μ N B p₀) hgp x
    (C₀ := C₀/Q.side) (by positivity) (r := C₀/(2:ℝ)^g)
    (div_mul_div_cancel₀ (ne_of_gt hQ)).ge
    (lo := R^(-3*lam)*R^(-sourceProfile Q μ N B p₀ p)) (by positivity)
    (hi := R^(3*lam)*R^(-sourceProfile Q μ N B p₀ g)) (by positivity)
    (fun q hq hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hpN
      ((mem_dyadicPaths p q).mp hq) hpos).1)
    (fun q hq hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ (hgp.trans hpN)
      ((mem_dyadicPaths g q).mp hq) hpos).2)
  apply hh.trans_eq
  rw [mul_div_assoc]
  congr 1
  rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 1
  ring

end PlanarFalconer

end OAI
