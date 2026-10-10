import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateKernels
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! Derivative bounds for one moving gate, expressed through the velocity
and the rescaled center. Only positive derivatives of the center enter. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff BigOperators

def gatePacket (v z : ℝ × Plane → Plane) (y : ℝ × Plane) : Plane :=
  ∑ j : Fin 2, v y j • gateKernel j (z y)

theorem gatePacket_jet_bound {v z : ℝ × Plane → Plane}
    (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ z)
    (n : ℕ) (y : ℝ × Plane) {C D ε : ℝ}
    (_hC : 0 ≤ C) (_hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hk : ∀ j : Fin 2, ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (gateKernel j) x‖ ≤ C)
    (hvel : ∀ j : Fin 2, ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i (fun p => v p j) y‖ ≤ ε)
    (hcenter : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i z y‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (gatePacket v z) y‖ ≤
      2 * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ε * ((n - i).factorial * C * D ^ (n - i)) := by
  have hs (j : Fin 2) : ContDiff ℝ ∞
      (fun p : ℝ × Plane => v p j • gateKernel j (z p)) :=
    ((contDiff_apply ℝ ℝ j).comp hv).smul ((gateKernel_smooth j).comp hz)
  unfold gatePacket
  rw [iteratedFDeriv_fun_sum_apply
    (fun j _ => ((hs j).of_le (by simp)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  have hb (j : Fin 2) :
      ‖iteratedFDeriv ℝ n (fun p => v p j • gateKernel j (z p)) y‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ε * ((n - i).factorial * C * D ^ (n - i)) := by
    apply (norm_iteratedFDeriv_smul_le ((contDiff_apply ℝ ℝ j).comp hv)
      ((gateKernel_smooth j).comp hz) y (by simp : (n : ℕ∞ω) ≤ ∞)).trans
    apply Finset.sum_le_sum
    intro i hi
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hcomp : ‖iteratedFDeriv ℝ (n - i) (fun p => gateKernel j (z p)) y‖ ≤
        (n - i).factorial * C * D ^ (n - i) :=
      norm_iteratedFDeriv_comp_le (gateKernel_smooth j) hz (by simp) y
        (fun k hk' => hk j k (hk'.trans (Nat.sub_le n i)) _)
        (fun k hk' hkn => hcenter k hk' (hkn.trans (Nat.sub_le n i)))
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hvel j i hin) (Nat.cast_nonneg _)) hcomp
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hε)
  calc
    _ ≤ ∑ _j : Fin 2, ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ε * ((n - i).factorial * C * D ^ (n - i)) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [two_mul]

end ForcedComputation.ExpandingDetector

end

end OAI
