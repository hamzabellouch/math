import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.DyadicLongScales
import OAI.Analysis.LipschitzHilbert.Estimates.LongScaleVariation
import OAI.Analysis.LipschitzHilbert.Packets.HilbertPacketSums

namespace OAI

/-! Long-scale oscillation for actual Hilbert packet synthesis. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem long_line_variation {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W y u r C : ℝ) (hL : 0 < L) (hW : W ≠ 0) (hr : 0 < r) (hC : 0 ≤ C)
    (hc : ∀ j i, ‖c j i‖ ≤ 1)
    (hderiv : ∀ j i k x, ‖deriv (f j i k) x‖ ≤ (C / (L / (2 : ℝ) ^ j.val)) *
      (lineEnvelope (a + (L / (2 : ℝ) ^ j.val) * (site j i).1)
        (L / (2 : ℝ) ^ j.val) 3 x *
        lineEnvelope (b + W * (site j i).2) W 2 y))
    {x z : ℝ} (hx : x ∈ Icc (u - r) (u + r)) (hz : z ∈ Icc (u - r) (u + r)) :
    cubicVariation (fun n =>
      hilbertPartialBandSum (fun j k => if r < L / (2 : ℝ) ^ j.val then
        packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n x -
      hilbertPartialBandSum (fun j k => if r < L / (2 : ℝ) ^ j.val then
        packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n z) N ≤
      4 * (C * (4 * Real.pi) ^ 2) := by
  let len := fun j : Fin N => L / (2 : ℝ) ^ j.val
  let F := fun (j : Fin N) x => if r < len j then vectorPacketSynthesis (c j) (f j) x else 0
  let D := fun j : Fin N => if r < len j then (C / len j) * (4 * Real.pi) ^ 2 else 0
  have hlen (j : Fin N) : 0 < len j := div_pos hL (pow_pos (by norm_num) _)
  have hF (j : Fin N) (x : ℝ) : DifferentiableAt ℝ (F j) x := by
    by_cases hj : r < len j
    · simpa only [F, ite_eq_left hj] using (vectorPacketSynthesis_hasDerivAt (c j) (f j) x).differentiableAt
    · simpa only [F, ite_eq_right hj] using (hasDerivAt_const x (0 : EuclideanSpace ℂ κ)).differentiableAt
  have hd (j : Fin N) (x : ℝ) : ‖deriv (F j) x‖ ≤ D j := by
    by_cases hj : r < len j
    · simpa only [F, D, ite_eq_left hj] using
        tile_vectorPacketSynthesis_deriv_bound (c j) (f j) (site j) (hinj j)
          a b (len j) W x y C (hlen j) hW hC (hc j) (fun i k => hderiv j i k x)
    · simp only [F, D, ite_eq_right hj, deriv_const, norm_zero, le_refl]
  have hsum : (∑ j, D j) ≤ (C * (4 * Real.pi) ^ 2) * (2 / r) := by
    have heq (j : Fin N) : D j = (C * (4 * Real.pi) ^ 2) *
        (if r < len j then (len j)⁻¹ else 0) := by
      by_cases hj : r < len j <;> simp only [D, hj, ite_true, ite_false, mul_zero]
      rw [div_eq_mul_inv]
      ring
    simp_rw [heq]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_long_dyadic_reciprocals N L r hL hr) (by positivity)
  have heq (n : ℕ) (v : ℝ) :
      hilbertPartialBandSum (fun j k => if r < len j then
        packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n v =
        packetPartialSum (fun j => F j v) n := by
    rw [hilbertPartialBandSum_eq_packetPartialSum]
    congr 1
    funext j
    by_cases hj : r < len j
    · simp only [F, ite_eq_left hj, vectorPacketSynthesis]
    · simp only [F, ite_eq_right hj]
      rfl
  change cubicVariation (fun n =>
    hilbertPartialBandSum (fun j k => if r < len j then
      packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n x -
    hilbertPartialBandSum (fun j k => if r < len j then
      packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n z) N ≤ _
  simp_rw [heq]
  have hdist : |x - z| ≤ 2 * r :=
    abs_le.mpr ⟨by linarith [hx.1,hz.2], by linarith [hx.2,hz.1]⟩
  calc
    _ ≤ (∑ j, D j) * |x - z| :=
      long_scale_variation_lipschitz F _ _ D (fun j x _ => hF j x) (fun j x _ => hd j x) hx hz
    _ ≤ ((C * (4 * Real.pi) ^ 2) * (2 / r)) * (2 * r) :=
      mul_le_mul hsum hdist (abs_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end LipschitzHilbert

end

end OAI
