import OAI.Analysis.LipschitzHilbert.Estimates.EnvelopeSynthesis
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Dimension-free synthesis and derivative estimates on a reference line.
The multiplication of a Hilbert coefficient by a packet is componentwise. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem diagonal_packet_norm {κ : Type*} [Fintype κ]
    (c : EuclideanSpace ℂ κ) (v : κ → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hv : ∀ k, ‖v k‖ ≤ K) :
    ‖WithLp.toLp 2 (fun k => c k * v k)‖ ≤ K * ‖c‖ := by
  have hs : ‖WithLp.toLp 2 (fun k => c k * v k)‖ ^ 2 ≤ (K * ‖c‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    change ‖c k * v k‖ ^ 2 ≤ K ^ 2 * ‖c k‖ ^ 2
    rw [norm_mul, mul_pow, mul_comm (K ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hv k) 2)
      (sq_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => c k * v k)),
    mul_nonneg hK (norm_nonneg c)]

def vectorPacketSynthesis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => packetSynthesis (fun i => c i k) (fun i => f i k) x)

theorem vectorPacketSynthesis_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    vectorPacketSynthesis c f x = ∑ i, WithLp.toLp 2 (fun k => c i k * f i k x) := by
  ext k
  simp only [vectorPacketSynthesis, packetSynthesis_apply, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply]

theorem vectorPacketSynthesis_hasDerivAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (vectorPacketSynthesis c f)
      (WithLp.toLp 2 (fun k => ∑ i, c i k * deriv (f i k) x)) x := by
  have hd : HasDerivAt (fun x k => packetSynthesis (fun i => c i k) (fun i => f i k) x)
      (fun k => ∑ i, c i k * deriv (f i k) x) x := by
    apply hasDerivAt_pi.mpr
    intro k
    simp only [packetSynthesis_apply]
    have heq : (fun x => ∑ i, c i k * f i k x) = ∑ i, (fun x => c i k * f i k x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact HasDerivAt.sum (u := Finset.univ)
      (fun i _ => ((f i k).differentiable x).hasDerivAt.const_mul (c i k))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd

theorem vectorPacketSynthesis_deriv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (vectorPacketSynthesis c f) x =
      ∑ i, WithLp.toLp 2 (fun k => c i k * deriv (f i k) x) := by
  rw [(vectorPacketSynthesis_hasDerivAt c f x).deriv]
  ext k
  simp only [WithLp.ofLp_sum, Finset.sum_apply]

theorem vectorPacketSynthesis_deriv_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (w : ι → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hover : ∑ i, w i ≤ D) (x : ℝ)
    (hf : ∀ i k, ‖deriv (f i k) x‖ ≤ C * w i) :
    ‖deriv (vectorPacketSynthesis c f) x‖ ≤ C * D := by
  rw [vectorPacketSynthesis_deriv]
  calc
    _ ≤ ∑ i, ‖WithLp.toLp 2 (fun k => c i k * deriv (f i k) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact (diagonal_packet_norm (c i) _ (mul_nonneg hC (hw i)) (hf i)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hc i) (mul_nonneg hC (hw i)))
    _ ≤ C * D := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hover hC

theorem tile_vectorPacketSynthesis_deriv_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y C : ℝ) (hl : 0 < l) (hW : W ≠ 0) (hC : 0 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ 1)
    (hf : ∀ i k, ‖deriv (f i k) x‖ ≤ (C / l) *
      (lineEnvelope (a + l * (index i).1) l 3 x *
        lineEnvelope (b + W * (index i).2) W 2 y)) :
    ‖deriv (vectorPacketSynthesis c f) x‖ ≤ (C / l) * (4 * Real.pi) ^ 2 := by
  exact vectorPacketSynthesis_deriv_bound c f _ (div_nonneg hC hl.le)
    (fun i => mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) hc
    (injective_tile_lattice_overlap index hinj a b l W x y hl.ne' hW (by decide) (by decide)) x hf

end LipschitzHilbert

end

end OAI
