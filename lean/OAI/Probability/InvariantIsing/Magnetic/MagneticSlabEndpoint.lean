import OAI.Probability.InvariantIsing.Magnetic.MagneticMeanShift
import OAI.Probability.InvariantIsing.Magnetic.MagneticUniformSlabBounds

namespace OAI

/-! Endpoint decay for bounded square continuations in a varying slab. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_family_continuation_endpoint {ι : Type*} {l : Filter ι}
    {M A B C D : ι → ℝ → ℝ} {x : ι → ℝ} {c L K : ℝ}
    (hc : c ^ 2 = 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hA : ∀ i z, (M i z) ^ 2 ≤ A i z ∧ A i z ≤ 1)
    (dA : ∀ i z, HasDerivAt (A i) (B i z) z)
    (dB : ∀ i z, HasDerivAt (B i) (C i z) z)
    (dC : ∀ i z, HasDerivAt (C i) (D i z) z)
    (bC : ∀ i z, |C i z| ≤ L) (bD : ∀ i z, |D i z| ≤ K)
    (hM : ∀ h : ℝ, Tendsto (fun i => M i (x i + h)) l (𝓝 c)) :
    Tendsto (fun i => B i (x i)) l (𝓝 0) ∧
      Tendsto (fun i => C i (x i)) l (𝓝 0) := by
  have hlim (h : ℝ) : Tendsto (fun i => A i (x i + h)) l (𝓝 (1 : ℝ)) := by
    have hs : Tendsto (fun i => (M i (x i + h)) ^ 2) l (𝓝 (1 : ℝ)) := by
      simpa only [hc] using (hM h).pow 2
    exact hs.squeeze tendsto_const_nhds (fun i => (hA i (x i + h)).1)
      (fun i => (hA i (x i + h)).2)
  exact ⟨magnetic_family_derivative_tendsto_zero hL dA dB bC hlim,
    magnetic_family_second_tendsto_zero hL hK dA dB dC bC bD hlim⟩

lemma magnetic_family_weighted_endpoint {ι : Type*} {l : Filter ι}
    {B C R : ι → ℝ} {K : ℝ}
    (hB : Tendsto B l (𝓝 0)) (hC : Tendsto C l (𝓝 0))
    (hR : ∀ i, |R i| ≤ K) :
    Tendsto (fun i => C i - B i * R i) l (𝓝 0) := by
  have hmul : Tendsto (fun i => B i * R i) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_)
      (show Tendsto (fun i => |B i| * K) l (𝓝 0) by
        simpa only [Real.norm_eq_abs, abs_zero, zero_mul] using hB.norm.mul_const K)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hR i) (abs_nonneg _)
  simpa only [sub_zero] using hC.sub hmul

end InvariantIsing

end

end OAI
