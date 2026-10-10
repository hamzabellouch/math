import OAI.Probability.SLE.Multipoint.MultipointKernelExpansion
import OAI.Probability.SLE.Multipoint.MultipointTupleNull
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

/-! Integrable two-point kernels have vanishing mass near the diagonal.
Finite cutoff sums with bounded overlap inherit this decay. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped ENNReal Topology

namespace SLEExactGauge.Multipoint

def nearDiagonalKernel (α b r : ℝ) (z : Fin 2 → ℂ) : ℝ≥0∞ :=
  if dist (z 0) (z 1) ≤ r then cappedDistanceKernel α b z else 0

lemma nearDiagonalKernel_measurable (α b r : ℝ) : Measurable (nearDiagonalKernel α b r) :=
  (measurable_cappedDistanceKernel α b).ite
    (measurableSet_le ((measurable_pi_apply 0).dist (measurable_pi_apply 1)) measurable_const)
    measurable_const

theorem nearDiagonalKernel_integral_tendsto_zero {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (b : ℝ) (K : Set ℂ) (hK : Bornology.IsBounded K)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z : Fin 2 → ℂ, nearDiagonalKernel α b (r n) z
      ∂Measure.pi (fun _ : Fin 2 => volume.restrict K)) atTop (𝓝 0) := by
  have hh := tendsto_lintegral_of_dominated_convergence
    (μ := Measure.pi (fun _ : Fin 2 => volume.restrict K))
    (F := fun n => nearDiagonalKernel α b (r n)) (f := fun _ => 0)
    (cappedDistanceKernel α b) (fun n => nearDiagonalKernel_measurable α b (r n))
    (fun n => Eventually.of_forall (fun z => by
      unfold nearDiagonalKernel
      split_ifs <;> simp only [le_refl,zero_le]))
    (cappedDistanceKernel_integral_lt_top hα hα1 b K hK).ne ?_
  · simpa only [lintegral_zero] using hh
  filter_upwards [ae_tuple_pair_ne K (0 : Fin 2) 1 (by decide)] with z hz
  have hdist : 0 < dist (z 0) (z 1) := dist_pos.mpr hz
  have he : ∀ᶠ n in atTop, nearDiagonalKernel α b (r n) z = 0 := by
    filter_upwards [(tendsto_order.mp hr).2 _ hdist] with n hn
    exact ite_eq_right (not_le.mpr hn)
  exact tendsto_const_nhds.congr' (he.mono (fun _ hn => hn.symm))

lemma sum_weighted_pair_kernel_le {ι : Type*} (I : Finset ι)
    (f : ι → ℂ → ℝ≥0∞) (hf : ∀ i ∈ I, Measurable (f i))
    (α b r : ℝ) (N : ℝ≥0∞)
    (hcover : ∀ x y, (∑ i ∈ I, f i x * f i y) ≤ if dist x y ≤ r then N else 0)
    (K : Set ℂ) :
    (∑ i ∈ I, ∫⁻ z : Fin 2 → ℂ, (∏ j, f i (z j)) * cappedDistanceKernel α b z
      ∂Measure.pi (fun _ : Fin 2 => volume.restrict K)) ≤
      N * ∫⁻ z : Fin 2 → ℂ, nearDiagonalKernel α b r z
        ∂Measure.pi (fun _ : Fin 2 => volume.restrict K) := by
  rw [← lintegral_finsetSum I (f := fun i z => (∏ j : Fin 2, f i (z j)) * cappedDistanceKernel α b z)
    (fun i hi => (Finset.measurable_prod _ (fun j _ => (hf i hi).comp (measurable_pi_apply j))).mul
      (measurable_cappedDistanceKernel α b))]
  rw [← lintegral_const_mul _ (nearDiagonalKernel_measurable α b r)]
  apply lintegral_mono
  intro z
  simp only [Fin.prod_univ_two]
  rw [← Finset.sum_mul]
  apply (mul_le_mul' (hcover (z 0) (z 1)) le_rfl).trans_eq
  unfold nearDiagonalKernel
  split_ifs <;> simp only [zero_mul,mul_zero]

end SLEExactGauge.Multipoint

end

end OAI
