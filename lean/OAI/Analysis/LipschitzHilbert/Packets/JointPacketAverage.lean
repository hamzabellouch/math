import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! A finite collection of translated packet lattices is averaged as
one form. The finite-form estimate is applied before integration, so no
factor for the number of length/direction labels is introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem joint_packet_average_bound {ι : Type*} [Fintype ι]
    (μ : ι → Measure (ℝ×ℝ)) [∀ i, IsProbabilityMeasure (μ i)]
    (value : ι → (ℝ×ℝ) → ℂ)
    (hvalue : ∀ i, Integrable (value i) (μ i))
    (term : ι → (ℝ×ℝ) → (ℤ×ℤ) → ℂ)
    (hseries : ∀ i, ∀ᵐ z ∂μ i,
      Summable (fun n => ‖term i z n‖) ∧ (∑' n, term i z n) = value i z)
    (C : ℝ)
    (hfinite : ∀ z : ι → (ℝ×ℝ), ∀ S : Finset (ι×(ℤ×ℤ)),
      ‖∑ p ∈ S, term p.1 (z p.1) p.2‖ ≤ C) :
    ‖∑ i, ∫ z, value i z ∂μ i‖ ≤ C := by
  classical
  have hjoint : ∀ᵐ z : ι → (ℝ×ℝ) ∂Measure.pi μ, ∀ i,
      Summable (fun n => ‖term i (z i) n‖) ∧
        (∑' n, term i (z i) n) = value i (z i) := by
    apply ae_all_iff.mpr
    intro i
    have hi := hseries i
    rw [← (measurePreserving_eval μ i).map_eq] at hi
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  have hbound : ∀ᵐ z : ι → (ℝ×ℝ) ∂Measure.pi μ,
      ‖∑ i, value i (z i)‖ ≤ C := by
    filter_upwards [hjoint] with z hz
    have hn : Summable (fun p : ι×(ℤ×ℤ) => ‖term p.1 (z p.1) p.2‖) :=
      (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
        ⟨fun i => (hz i).1, (hasSum_fintype _).summable⟩
    have hs : Summable (fun p : ι×(ℤ×ℤ) => term p.1 (z p.1) p.2) := hn.of_norm
    have heq : (∑' p : ι×(ℤ×ℤ), term p.1 (z p.1) p.2) =
        ∑ i, value i (z i) := hs.tsum_prod.trans (by
      rw [tsum_fintype]
      exact Finset.sum_congr rfl (fun i _ => (hz i).2))
    rw [← heq]
    exact le_of_tendsto hs.hasSum.norm (Eventually.of_forall (hfinite z))
  have heq : (∫ z : ι → (ℝ×ℝ), ∑ i, value i (z i) ∂Measure.pi μ) =
      ∑ i, ∫ z, value i z ∂μ i := by
    rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (hvalue i))]
    exact Finset.sum_congr rfl (fun i _ => integral_comp_eval (hvalue i).aestronglyMeasurable)
  rw [← heq]
  simpa using norm_integral_le_of_norm_le_const hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
