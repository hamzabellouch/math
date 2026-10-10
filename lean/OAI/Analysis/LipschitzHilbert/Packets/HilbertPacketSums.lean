import OAI.Analysis.LipschitzHilbert.Fourier.HilbertAnnularVariation
import OAI.Analysis.LipschitzHilbert.Packets.VariationPacketL1

namespace OAI

/-! Actual Hilbert packet sums are continuous and agree with the generic
partial sums used for spatial oscillation estimates. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem partialBandSum_continuous {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (n : ℕ) :
    Continuous (partialBandSum f n) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using (f j).continuous
  · simpa only [ite_eq_right hj] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem hilbertPartialBandSum_continuous {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) :
    Continuous (hilbertPartialBandSum f n) := by
  exact (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
    (continuous_pi (fun k => partialBandSum_continuous (fun j => f j k) n))

theorem hilbertPartialBandSum_eq_packetPartialSum {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum f n x =
      packetPartialSum (fun j => WithLp.toLp 2 (fun k => f j k x)) n := by
  ext k
  change (∑ j : Fin N, if j.val < n then f j k x else 0) = _
  simp only [packetPartialSum, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

end LipschitzHilbert

end

end OAI
