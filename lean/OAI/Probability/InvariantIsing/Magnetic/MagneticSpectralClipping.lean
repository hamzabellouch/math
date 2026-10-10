import OAI.Probability.InvariantIsing.Spectral.SpectralClipping

namespace OAI

/-! Spectral clipping has the same uniform error for every external field. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical
namespace InvariantIsing

lemma spectral_clip_mean_field_pressure_close {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig : Fin N → ℝ)
    (a b η : ℝ) (hab : a ≤ b) (hη : 0 ≤ η)
    (heig : ∀ i, a-η ≤ eig i ∧ eig i ≤ b+η) (c : Fin N → ℝ) :
    |(∫ V, rotatedPressure (fun i => spectralClip a b (eig i))
      (matrixRotation V⁻¹) c ∂μ)-
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ| ≤ η/2 := by
  let K := (∑ i, |eig i|)+|a|+|b|
  have hsum : 0 ≤ ∑ i, |eig i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hi i : |eig i| ≤ K := by
    have hh := Finset.single_le_sum (fun i _ => abs_nonneg (eig i)) (Finset.mem_univ i)
    dsimp [K]
    linarith [abs_nonneg a,abs_nonneg b]
  have hc i : |spectralClip a b (eig i)| ≤ K := by
    have hh := spectralClip_mem hab (eig i)
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [hh.1,hh.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hd i := abs_le.mp (spectralClip_close hab hη (heig i))
  have hh := cavity_meanPressure_squeeze hN μ eig
    (fun i => spectralClip a b (eig i)) (fun i => spectralClip a b (eig i))
    c η K hi hc hc
    (fun i => by linarith [(hd i).2]) (fun i => by linarith [(hd i).1])
  rw [abs_le]
  constructor <;> linarith

end InvariantIsing

end

end OAI
