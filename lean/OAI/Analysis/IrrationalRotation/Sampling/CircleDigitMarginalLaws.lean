import OAI.Analysis.IrrationalRotation.Rotation.CircleMarginalBudget
import OAI.Analysis.IrrationalRotation.Rotation.CircleMarginalDensity

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleParameterData

theorem digitMarginalLaws {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : DigitMarginalLaws p hr := by
  refine ⟨Real.exp_pos _, fun j ε => ?_⟩
  obtain ⟨hs, hC⟩ := hp.circle_marginal_budget j
  have hs' : Summable (fun i : ℕ => if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
    simpa only [tag] using hs
  have hC' : (∑' i : ℕ, if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) ≤
      50 * ((∑' s : ℕ, kappa s ^ 2) + 1) := by
    simpa only [tag] using hC
  have h := hybrid_density_of_coordinate_budget hp j hr ε hs' hC'
  have he : 50 * ((∑' s : ℕ, kappa s ^ 2) + 1) / 2 =
      25 * ((∑' s : ℕ, kappa s ^ 2) + 1) := by ring
  simpa only [marginalBound, he] using h

theorem exists_digitMarginalLaws {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i, DigitMarginalLaws p hr :=
  ⟨MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible,
    digitMarginalLaws hp _⟩

theorem endpoint_density {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∃ H : Circle → ℝ, MemLp H 2 volume ∧ (0 ≤ᵐ[volume] H) ∧
      (∫ x, H x) = 1 ∧ eLpNorm H 2 volume ≤ ENNReal.ofReal marginalBound ∧
      (law p j).map (point p hr side) =
        volume.withDensity (fun x => ENNReal.ofReal (H x)) := by
  simpa only [hybridPoint_const] using (digitMarginalLaws hp hr).2 j (fun _ => side)

end Invariant233.CircleCoupling

end

end OAI
