import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.UniformBetaPacking

namespace OAI

/-!
# Total mass of bad-beta descendants

Bad-beta descendants are the support-cell descendants whose enlarged-ball
bilateral beta number exceeds the threshold. Taking the supremum over finite
subsets upgrades the uniform finite Carleson estimate to their full `ENNReal`
mass sum, with the constant still chosen before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def BadBetaDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (H ε : ℝ) :=
  {i : SupportCellDescendant μ R hR k z // ε ≤ bilateralBeta n μ i.center (H * i.radius)}

theorem exists_uniform_bad_beta_total_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : BadBetaDescendant (p + 1) μ R hR k z H ε,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  classical
  obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_beta_carleson_constant hnd C G H ε D hC hG hH hε
  refine ⟨K, hK, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let emb : BadBetaDescendant (p + 1) μ R hR k z H ε ↪ SupportCellDescendant μ R hR k z :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hs : ∀ i ∈ s.map emb, ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have hb := hpack μ hg hlower hRiesz R hR k z hcore (s.map emb) hs
  simpa only [Finset.sum_map] using! hb

end

end RieszRectifiability

end OAI
