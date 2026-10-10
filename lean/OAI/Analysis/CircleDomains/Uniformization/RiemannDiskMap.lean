import OAI.Analysis.CircleDomains.Uniformization.RiemannDiskExtremal
import OAI.Analysis.CircleDomains.Uniformization.RiemannDiskImprovement

namespace OAI

/-! The disk map needed for a single circularization step, constructed
from derivative maximization and the omitted-value root improvement. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma exists_normalized_riemann_disk_map {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧
      BijOn f U (ball 0 1) ∧ deriv f a ≠ 0 := by
  obtain ⟨f,hf,hdf,hmax⟩ := exists_extremal_normalized_disk_embedding hU
    hc.isPathConnected.isConnected ha (exists_normalized_disk_embedding hU hc hproper ha)
  refine ⟨f,hf,⟨hf.mapsTo,hf.injective,?_⟩,hdf⟩
  intro b hb
  by_contra hmiss
  obtain ⟨g,hg,hgain⟩ := improve_disk_embedding_of_omitted_value hU hc ha hf hdf
    (mem_ball_zero_iff.mp hb) hmiss
  exact (not_lt_of_ge (hmax g hg)) hgain

end CircleDomainRigidity

end

end OAI
