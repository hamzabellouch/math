import OAI.Analysis.HyperbolicCones.PencilRepresentation
import OAI.Analysis.HyperbolicCones.PencilSplit
import OAI.Analysis.HyperbolicCones.PencilRecovery
import OAI.Analysis.HyperbolicCones.PencilRegularization
import OAI.Analysis.HyperbolicCones.ConeInterior
import OAI.Analysis.HyperbolicCones.ConeZero

namespace OAI

noncomputable section

namespace Paper256

theorem pencil_normalization (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N)
    (hL : cone = {x | (L x : Mat N ℝ).PosSemidef}) : Nonempty NormalizedPencil := by
  obtain ⟨m, hm, C, hC, hrep⟩ := representation_compression_of_zero_slice cone L hL
    basePoint_mem_interior_cone cone_zero_slice
  obtain ⟨P⟩ := blockPencil_exists cone m hm C hC hrep cone_zero_slice
  exact P.normalized_exists cone_positive_slice

end Paper256

end

end OAI
