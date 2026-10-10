import OAI.Analysis.CircleDomains.Uniformization.ConformalFiniteEmbedding
import OAI.Analysis.CircleDomains.Topology.JordanDiskImages
import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletionUniformization
import OAI.Analysis.CircleDomains.Topology.PlanarSchoenfliesProof

namespace OAI

/-! A compact Jordan hole lying in the domain of a conformal open embedding
has another actual Jordan hole as its image. -/
open Set Function
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_conformal_jordan_cap_image
    {f : Sphere → Sphere} {U : Set Sphere} (hf : IsConformalOn f U)
    (hU : IsOpen U) (hi : InjOn f U) (hinf : ∞ ∈ U) (hfix : f ∞=∞)
    (H : ℂ ≃ₜ ℂ) (hHU : closedTerminalCap H ⊆ U) :
    ∃ K : ℂ ≃ₜ ℂ, f '' closedTerminalCap H = closedTerminalCap K := by
  obtain ⟨hd,ho,hij⟩ := hf.finite_open_embedding hU hi hinf hfix
  have hsub : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' U :=
    fun z hz => hHU ⟨z,hz,rfl⟩
  obtain ⟨K,_hKi,hKc,_hKf⟩ := exists_jordan_image_disk planarSchoenflies
    (hU.preimage OnePoint.continuous_coe) hd.continuousOn ho hij H hsub
  refine ⟨K,?_⟩
  rw [closedTerminalCap, ← finite_part_sphere_image
    (fun z hz => finite_image_of_fixes_infty hi hinf hfix (hsub hz)), hKc]
  rfl

end CircleDomainRigidity

end

end OAI
