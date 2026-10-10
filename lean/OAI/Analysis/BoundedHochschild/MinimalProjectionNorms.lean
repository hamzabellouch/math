import OAI.Analysis.BoundedHochschild.CentralRowCompression
import OAI.Analysis.BoundedHochschild.NormalInfiniteAverages

namespace OAI

/-! Every projection corner retains the norm of right compression in a
minimal represented averaging family. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem minimal_family_projection_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (F : Set (NormalGNS e →WOT[ℂ] K))
    (hclosed : IsClosed F) (hconv : Convex ℝ F)
    (hinv : RepresentedRightAverageInvariant π (normalGNSRepresentation e) F)
    (hmin : ∀ G : Set (NormalGNS e →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
      Convex ℝ G → RepresentedRightAverageInvariant π (normalGNSRepresentation e) G → F ⊆ G)
    (W : NormalGNS e →WOT[ℂ] K) (hW : W ∈ F) {p : M} (hp : IsStarProjection p) :
    ‖W.toCLM.comp (normalGNSRepresentation e p)‖ =
      ‖(π p).comp (W.toCLM.comp (normalGNSRepresentation e p))‖ := by
  let σ := normalGNSRepresentation e
  obtain ⟨z, hz⟩ := exists_central_support e hp
  obtain ⟨S, hS, ho, ht⟩ := exists_central_support_row e hp hz
  obtain ⟨hm, hlim⟩ := centralSupportRow_normalized e hz.1.1 S
    (fun v hv => (hS v hv).2) ho ht
  let U := ContinuousLinearMapWOT.ofCLM
    (infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm W.toCLM)
  have hU : U ∈ F := infinite_represented_average_mem_family π σ F hclosed hinv W hW
    (centralSupportRow z S) hm (normalGNS_row_limit e _ hlim)
  have hzcomm (a : M) : (σ z).comp (σ a) = (σ a).comp (σ z) := by
    change σ z * σ a = σ a * σ z
    rw [← map_mul, ← map_mul, (hz.1.2 a).eq]
  have hn := compressed_norm_eq_on_minimal_family π σ F hclosed hconv hinv hmin
    (1 : K →L[ℂ] K) (σ z) (fun _ => by ext; simp) hzcomm hW hU
  have hn' : ‖W.toCLM.comp (σ z)‖ = ‖U.toCLM.comp (σ z)‖ := by
    have hcomp (A : NormalGNS e →L[ℂ] K) : (1 : K →L[ℂ] K).comp A = A := by
      ext ξ
      rfl
    simpa only [weakCompression, ContinuousLinearMapWOT.toCLM_comp,
      ContinuousLinearMapWOT.toCLM_ofCLM, hcomp] using hn
  have hle : ‖W.toCLM.comp (σ z)‖ ≤ ‖(π p).comp (W.toCLM.comp (σ p))‖ := by
    rw [hn']
    exact centralSupportRow_compression_norm_le π σ hp hz.1.1 hz.2.1 S hS hm W.toCLM
  have hpp : ‖(π p).comp (W.toCLM.comp (σ p))‖ ≤ ‖W.toCLM.comp (σ p)‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((hp.map π).norm_le _))
  have hpz : (σ z).comp (σ p) = σ p := by
    change σ z * σ p = σ p
    rw [← map_mul, (hp.le_iff_mul_eq_right hz.1.1).mp hz.2.1]
  have hpz' : W.toCLM.comp (σ p) = (W.toCLM.comp (σ z)).comp (σ p) := by
    rw [ContinuousLinearMap.comp_assoc, hpz]
  have hpc : ‖W.toCLM.comp (σ p)‖ ≤ ‖W.toCLM.comp (σ z)‖ := by
    rw [hpz']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) ((hp.map σ).norm_le _))
  exact le_antisymm (hpc.trans hle) hpp

end BoundedHochschild.KadisonRingrose

end

end OAI
