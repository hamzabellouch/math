import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralPatchNull

namespace OAI

/-! # Arbitrarily small neutral rectangles inside bounded root boxes -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] completeRootChain

theorem exists_small_neutral_rectangle (n : ℕ) (g : G n)
    (z₀ : NeutralCoordinateBase n × transverseNeutralSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
        (emptyRootPattern n) (completeRootChain_final n) g)
      (R : ℝ) (A : Set (NeutralCoordinateBase n)) (K : Set (transverseNeutralSpace n)),
      IsOpen A ∧ IsOpen K ∧ z₀ ∈ A ×ˢ K ∧
      B.time ⊆ (completeRootChain n).remainingWindow R 0 ∧
      (∀ z ∈ A ×ˢ K, neutralToPrefix n z ∈ B.domain) ∧
      ∀ z ∈ A ×ˢ K, ∀ w ∈ A ×ˢ K,
        (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n ε := by
  obtain ⟨B₀,hB₀⟩ := exists_rootPrefixBox_at_coordinates (neutralEmptyPrefix n)
    (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) g
    (neutralToPrefix n z₀)
  have hcover : (neutralToPrefix n z₀).2 ∈
      ⋃ m, (completeRootChain n).remainingWindow 1 m := by
    rw [(completeRootChain n).remainingWindow_cover]
    trivial
  obtain ⟨m,hm⟩ := mem_iUnion.mp hcover
  let B := B₀.shrink B₀.transverse
    (B₀.time ∩ (completeRootChain n).remainingWindow 1 m)
    B₀.transverse_open (B₀.time_open.inter ((completeRootChain n).remainingWindow_open 1 m))
    subset_rfl inter_subset_left
  have hzB : neutralToPrefix n z₀ ∈ B.domain := ⟨hB₀.1,hB₀.2,hm⟩
  let f := fun q : (NeutralCoordinateBase n × transverseNeutralSpace n) ×
      (NeutralCoordinateBase n × transverseNeutralSpace n) =>
    (neutralProductParam n q.1)⁻¹*neutralProductParam n q.2
  have hf : Continuous f :=
    (((neutralProductParam_isOpenEmbedding n).continuous.comp continuous_fst).inv).mul
      ((neutralProductParam_isOpenEmbedding n).continuous.comp continuous_snd)
  have hneigh : f ⁻¹' matrixBall n ε ∈ 𝓝 (z₀,z₀) := by
    apply (hf.isOpen_preimage _ (matrixBall_isOpen n ε)).mem_nhds
    change (neutralProductParam n z₀)⁻¹*neutralProductParam n z₀ ∈ matrixBall n ε
    rw [inv_mul_cancel]
    exact one_mem_matrixBall n hε
  obtain ⟨U,V,hU,hzU,hV,hzV,hUV⟩ := mem_nhds_prod_iff'.mp hneigh
  let W := (U ∩ V) ∩ (neutralToPrefix n) ⁻¹' B.domain
  have hW : IsOpen W := (hU.inter hV).inter
    ((B.transverse_open.prod B.time_open).preimage
      (neutralToPrefix_isOpenEmbedding n).continuous)
  have hzW : z₀ ∈ W := ⟨⟨hzU,hzV⟩,hzB⟩
  obtain ⟨A,K,hA,hzA,hK,hzK,hAK⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hzW)
  refine ⟨B,1+m,A,K,hA,hK,⟨hzA,hzK⟩,?_,?_,?_⟩
  · intro t ht
    simpa only [EliminationChain.remainingWindow,Nat.cast_zero,add_zero] using ht.2
  · intro z hz
    exact (hAK hz).2
  · intro z hz w hw
    change f (z,w) ∈ matrixBall n ε
    exact hUV ⟨(hAK hz).1.1,(hAK hw).1.2⟩

end DukePrimeDegree

end

end OAI
