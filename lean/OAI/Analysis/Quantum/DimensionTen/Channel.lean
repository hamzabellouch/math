import OAI.InformationTheory.DimensionTen.ChoiTransfer
import OAI.Analysis.Quantum.PPTSquare.OrderedChannel

namespace OAI

/-! A trace-preserving PPT channel with an entangled square, from the dimension-ten pair. -/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

def phiOneLinear : ChannelCompletion.Map (Fin 10) (Fin 10) :=
  ∑ p : Fin 6 × Fin 6, ChannelCompletion.ad (phiOneKraus p)

@[simp] lemma phiOneLinear_apply (A : Mat 10) : phiOneLinear A = phiOne A := by
  rw [phiOne_kraus]
  simp only [phiOneLinear, LinearMap.sum_apply, ChannelCompletion.ad_apply, krausMap]

@[simp] lemma phiTwoLinear_apply (A : Mat 10) : phiTwoLinear A = phiTwo A := rfl

lemma phiOneLinear_cp : ChannelCompletion.CP phiOneLinear := by
  exact TensorCriterion.cp_sum _ (fun _ => ChannelCompletion.cp_ad _)

lemma phiTwoLinear_cp : ChannelCompletion.CP phiTwoLinear := by
  have h : phiTwoLinear =
      ∑ p : Fin 6 × Fin 6, ChannelCompletion.ad (phiTwoKraus p) := by
    ext A i j
    simp only [phiTwoLinear_apply, LinearMap.sum_apply, ChannelCompletion.ad_apply]
    rw [phiTwo_kraus]
    rfl
  rw [h]
  exact TensorCriterion.cp_sum _ (fun _ => ChannelCompletion.cp_ad _)

lemma phiOneLinear_ppt : ChannelCompletion.PPT phiOneLinear := by
  refine ⟨phiOneLinear_cp, ?_⟩
  have h : ChannelCompletion.transposeMap.comp phiOneLinear = phiOneLinear := by
    ext A i j
    change (phiOneLinear A)ᵀ i j = phiOneLinear A i j
    simp only [phiOneLinear_apply, phiOne_output_transpose]
  rw [h]
  exact phiOneLinear_cp

lemma phiTwoLinear_ppt : ChannelCompletion.PPT phiTwoLinear := by
  refine ⟨phiTwoLinear_cp, ?_⟩
  have h : ChannelCompletion.transposeMap.comp phiTwoLinear = phiTwoLinear := by
    ext A i j
    change (phiTwoLinear A)ᵀ i j = phiTwoLinear A i j
    simp only [phiTwoLinear_apply, phiTwo_output_transpose]
  rw [h]
  exact phiTwoLinear_cp

lemma linear_composite_choi :
    ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear) = compositeChoi := by
  ext i j
  simp only [ChannelCompletion.choi, LinearMap.comp_apply,
    phiOneLinear_apply, phiTwoLinear_apply, compositeChoi, choi, Function.comp_apply]

lemma linear_composite_not_separable :
    ¬ ChannelCompletion.Separable
      (ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear)) := by
  rw [linear_composite_choi]
  intro h
  obtain ⟨r, A, B, hA, hB, hsum⟩ := h
  exact compositeChoi_not_separable ⟨r, A, B, fun i => ⟨hA i, hB i⟩, hsum⟩

def channel : ChannelCompletion.Map (ChannelCompletion.Space 10)
    (ChannelCompletion.Space 10) :=
  ChannelCompletion.theta 10 phiOneLinear phiTwoLinear

def channel21 : ChannelCompletion.Map (Fin 21) (Fin 21) :=
  ChannelCompletion.rename ExplicitPencil.orderedCoordinates.symm channel

def PublishedChoi21 : Prop :=
  ChannelCompletion.EntanglementBreaking (channel.comp channel) →
    ChannelCompletion.Separable (ChannelCompletion.choi (channel.comp channel))

lemma channel_choi_corner :
    (ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10)ᴴ *
      ChannelCompletion.choi (channel.comp channel) *
        (ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10) =
    ((ChannelCompletion.coefficient phiOneLinear *
      ChannelCompletion.coefficient phiTwoLinear : ℝ) : ℂ) • compositeChoi := by
  rw [channel, ChannelCompletion.choi_corner, linear_composite_choi]

theorem main_channel_conditional (hsr : PublishedChoi21) :
    ChannelCompletion.PPT channel ∧ ChannelCompletion.TracePreserving channel ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel.comp channel) := by
  refine ⟨ChannelCompletion.theta_ppt 10 phiOneLinear_ppt phiTwoLinear_ppt,
    ChannelCompletion.theta_tracePreserving 10 phiOneLinear phiTwoLinear, ?_⟩
  intro hEB
  have hsep := ChannelCompletion.separable_coord_compress (hsr hEB)
    (ChannelCompletion.first 10) (ChannelCompletion.first 10)
  change ChannelCompletion.Separable
    ((ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10)ᴴ *
      ChannelCompletion.choi (channel.comp channel) *
        (ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10)) at hsep
  rw [channel_choi_corner] at hsep
  have hpos : 0 < ChannelCompletion.coefficient phiOneLinear *
      ChannelCompletion.coefficient phiTwoLinear :=
    mul_pos (ChannelCompletion.coefficient_pos phiOneLinear_cp)
      (ChannelCompletion.coefficient_pos phiTwoLinear_cp)
  apply linear_composite_not_separable
  rw [linear_composite_choi]
  exact ChannelCompletion.separable_of_smul hpos hsep

theorem main_channel_fin21_conditional (hsr : PublishedChoi21) :
    ChannelCompletion.PPT channel21 ∧ ChannelCompletion.TracePreserving channel21 ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel21.comp channel21) := by
  obtain ⟨hP, hT, hE⟩ := main_channel_conditional hsr
  refine ⟨ChannelCompletion.rename_ppt _ hP,
    ChannelCompletion.rename_tracePreserving _ hT, ?_⟩
  intro hEB
  unfold channel21 at hEB
  rw [ChannelCompletion.rename_comp] at hEB
  exact hE (ChannelCompletion.eb_of_rename _ (ChannelCompletion.cp_comp hP.1 hP.1) hEB)

end DimensionTen

noncomputable section

namespace DimensionTen

theorem publishedChoi21 : PublishedChoi21 := by
  intro hEB
  exact ChannelCompletion.eb_choi hEB

theorem main_channel :
    ChannelCompletion.PPT channel ∧ ChannelCompletion.TracePreserving channel ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel.comp channel) :=
  main_channel_conditional publishedChoi21

theorem main_channel_fin21 :
    ChannelCompletion.PPT channel21 ∧ ChannelCompletion.TracePreserving channel21 ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel21.comp channel21) :=
  main_channel_fin21_conditional publishedChoi21

theorem exists_channel_fin21 :
    ∃ Θ : ChannelCompletion.Map (Fin 21) (Fin 21),
      ChannelCompletion.PPT Θ ∧ ChannelCompletion.TracePreserving Θ ∧
        ¬ ChannelCompletion.EntanglementBreaking (Θ.comp Θ) :=
  ⟨channel21, main_channel_fin21⟩

end DimensionTen

end
end

end OAI
