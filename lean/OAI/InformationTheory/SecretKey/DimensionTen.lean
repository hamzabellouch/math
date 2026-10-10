import OAI.InformationTheory.SecretKey.Main
import OAI.InformationTheory.SecretKey.ChoiTransferProof
import OAI.Analysis.Quantum.DimensionTen.Channel
import OAI.InformationTheory.SecretKey.DimensionTenModel

namespace OAI

/-! Key separation for the dimension-ten state in the finite terminal-readout model. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder

namespace ZeroKey.TenDimensional

universe u

lemma rho_density : Density rho := DimensionTen.rho_density

lemma trace_ne_zero : trace DimensionTen.compositeChoi ≠ 0 :=
  DimensionTen.compositeChoi_trace_ne

lemma rho_not_separable : ¬ Separable rho := DimensionTen.rho_entangled

lemma rho_productfree :
    ∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      rho *ᵥ w = DimensionTen.productVector u v → u = 0 ∨ v = 0 :=
  DimensionTen.rho_productfree

def TransferInput : Prop :=
  ChoiTransfer.PublishedTransfer DimensionTen.phiOneLinear DimensionTen.phiTwoLinear

def PPTInput : Prop :=
  ChoiTransfer.PublishedPPT DimensionTen.phiOneLinear DimensionTen.phiTwoLinear

lemma rho_inClass_conditional (hppt : PPTInput) (htransfer : TransferInput) :
    InClass rho := by
  have h := ChoiTransfer.normalized_inClass_conditional
    DimensionTen.phiOneLinear DimensionTen.phiTwoLinear hppt htransfer
  rw [DimensionTen.linear_composite_choi] at h
  exact h DimensionTen.compositeChoi_posSemidef DimensionTen.compositeChoi_ne

theorem main_state_conditional (hppt : PPTInput) (htransfer : TransferInput) :
    MainClaim.{u} := by
  have hc := rho_inClass_conditional hppt htransfer
  exact ⟨rho_density, rho_not_separable, rho_productfree,
    class_distillableSecretKey_zero rho rho_density hc,
    class_uniformProtocolGap rho rho_density hc,
    class_uniformCompletedGap rho rho_density hc⟩

end ZeroKey.TenDimensional

noncomputable section

namespace ZeroKey.TenDimensional

universe u

theorem pptInput : PPTInput :=
  ChoiTransfer.publishedPPT DimensionTen.phiOneLinear_ppt DimensionTen.phiTwoLinear_ppt

theorem transferInput : TransferInput :=
  ChoiTransfer.publishedTransfer DimensionTen.phiOneLinear DimensionTen.phiTwoLinear
    DimensionTen.phiOneLinear_cp

theorem rho_inClass : InClass rho :=
  rho_inClass_conditional pptInput transferInput

theorem main_state : MainClaim.{u} :=
  main_state_conditional pptInput transferInput

end ZeroKey.TenDimensional

end
end

end OAI
