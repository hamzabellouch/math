import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergyClosure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1GradientLinear

namespace OAI

/-! Actual C1 sections of finite value and gradient energy form a
complex vector space. This retains their literal pointwise functions. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaFiniteEnergySections : Submodule ℂ CubicThetaSection where
  carrier := {F | ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2} ∧
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure ∧
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure}
  zero_mem' := ⟨(0 : cubicThetaSmoothTests).property.1.of_le (by simp),
    cubicThetaSectionRepresentative_memLp (0 : cubicThetaSmoothTests),
    cubicThetaGradientRepresentative_memLp (0 : cubicThetaSmoothTests)⟩
  add_mem' := by
    intro F G hF hG
    refine ⟨hF.1.add hG.1,hF.2.1.add hG.2.1,?_⟩
    have he : cubicThetaGradientRepresentative (F+G)=
        cubicThetaGradientRepresentative F+cubicThetaGradientRepresentative G := by
      funext q
      exact cubicThetaC1Gradient_add F G hF.1 hG.1 _
    rw [he]
    exact hF.2.2.add hG.2.2
  smul_mem' := by
    intro c F hF
    refine ⟨hF.1.const_smul c,hF.2.1.const_smul c,?_⟩
    have he : cubicThetaGradientRepresentative (c • F)=c • cubicThetaGradientRepresentative F := by
      funext q
      exact cubicThetaC1Gradient_smul c F hF.1 _
    rw [he]
    exact hF.2.2.const_smul c

def cubicThetaFiniteEnergyValue : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun F := F.property.2.1.toLp _
  map_add' F G := MemLp.toLp_add F.property.2.1 G.property.2.1
  map_smul' c F := MemLp.toLp_const_smul c F.property.2.1

def cubicThetaFiniteEnergyGradient : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaGradientL2 where
  toFun F := F.property.2.2.toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(F+G).property.2.2.coeFn_toLp,F.property.2.2.coeFn_toLp,
      G.property.2.2.coeFn_toLp,Lp.coeFn_add (F.property.2.2.toLp _) (G.property.2.2.toLp _)]
      with q hFG hF hG ha
    simp only [Pi.add_apply] at ha
    rw [hFG,ha,hF,hG]
    exact cubicThetaC1Gradient_add F G F.property.1 G.property.1 _
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(c • F).property.2.2.coeFn_toLp,F.property.2.2.coeFn_toLp,
      Lp.coeFn_smul c (F.property.2.2.toLp _)] with q hCF hF ha
    simp only [Pi.smul_apply,RingHom.id_apply] at ha ⊢
    rw [hCF,ha,hF]
    exact cubicThetaC1Gradient_smul c F F.property.1 _

def cubicThetaFiniteEnergyEmbedding : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  (((WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).symm.toLinearMap).comp
    (cubicThetaFiniteEnergyValue.prod cubicThetaFiniteEnergyGradient)).codRestrict
      cubicThetaGlobalEnergySpace (fun F => cubicThetaFiniteEnergy_mem_graph F F.property.1
        F.property.2.1 F.property.2.2)

lemma cubicThetaFiniteEnergyEmbedding_value (F : cubicThetaFiniteEnergySections) :
    cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F)=cubicThetaFiniteEnergyValue F := rfl

lemma cubicThetaFiniteEnergyEmbedding_gradient (F : cubicThetaFiniteEnergySections) :
    cubicThetaGlobalEnergyGradient (cubicThetaFiniteEnergyEmbedding F)=cubicThetaFiniteEnergyGradient F := rfl

lemma cubicThetaSmoothTests_finiteEnergy : cubicThetaSmoothTests≤cubicThetaFiniteEnergySections := by
  intro F hF
  let G : cubicThetaSmoothTests := ⟨F,hF⟩
  exact ⟨hF.1.of_le (by simp),cubicThetaSectionRepresentative_memLp G,cubicThetaGradientRepresentative_memLp G⟩

def cubicThetaSmoothToFiniteEnergy : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaFiniteEnergySections :=
  Submodule.inclusion cubicThetaSmoothTests_finiteEnergy

lemma cubicThetaFiniteEnergyEmbedding_smooth (F : cubicThetaSmoothTests) :
    cubicThetaFiniteEnergyEmbedding (cubicThetaSmoothToFiniteEnergy F)=cubicThetaGlobalEnergyTest F := rfl

end CubicFirstMoment

end

end OAI
