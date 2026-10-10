import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinatePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunctionEnergyTransport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! C1 functions on the hyperbolic upper half-space, used only to
transport the actual gradients through the finite Hecke correspondence. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPointFunction (F : C(CubicThetaPoint,ℂ)) (y : ℂ × ℝ) : ℂ :=
  F (cubicThetaPointInclusion.symm y)

lemma cubicThetaPointFunction_apply (F : C(CubicThetaPoint,ℂ))
    {y : ℂ × ℝ} (hy : 0<y.2) : cubicThetaPointFunction F y=F ⟨y,hy⟩ := by
  apply congrArg F
  apply Subtype.ext
  have hy' : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  exact cubicThetaPointInclusion.right_inv hy'

def cubicThetaPointC1 : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ContDiffOn ℝ 1 (cubicThetaPointFunction F) {y : ℂ × ℝ | 0<y.2}}
  zero_mem' := contDiffOn_const
  add_mem' := fun hF hG => hF.add hG
  smul_mem' := fun c _ hF => hF.const_smul c

lemma cubicThetaPointC1_differentiable (F : cubicThetaPointC1)
    {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaPointFunction F.val) y :=
  (F.property.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt
    (by norm_num)

def cubicThetaPointC1Gradient (x : CubicThetaPoint) : cubicThetaPointC1 →ₗ[ℂ] CubicThetaGradient where
  toFun F := (x.val.2:ℂ) • cubicThetaTangentValues (fderiv ℝ (cubicThetaPointFunction F.val) x.val)
  map_add' F G := by
    change (x.val.2:ℂ) • cubicThetaTangentValues
      (fderiv ℝ (cubicThetaPointFunction F.val+cubicThetaPointFunction G.val) x.val)=_
    rw [fderiv_add (cubicThetaPointC1_differentiable F x.property)
      (cubicThetaPointC1_differentiable G x.property),map_add,smul_add]
  map_smul' c F := by
    change (x.val.2:ℂ) • cubicThetaTangentValues
      (fderiv ℝ (c • cubicThetaPointFunction F.val) x.val)=_
    rw [fderiv_const_smul (cubicThetaPointC1_differentiable F x.property),map_smul]
    exact smul_comm _ _ _

lemma cubicThetaPointC1Gradient_norm_sq (F : cubicThetaPointC1) (x : CubicThetaPoint) :
    ‖cubicThetaPointC1Gradient x F‖^2=
      x.val.2^2*cubicThetaFunctionEnergy (cubicThetaPointFunction F.val) x.val := by
  change ‖(x.val.2:ℂ) • cubicThetaTangentValues
    (fderiv ℝ (cubicThetaPointFunction F.val) x.val)‖^2=_
  rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

def cubicThetaPointC1Pullback (g : SL(2,ℂ)) : cubicThetaPointC1 →ₗ[ℂ] cubicThetaPointC1 where
  toFun F := ⟨⟨fun x => F.val (g • x),F.val.continuous.comp (continuous_const_smul g)⟩,by
    have hm : ContDiffOn ℝ 1 (cubicThetaMobius g) {y : ℂ × ℝ | 0<y.2} :=
      fun y hy => ((cubicThetaMobius_contDiffAt g hy).of_le (by simp)).contDiffWithinAt
    apply (F.property.comp hm (fun y hy => cubicThetaMobius_height_pos g hy)).congr
    intro y hy
    rw [cubicThetaPointFunction_apply _ hy]
    change F.val (⟨cubicThetaMobius g y,cubicThetaMobius_height_pos g hy⟩:CubicThetaPoint)=
      cubicThetaPointFunction F.val (cubicThetaMobius g y)
    exact (cubicThetaPointFunction_apply F.val (cubicThetaMobius_height_pos g hy)).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cubicThetaPointC1Pullback_function (g : SL(2,ℂ)) (F : cubicThetaPointC1)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPointFunction (cubicThetaPointC1Pullback g F).val y=
      cubicThetaPointFunction F.val (cubicThetaMobius g y) := by
  rw [cubicThetaPointFunction_apply _ hy,
    cubicThetaPointFunction_apply _ (cubicThetaMobius_height_pos g hy)]
  rfl

lemma cubicThetaPointC1Pullback_gradient_norm (g : SL(2,ℂ))
    (F : cubicThetaPointC1) (x : CubicThetaPoint) :
    ‖cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback g F)‖=
      ‖cubicThetaPointC1Gradient (g • x) F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPointC1Gradient_norm_sq,cubicThetaPointC1Gradient_norm_sq]
  have he : cubicThetaPointFunction (cubicThetaPointC1Pullback g F).val=ᶠ[𝓝 x.val]
      (fun y => cubicThetaPointFunction F.val (cubicThetaMobius g y)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    exact cubicThetaPointC1Pullback_function g F hy
  have hder := he.fderiv_eq (𝕜:=ℝ)
  change x.val.2^2*cubicThetaFunctionEnergy _ x.val=
    (cubicThetaMobius g x.val).2^2*cubicThetaFunctionEnergy _ (cubicThetaMobius g x.val)
  unfold cubicThetaFunctionEnergy
  rw [hder]
  exact cubicThetaFunctionEnergy_mobius _ g x.property
    (cubicThetaPointC1_differentiable F (cubicThetaMobius_height_pos g x.property))

theorem cubicThetaPointC1Pullback_gradient_pair (g : SL(2,ℂ))
    (F G : cubicThetaPointC1) (x : CubicThetaPoint) :
    inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback g F))
      (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback g G))=
    inner ℂ (cubicThetaPointC1Gradient (g • x) F) (cubicThetaPointC1Gradient (g • x) G) := by
  let : AddCommGroup cubicThetaPointC1 := Module.addCommMonoidToAddCommGroup ℂ
  let L : cubicThetaPointC1 →ₗ[ℂ] CubicThetaGradient :=
    (cubicThetaPointC1Gradient x).comp (cubicThetaPointC1Pullback g)
  let M : cubicThetaPointC1 →ₗ[ℂ] CubicThetaGradient := cubicThetaPointC1Gradient (g • x)
  have hn (F : cubicThetaPointC1) : ‖L F‖=‖M F‖ :=
    cubicThetaPointC1Pullback_gradient_norm g F x
  change inner ℂ (L F) (L G)=inner ℂ (M F) (M G)
  exact cubicThetaLinear_inner_of_norm_eq L M hn F G

end CubicFirstMoment

end

end OAI
