import Mathlib
import OAI.Geometry.CubicTorus.Regularity.TranslateNormal

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeQuadratic_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    volumeQuadratic (l.smulRight v)=0 := by
  have hc : (l.smulRight v).comp (l.smulRight v)=l v • l.smulRight v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      map_smul,smul_apply]
    module
  simp only [volumeQuadratic,hc,coverTrace_smulRight,coverTrace_smul]
  ring

lemma normal_jet_acceleration_step (D L M K : Cover →L[ℝ] Cover) (n : Cover)
    (hM : cofactorQuadratic M n=0) :
    cofactorLinear D n+cofactorQuadratic L n+
        2 • (cofactorLinear K n+cofactorLinear M (cofactorLinear L n))=
      cofactorLinear (D+2 • (K+M.comp L)) n+cofactorQuadratic (L+M) n := by
  rw [cofactorQuadratic_add,hM]
  simp only [two_smul,cofactorLinear_add]
  module

lemma mass_jet_acceleration_step (D L M K : Cover →L[ℝ] Cover)
    (hM : volumeQuadratic M=0) :
    coverTrace D+volumeQuadratic L+2*(coverTrace K+coverTrace L*coverTrace M)=
      coverTrace (D+2 • (K+M.comp L))+volumeQuadratic (L+M) := by
  rw [volumeQuadratic_add,hM]
  simp only [two_smul,coverTrace_add]
  ring

lemma divergence_smooth {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  exact coverTraceCLM.contDiff.comp hd

lemma divergence_derivative {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x v : Cover) : fderiv ℝ (divergence F) x v=coverTrace (fderiv ℝ (fderiv ℝ F) x v) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  have he := (coverTraceCLM.hasFDerivAt.comp x (hd.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ coverTraceCLM (fderiv ℝ F y)) x v=_
  simp only [Function.comp_def] at he
  rw [he]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def chainAcceleration (l : List Variation) (x : Cover) : Cover := (motionJet l x).2

lemma chainAcceleration_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞) (chainAcceleration l) :=
  (motionJet_smooth l).snd

lemma chainAcceleration_periodic (l : List Variation) (m : Fin 3 → ℤ) (x : Cover) :
    chainAcceleration l (x+latticeVector m)=chainAcceleration l x := by
  simp only [chainAcceleration,motionJet_periodic]

lemma chainAcceleration_append (l : List Variation) (a : Variation) :
    chainAcceleration (l++[a])=fun x ↦ chainAcceleration l x+
      2 • fderiv ℝ (variationField a) x (chainVelocity l x) := by
  funext x
  simp only [chainAcceleration,motionJet_append,motionJet_first]

lemma chainAcceleration_derivative_append (l : List Variation) (a : Variation) (x : Cover) :
    fderiv ℝ (chainAcceleration (l++[a])) x=fderiv ℝ (chainAcceleration l) x+
      2 • (fderiv ℝ (fderiv ℝ (variationField a)) x (chainVelocity l x)+
        (fderiv ℝ (variationField a) x).comp (fderiv ℝ (chainVelocity l) x)) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (variationField a)) :=
    (variationField_smooth a).fderiv_right (by simp)
  have ht := hd.clm_apply (chainVelocity_smooth l)
  have h2 : fderiv ℝ (fun y ↦ 2 • fderiv ℝ (variationField a) y (chainVelocity l y)) x=
      2 • fderiv ℝ (fun y ↦ fderiv ℝ (variationField a) y (chainVelocity l y)) x := by
    simp only [two_smul]
    exact fderiv_fun_add (ht.differentiable (by simp) x) (ht.differentiable (by simp) x)
  rw [chainAcceleration_append,fderiv_fun_add
    ((chainAcceleration_smooth l).differentiable (by simp) x)
    ((ht.const_smul 2).differentiable (by simp) x),
    h2,
    derivative_transport (chainVelocity_smooth l) (variationField_smooth a)]

lemma variation_normal_derivative (a : Variation) (x n u v : Cover) :
    fderiv ℝ (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2)
      (x,n) (u,v)=cofactorLinear (fderiv ℝ (fderiv ℝ (variationField a)) x u) n+
        cofactorLinear (fderiv ℝ (variationField a) x) v := by
  have he : (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2)=
      (fun p : Cover×Cover ↦ cofactorLinear (fderiv ℝ (variationField a) p.1) p.2) := by
    funext p
    exact (cofactorLinear_coordinate (a.smooth.differentiable (by simp) p.1) a.coordinate p.2).symm
  rw [he,cofactor_field_derivative (variationField_smooth a)]

lemma variation_cofactor_quadratic (a : Variation) (x n : Cover) :
    cofactorQuadratic (fderiv ℝ (variationField a) x) n=0 := by
  unfold variationField
  rw [fderiv_smul_const (a.smooth.differentiable (by simp) x)]
  exact cofactorQuadratic_smulRight _ _ _

theorem normalJet_second (l : List Variation) (x n : Cover) :
    (normalJet l x n).2.2=cofactorLinear (fderiv ℝ (chainAcceleration l) x) n+
      cofactorQuadratic (fderiv ℝ (chainVelocity l) x) n := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=cofactorLinear (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x) n+
      cofactorQuadratic (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x) n
    simp [cofactorLinear,cofactorQuadratic]
  | append_singleton l a ih =>
    rw [normalJet_append]
    dsimp only
    rw [ih,(normalJet_first l x n).1,(normalJet_first l x n).2,
      variation_normal_derivative,chainNormalVelocity_eq_cofactor,
      chainAcceleration_derivative_append,chainVelocity_append,
      fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
        ((variationField_smooth a).differentiable (by simp) x)]
    exact normal_jet_acceleration_step _ _ _ _ _ (variation_cofactor_quadratic a x n)

lemma componentDivergence_eq (a : Variation) : componentDivergence a=divergence (variationField a) := by
  funext x
  exact (divergence_smul_const (a.smooth.differentiable (by simp) x) _).symm

lemma variation_volume_quadratic (a : Variation) (x : Cover) :
    volumeQuadratic (fderiv ℝ (variationField a) x)=0 := by
  unfold variationField
  rw [fderiv_smul_const (a.smooth.differentiable (by simp) x)]
  exact volumeQuadratic_smulRight _ _

lemma massJet_divergence (l : List Variation) (x : Cover) :
    (massJet l x).2.1=coverTrace (fderiv ℝ (chainVelocity l) x) := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=coverTrace (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x)
    simp
  | append_singleton l a ih =>
    rw [massJet_append]
    dsimp only
    rw [ih,componentDivergence_eq,chainVelocity_append,
      fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
        ((variationField_smooth a).differentiable (by simp) x),coverTrace_add]
    rfl

theorem massJet_second (l : List Variation) (x : Cover) :
    (massJet l x).2.2=coverTrace (fderiv ℝ (chainAcceleration l) x)+
      volumeQuadratic (fderiv ℝ (chainVelocity l) x) := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=coverTrace (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x)+
      volumeQuadratic (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x)
    simp [volumeQuadratic]
  | append_singleton l a ih =>
    rw [massJet_append]
    dsimp only
    rw [ih,massJet_first,massJet_divergence,componentDivergence_eq,
      divergence_derivative (variationField_smooth a),divergence_eq_coverTrace,
      chainAcceleration_derivative_append,chainVelocity_append,
      fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
        ((variationField_smooth a).differentiable (by simp) x)]
    exact mass_jet_acceleration_step _ _ _ _ (variation_volume_quadratic a x)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def ambientAreaQuadratic (L : Cover →L[ℝ] Cover) (n : Cover) : ℝ :=
  ‖cofactorLinear L n‖^2-⟪n,cofactorLinear L n⟫^2+⟪n,cofactorQuadratic L n⟫

def ambientQuadratic (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (F : Cover → Cover) : ℝ :=
  (∫ z,ambientAreaQuadratic (fderiv ℝ F z.1) z.2 ∂(μ : Measure NormalBundle))-
    H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,volumeQuadratic (fderiv ℝ F x))

lemma volumeQuadratic_continuous : Continuous volumeQuadratic := by
  exact (coverTraceCLM.continuous.pow 2).sub
    (coverTraceCLM.continuous.comp (continuous_id.clm_comp continuous_id))

lemma cofactorQuadratic_continuous :
    Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ cofactorQuadratic p.1 p.2) := by
  have ht : Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ coverTrace p.1) :=
    coverTraceCLM.continuous.comp continuous_fst
  have ha : Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ p.1.adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp continuous_fst
  exact (((volumeQuadratic_continuous.comp continuous_fst).smul continuous_snd).sub
    ((continuous_const.mul ht).smul (ha.clm_apply continuous_snd))).add
      ((ha.clm_apply (ha.clm_apply continuous_snd)).const_smul 2)

lemma ambientAreaQuadratic_continuous :
    Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ ambientAreaQuadratic p.1 p.2) := by
  have hc : Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ cofactorLinear p.1 p.2) :=
    (cofactorOperator.continuous.comp continuous_fst).clm_apply continuous_snd
  exact ((hc.norm.pow 2).sub ((continuous_snd.inner hc).pow 2)).add
    (continuous_snd.inner cofactorQuadratic_continuous)

lemma ambientAreaQuadratic_integrable (μ : FiniteMeasure NormalBundle)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Integrable (fun z : NormalBundle ↦ ambientAreaQuadratic (fderiv ℝ F z.1) z.2)
      (μ : Measure NormalBundle) := by
  exact (ambientAreaQuadratic_continuous.comp
    (((hF.continuous_fderiv (by simp)).comp normalEmbedding_continuous.fst).prodMk
      continuous_normalUnit)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma cube_integrable_continuous (E : Set Torus) {f : Cover → ℝ} (hf : Continuous f) :
    IntegrableOn f (fundamentalCube∩quotientMap ⁻¹' E) :=
  integrable_of_continuous_compact_carrier isCompact_closedFundamentalCube
    (cubeIntersection_compact_carrier E) hf

lemma periodic_normal_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x := by
  obtain ⟨C,_,hb⟩ := periodic_bounded hF.continuous hp
  have hc : 0<C+‖F 0‖+1 := by linarith [hb 0,norm_nonneg (F 0)]
  exact normalMeasure_flux hμ hF hp hc
    (fun x ↦ (hb x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma chainQuadratic_eq_ambient {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (l : List Variation) :
    chainQuadratic E μ H l=ambientQuadratic E μ H (chainVelocity l) := by
  have ha := ambientAreaQuadratic_integrable μ (chainVelocity_smooth l)
  have hb : Integrable (fun z : NormalBundle ↦
      tangentialDivergence (chainAcceleration l) z.1 z.2) (μ : Measure NormalBundle) :=
    (continuous_tangentialDivergence (chainAcceleration_smooth l)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc := cube_integrable_continuous E
    (continuous_divergence (chainAcceleration_smooth l))
  have hd := cube_integrable_continuous E
    (volumeQuadratic_continuous.comp ((chainVelocity_smooth l).continuous_fderiv (by simp)))
  change IntegrableOn (fun x ↦ volumeQuadratic (fderiv ℝ (chainVelocity l) x))
    (fundamentalCube∩quotientMap ⁻¹' E) at hd
  have hn : (fun z : NormalBundle ↦
      ‖chainNormalVelocity l z.1 z.2‖^2-⟪(z.2 : Cover),chainNormalVelocity l z.1 z.2⟫^2+
      ⟪(z.2 : Cover),(normalJet l z.1 z.2).2.2⟫)=
      (fun z : NormalBundle ↦ ambientAreaQuadratic (fderiv ℝ (chainVelocity l) z.1) z.2+
        tangentialDivergence (chainAcceleration l) z.1 z.2) := by
    funext z
    rw [normalJet_second,chainNormalVelocity_eq_cofactor,inner_add_right,
      cofactorLinear_inner (fderiv ℝ (chainAcceleration l) z.1) z.2.property]
    unfold ambientAreaQuadratic tangentialDivergence
    rw [divergence_eq_coverTrace]
    ring
  have hv : (fun x ↦ (massJet l x).2.2)=
      (fun x ↦ divergence (chainAcceleration l) x+
        volumeQuadratic (fderiv ℝ (chainVelocity l) x)) := by
    funext x
    exact massJet_second l x
  have hh := hH (chainAcceleration l) (chainAcceleration_smooth l) (chainAcceleration_periodic l)
  rw [periodic_normal_flux hμ (chainAcceleration_smooth l) (chainAcceleration_periodic l)] at hh
  unfold chainQuadratic ambientQuadratic
  rw [hn,hv,integral_add ha hb,integral_add hc hd,hh]
  ring

theorem isMinimizerAt_ambient_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=0 →
        0≤ambientQuadratic E μ H F := by
  obtain ⟨μ,H,hμ,hH,_,hs⟩ := isMinimizerAt_expanded_stability hV hE hmin
  refine ⟨μ,H,hμ,hH,?_⟩
  intro F hf hp hz
  obtain ⟨l,hl,_,hq⟩ := hs F hf hp hz
  rw [chainQuadratic_eq_ambient hμ hH l,show chainVelocity l=F from funext hl] at hq
  exact hq

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def volumeCorrection (F : Cover → Cover) (x : Cover) : Cover :=
  divergence F x • F x-fderiv ℝ F x (F x)

lemma volumeCorrection_smooth {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (volumeCorrection F) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  exact ((divergence_smooth hF).smul hF).sub (hd.clm_apply hF)

lemma volumeCorrection_periodic {F : Cover → Cover}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (m : Fin 3 → ℤ) (x : Cover) :
    volumeCorrection F (x+latticeVector m)=volumeCorrection F x := by
  simp only [volumeCorrection,divergence_eq_coverTrace,fderiv_periodic hp,hp]

lemma divergence_volumeCorrection {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (volumeCorrection F) x=volumeQuadratic (fderiv ℝ F x) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hdiv := divergence_smooth hF
  have he := ((hdiv.differentiable (by simp) x).hasFDerivAt.smul
    (hF.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ divergence F y • F y) x = _ at he
  unfold volumeCorrection
  rw [divergence_eq_coverTrace,fderiv_fun_sub (f := fun y ↦ divergence F y • F y)
    ((hdiv.smul hF).differentiable (by simp) x)
    ((hd.clm_apply hF).differentiable (by simp) x),he,derivative_transport hF hF]
  change coverTraceCLM (_-_) = _
  rw [map_sub]
  simp only [coverTraceCLM_apply,coverTrace_add,coverTrace_smulRight,coverTrace_smul,
    divergence_derivative hF,volumeQuadratic,divergence_eq_coverTrace]
  ring

lemma volumeQuadratic_boundary {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,volumeQuadratic (fderiv ℝ F x))=
      ∫ z,⟪(z.2 : Cover),volumeCorrection F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [periodic_normal_flux hμ (volumeCorrection_smooth hF) (volumeCorrection_periodic hp)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ (divergence_volumeCorrection hF x).symm))

def ambientBoundaryQuadratic (H : ℝ) (F : Cover → Cover) (x n : Cover) : ℝ :=
  ambientAreaQuadratic (fderiv ℝ F x) n-H*⟪n,volumeCorrection F x⟫

lemma ambientQuadratic_boundary {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (H : ℝ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ambientQuadratic E μ H F=
      ∫ z,ambientBoundaryQuadratic H F z.1 z.2 ∂(μ : Measure NormalBundle) := by
  have hv : Integrable (fun z : NormalBundle ↦
      H*⟪(z.2 : Cover),volumeCorrection F z.1⟫) (μ : Measure NormalBundle) :=
    (continuous_const.mul (continuous_normalUnit.inner
      ((volumeCorrection_smooth hF).continuous.comp normalEmbedding_continuous.fst))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [ambientQuadratic,volumeQuadratic_boundary hμ hF hp]
  simp only [ambientBoundaryQuadratic]
  rw [integral_sub (ambientAreaQuadratic_integrable μ hF) hv,integral_const_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_boundary_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=0 →
        0≤∫ z,ambientBoundaryQuadratic H F z.1 z.2 ∂(μ : Measure NormalBundle) := by
  obtain ⟨μ,H,hμ,hH,hs⟩ := isMinimizerAt_ambient_stability hV hE hmin
  refine ⟨μ,H,hμ,hH,?_⟩
  intro F hf hp hz
  rw [← ambientQuadratic_boundary hμ H hf hp]
  exact hs F hf hp hz

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma adjoint_smulRight_unit (l : Cover →L[ℝ] ℝ) {n : Cover} (hn : ‖n‖=1) :
    (l.smulRight n).adjoint n=l.adjoint 1 := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,
    ContinuousLinearMap.adjoint_inner_left]
  simp

lemma inner_adjoint_one (l : Cover →L[ℝ] ℝ) (v : Cover) :
    ⟪l.adjoint 1,v⟫=l v := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

lemma coverTrace_normal_square (D : Cover →L[ℝ] Cover) (l : Cover →L[ℝ] ℝ)
    (n : Cover) (c : ℝ) :
    coverTrace ((c • D+l.smulRight n).comp (c • D+l.smulRight n))=
      c^2*coverTrace (D.comp D)+2*c*l (D n)+(l n)^2 := by
  have h1 : (l.smulRight n).comp D=(l.comp D).smulRight n := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have h2 : (l.smulRight n).comp (l.smulRight n)=l n • l.smulRight n := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      map_smul,smul_apply]
    module
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,coverTrace_add,
    coverTrace_smul,coverTrace_comp_comm D (l.smulRight n),h1,h2,
    coverTrace_smulRight,ContinuousLinearMap.comp_apply]
  ring

lemma ambientAreaQuadratic_formula (L : Cover →L[ℝ] Cover) {n : Cover} (hn : ‖n‖=1) :
    ambientAreaQuadratic L n=‖L.adjoint n‖^2-⟪n,L.adjoint n⟫^2+
      (coverTrace L)^2-coverTrace (L.comp L)-
      2*coverTrace L*⟪n,L.adjoint n⟫+2*⟪L n,L.adjoint n⟫ := by
  unfold ambientAreaQuadratic cofactorLinear cofactorQuadratic
  rw [norm_sub_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,sq_abs,hn,one_pow,mul_one,
    inner_add_right,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,ContinuousLinearMap.adjoint_inner_right]
  simp only [map_smul,real_inner_smul_left,two_smul,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

theorem normal_hessian_algebra (D : Cover →L[ℝ] Cover) (l : Cover →L[ℝ] ℝ)
    {n : Cover} (hn : ‖n‖=1) (hD : D.adjoint n=0) (c : ℝ) :
    ambientAreaQuadratic (c • D+l.smulRight n) n-
      coverTrace D*⟪n,coverTrace (c • D+l.smulRight n) • (c • n)-
        (c • D+l.smulRight n) (c • n)⟫=
      ‖l.adjoint 1‖^2-(l n)^2-c^2*coverTrace (D.comp D) := by
  have hd : ⟪n,D n⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hD,inner_zero_left]
  have ha : (c • D+l.smulRight n).adjoint n=l.adjoint 1 := by
    simp only [map_add,map_smul,add_apply,smul_apply,hD,smul_zero,zero_add]
    exact adjoint_smulRight_unit l hn
  have hi : ⟪n,l.adjoint 1⟫=l n := by rw [real_inner_comm,inner_adjoint_one]
  rw [ambientAreaQuadratic_formula _ hn,ha,hi,coverTrace_normal_square]
  simp only [coverTrace_add,coverTrace_smul,coverTrace_smulRight,
    add_apply,smul_apply,map_smul,
    ContinuousLinearMap.smulRight_apply,inner_add_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    hn,one_pow,mul_one]
  have hig : ⟪D n,l.adjoint 1⟫=l (D n) :=
    (real_inner_comm _ _).trans (inner_adjoint_one l (D n))
  simp only [hig,hi,inner_add_right,real_inner_smul_right,hd,mul_zero,zero_add,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_unit_normal_derivative {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hu : ∀ᶠ y in 𝓝 x, ‖N y‖=1) :
    (fderiv ℝ N x).adjoint (N x)=0 := by
  have he : (fun y ↦ ⟪N y,N y⟫)=ᶠ[𝓝 x](fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hu] with y hy
    rw [real_inner_self_eq_norm_sq,hy,one_pow]
  have hh := (hN.hasFDerivAt.inner ℝ hN.hasFDerivAt).fderiv
  have hz := he.fderiv_eq (𝕜 := ℝ)
  rw [hh] at hz
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : Cover →L[ℝ] ℝ ↦ L v) hz
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,fderiv_const_apply,zero_apply] at hv
  rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
  rw [real_inner_comm (fderiv ℝ N x v) (N x)] at hv
  nlinarith [real_inner_comm (N x) (fderiv ℝ N x v)]

lemma adjoint_fderiv_one (f : Cover → ℝ) (x : Cover) :
    (fderiv ℝ f x).adjoint 1=gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_adjoint_one,inner_gradient_left]

theorem normal_variation_hessian {N : Cover → Cover} {f : Cover → ℝ} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hf : DifferentiableAt ℝ f x)
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) {H : ℝ} (hH : divergence N x=H) :
    ambientBoundaryQuadratic H (fun y ↦ f y • N y) x (N x)=
      ‖gradient f x‖^2-⟪N x,gradient f x⟫^2-
        (f x)^2*coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)) := by
  have hd := (hf.hasFDerivAt.smul hN.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ f y • N y) x=_ at hd
  have hn : ‖N x‖=1 := hu.self_of_nhds
  have hg : fderiv ℝ f x (N x)=⟪N x,gradient f x⟫ := by
    rw [real_inner_comm,inner_gradient_left]
  unfold ambientBoundaryQuadratic volumeCorrection
  simp only [divergence_eq_coverTrace,hd]
  rw [← hH,divergence_eq_coverTrace,
    normal_hessian_algebra _ _ hn (smooth_unit_normal_derivative hN hu),
    adjoint_fderiv_one,hg]

lemma surface_gradient_norm {n : Cover} (hn : ‖n‖=1) (v : Cover) :
    ‖v-⟪n,v⟫ • n‖^2=‖v‖^2-⟪n,v⟫^2 := by
  rw [norm_sub_sq_real]
  simp only [real_inner_smul_right,norm_smul,Real.norm_eq_abs,hn,mul_one,sq_abs]
  rw [real_inner_comm v n]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalExtensionJacobi (μ : FiniteMeasure NormalBundle) (f : Cover → ℝ)
    (N : Cover → Cover) : ℝ :=
  ∫ z,‖gradient f z.1-⟪(z.2 : Cover),gradient f z.1⟫ • (z.2 : Cover)‖^2-
    (f z.1)^2*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)

lemma ambientBoundaryQuadratic_zero_of_notMem_tsupport {F : Cover → Cover}
    {x : Cover} (hx : x∉tsupport F) (H : ℝ) (n : Cover) :
    ambientBoundaryQuadratic H F x n=0 := by
  have hf : F x=0 := image_eq_zero_of_notMem_tsupport hx
  have hd : fderiv ℝ F x=0 := fderiv_of_notMem_tsupport ℝ hx
  simp [ambientBoundaryQuadratic,ambientAreaQuadratic,volumeCorrection,
    divergence_eq_coverTrace,hd,hf,cofactorLinear,cofactorQuadratic]

lemma boundaryQuadratic_eq_normalExtension {μ : FiniteMeasure NormalBundle} {H : ℝ}
    {f : Cover → ℝ} {N : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hgeom : ∀ᵐ z ∂(μ : Measure NormalBundle), z.1∈tsupport f →
      N z.1=(z.2 : Cover) ∧ (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H) :
    (∫ z,ambientBoundaryQuadratic H (fun y ↦ f y • N y) z.1 z.2 ∂(μ : Measure NormalBundle))=
      normalExtensionJacobi μ f N := by
  apply integral_congr_ae
  filter_upwards [hgeom] with z hz
  by_cases hx : (z.1 : Cover)∈tsupport f
  · obtain ⟨hn,hu,hh⟩ := hz hx
    rw [← hn,normal_variation_hessian (hN.differentiable (by simp) _) (hf.differentiable (by simp) _) hu hh,
      surface_gradient_norm (hu.self_of_nhds)]
  · have hF : (z.1 : Cover)∉tsupport (fun y ↦ f y • N y) :=
      fun h ↦ hx (tsupport_smul_subset_left f N h)
    rw [ambientBoundaryQuadratic_zero_of_notMem_tsupport hF,
      image_eq_zero_of_notMem_tsupport hx]
    have hg : gradient f z.1=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
    simp only [hg,inner_zero_right,zero_smul,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),zero_mul]

namespace Periodic

theorem isMinimizerAt_normal_extension_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      ∀ (f : Cover → ℝ) (N : Cover → Cover),
        ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) N →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∀ m x,N (x+latticeVector m)=N x) →
        (∀ᵐ z ∂(μ : Measure NormalBundle),z.1∈tsupport f →
          N z.1=(z.2 : Cover) ∧ (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,hμ,_,hs⟩ := isMinimizerAt_boundary_stability hV hE hmin
  refine ⟨μ,H,hμ,?_⟩
  intro f N hf hN hfp hNp hgeom hz
  have hp : ∀ m x,(fun y ↦ f y • N y) (x+latticeVector m)=f x • N x := by
    intro m x
    change f (x+latticeVector m) • N (x+latticeVector m)=_
    rw [hfp,hNp]
  have hflux : (∫ z,⟪(z.2 : Cover),f z.1 • N z.1⟫ ∂(μ : Measure NormalBundle))=0 := by
    rw [← hz]
    apply integral_congr_ae
    filter_upwards [hgeom] with z hg
    by_cases hx : (z.1 : Cover)∈tsupport f
    · rw [(hg hx).1,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_smul,inner_zero_right]
  rw [← boundaryQuadratic_eq_normalExtension hf hN hgeom]
  exact hs _ (hf.smul hN) hp hflux

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_contDiff_top {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  exact coverTraceCLM.contDiff.comp (hF.fderiv_right (by simp))

lemma tangentialDivergence_scalar_normal {N : Cover → Cover} {f : Cover → ℝ} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hf : DifferentiableAt ℝ f x)
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    tangentialDivergence (fun y ↦ f y • N y) x (N x)=f x*divergence N x := by
  have hd := (hf.hasFDerivAt.smul hN.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ f y • N y) x = _ at hd
  have hn := hu.self_of_nhds
  have hzero : ⟪N x,fderiv ℝ N x (N x)⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,smooth_unit_normal_derivative hN hu,inner_zero_left]
  unfold tangentialDivergence
  simp only [divergence_eq_coverTrace,hd,coverTrace_add,coverTrace_smul,
    coverTrace_smulRight,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,inner_add_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,hzero,mul_zero,mul_one]
  ring

theorem weakCMC_normal_extension {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H := by
  let f : Cover → ℝ := fun x ↦ divergence N x-H
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (divergence_contDiff_top hN).sub contDiff_const
  have hfp : ∀ m x,f (x+latticeVector m)=f x := by
    intro m x
    simp only [f,divergence_periodic hp]
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • N x) := hf.smul hN
  have hFp : ∀ m x,(fun y ↦ f y • N y) (x+latticeVector m)=f x • N x := by
    intro m x
    change f (x+latticeVector m) • N (x+latticeVector m)=_
    rw [hfp,hp]
  have h := hCMC _ hF hFp
  have hl : (∫ z,tangentialDivergence (fun x ↦ f x • N x) z.1 z.2 ∂(μ : Measure NormalBundle))=
      ∫ z,f z.1*divergence N z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    rw [← hz.1,tangentialDivergence_scalar_normal
      (hN.differentiable (by simp) _) (hf.differentiable (by simp) _) hz.2]
  have hr : (∫ z,⟪(z.2 : Cover),f z.1 • N z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ z,f z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    rw [hz.1,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
  rw [hl,hr] at h
  have hfc : Continuous (fun z : NormalBundle ↦ f z.1) := hf.continuous.comp
    (continuous_subtype_val.comp continuous_fst)
  have hdc : Continuous (fun z : NormalBundle ↦ divergence N z.1) :=
    (continuous_divergence hN).comp (continuous_subtype_val.comp continuous_fst)
  have hi : Integrable (fun z : NormalBundle ↦ f z.1*divergence N z.1) (μ : Measure NormalBundle) :=
    (hfc.mul hdc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun z : NormalBundle ↦ H*f z.1) (μ : Measure NormalBundle) :=
    (hfc.const_mul H).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : (∫ z,(f z.1)^2 ∂(μ : Measure NormalBundle))=0 := by
    have he : (fun z : NormalBundle ↦ (f z.1)^2)=
        (fun z ↦ f z.1*divergence N z.1-H*f z.1) := by
      funext z
      dsimp [f]
      ring
    rw [he,integral_sub hi hi',integral_const_mul,h,sub_self]
  have his : Integrable (fun z : NormalBundle ↦ (f z.1)^2) (μ : Measure NormalBundle) :=
    (hfc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z : NormalBundle ↦ sq_nonneg (f z.1))) his).mp hs
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_normal_CMC_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      ∀ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N →
        (∀ m x,N (x+latticeVector m)=N x) →
        (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
          (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) →
        (∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H) ∧
        ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
          (∀ m x,f (x+latticeVector m)=f x) →
          (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
          0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,hμ,hCMC,hs⟩ := isMinimizerAt_boundary_stability hV hE hmin
  refine ⟨μ,H,hμ,?_⟩
  intro N hN hp hn
  have hH := weakCMC_normal_extension hCMC hN hp hn
  refine ⟨hH,?_⟩
  intro f hf hfp hz
  have hgeom : ∀ᵐ z ∂(μ : Measure NormalBundle),z.1∈tsupport f →
      N z.1=(z.2 : Cover) ∧ (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H := by
    filter_upwards [hn,hH] with z hz he
    exact fun _ ↦ ⟨hz.1,hz.2,he⟩
  rw [← boundaryQuadratic_eq_normalExtension hf hN hgeom]
  apply hs _ (hf.smul hN)
  · intro m x
    change f (x+latticeVector m) • N (x+latticeVector m)=f x • N x
    rw [hfp,hp]
  · rw [← hz]
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    change ⟪(z.2 : Cover),f z.1 • N z.1⟫=f z.1
    rw [hz.1,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def regularizedNormal (R : Cover → Cover) (x : Cover) : Cover :=
  (Real.sqrt (‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))))⁻¹ • R x

lemma regularizedNormal_denom_pos (v : Cover) :
    0<‖v‖^2+(1-Real.smoothTransition (4*‖v‖^2)) := by
  by_cases h : v=0
  · simp [h]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma regularizedNormal_contDiff {R : Cover → Cover}
    (hR : ContDiff ℝ (⊤ : ℕ∞) R) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedNormal R) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ‖R x‖^2) := hR.norm_sq ℝ
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ ‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))) :=
    hq.add (contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul hq)))
  exact ((hd.sqrt (fun x ↦ (regularizedNormal_denom_pos _).ne')).inv
    (fun x ↦ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)).ne')).smul hR

lemma regularizedNormal_eq {R : Cover → Cover} {x : Cover} (h : (1/4 : ℝ)≤‖R x‖^2) :
    regularizedNormal R x=‖R x‖⁻¹ • R x := by
  unfold regularizedNormal
  rw [Real.smoothTransition.one_of_one_le (by linarith),sub_self,add_zero,
    Real.sqrt_sq (norm_nonneg _)]

lemma regularizedNormal_unit_near {R : Cover → Cover} (hR : Continuous R) {x : Cover}
    (hx : (1/4 : ℝ)<‖R x‖^2) :
    ∀ᶠ y in 𝓝 x,‖regularizedNormal R y‖=1 := by
  have hnear : ∀ᶠ y in 𝓝 x,(1/4 : ℝ)<‖R y‖^2 :=
    (hR.norm.pow 2).continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [hnear] with y hy
  have hn : 0<‖R y‖ := lt_of_not_ge fun h ↦ by
    have hz := le_antisymm h (norm_nonneg _)
    rw [hz] at hy
    norm_num at hy
  rw [regularizedNormal_eq hy.le,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
    inv_mul_cancel₀ hn.ne']

lemma regularizedNormal_periodic {R : Cover → Cover}
    (hR : ∀ m x,R (x+latticeVector m)=R x) :
    ∀ m x,regularizedNormal R (x+latticeVector m)=regularizedNormal R x := by
  intro m x
  simp only [regularizedNormal,hR]

theorem finite_normal_patch_gluing {ι : Type*} [Fintype ι]
    {μ : FiniteMeasure NormalBundle} (φ : ι → Cover → ℝ) (N : ι → Cover → Cover)
    (hφ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (φ i))
    (hN : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (N i))
    (hφp : ∀ i m x,φ i (x+latticeVector m)=φ i x)
    (hNp : ∀ i m x,N i (x+latticeVector m)=N i x)
    (hφn : ∀ i x,0≤φ i x)
    (hcover : ∀ᵐ z ∂(μ : Measure NormalBundle),∃ i,φ i z.1=1)
    (hpatch : ∀ i,∀ᵐ z ∂(μ : Measure NormalBundle),0<φ i z.1 → N i z.1=(z.2 : Cover)) :
    ∃ R : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) R ∧
      (∀ m x,R (x+latticeVector m)=R x) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),R z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖R y‖=1) := by
  classical
  let A : Cover → Cover := fun x ↦ ∑ i,φ i x • N i x
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := ContDiff.sum fun i _ ↦ (hφ i).smul (hN i)
  refine ⟨regularizedNormal A,regularizedNormal_contDiff hA,?_,?_⟩
  · apply regularizedNormal_periodic
    intro m x
    simp only [A,hφp,hNp]
  · have hall := (ae_all_iff (μ := (μ : Measure NormalBundle))).mpr hpatch
    filter_upwards [hcover,hall] with z hz hn
    let w : ℝ := ∑ i,φ i z.1
    have hw : 1≤w := by
      obtain ⟨i,hi⟩ := hz
      rw [← hi]
      exact Finset.single_le_sum (fun j _ ↦ hφn j _) (Finset.mem_univ i)
    have he : A z.1=w • (z.2 : Cover) := by
      dsimp only [A,w]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0<φ i z.1
      · rw [hn i h]
      · rw [le_antisymm (le_of_not_gt h) (hφn i _),zero_smul,zero_smul]
    have hnorm : ‖A z.1‖=w := by
      rw [he,norm_smul,Real.norm_of_nonneg (by linarith),z.2.property,mul_one]
    have hs : (1/4 : ℝ)<‖A z.1‖^2 := by rw [hnorm]; nlinarith
    refine ⟨?_,regularizedNormal_unit_near hA.continuous hs⟩
    rw [regularizedNormal_eq hs.le,hnorm,he,smul_smul,inv_mul_cancel₀ (by linarith : w≠0),one_smul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
