import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricTensor

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff Topology
open Set Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance christoffelDualNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance christoffelMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := V)) :=
  ContinuousLinearMap.toNormedSpace
local instance christoffelMetricDerivativeNormedAddCommGroup :
    NormedAddCommGroup (MetricDerivative (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelMetricDerivativeNormedSpace :
    NormedSpace ℝ (MetricDerivative (V := V)) := ContinuousLinearMap.toNormedSpace

local instance christoffelEndomorphismNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelEndomorphismNormedSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
local instance christoffelBilinearNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelBilinearNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

def christoffelCLM : MetricDerivative (V := V) →L[ℝ] (V →L[ℝ] V →L[ℝ] V) :=
  LinearMap.toContinuousLinearMap
    { toFun := christoffel
      map_add' := by
        intro G H
        ext u v
        apply ext_inner_right ℝ
        intro w
        simp only [christoffel_apply, christoffelValue_inner, add_apply,
          inner_add_left]
        ring
      map_smul' := by
        intro c G
        ext u v
        apply ext_inner_right ℝ
        intro w
        simp only [christoffel_apply, christoffelValue_inner, smul_apply,
          real_inner_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }

@[simp] lemma christoffelCLM_apply (G : MetricDerivative (V := V)) :
    christoffelCLM G = christoffel G := rfl

lemma christoffel_contDiff : ContDiff ℝ ∞ (christoffel (V := V)) :=
  by
    convert! (christoffelCLM (V := V)).contDiff using 1

def jointJet (G : V → MetricDerivative (V := V)) (pz : V × V) : V :=
  coordinateJet (G pz.1) pz.2

lemma jointJet_contDiff (G : V → MetricDerivative (V := V)) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (jointJet G) := by
  exact contDiff_snd.sub (((christoffel_contDiff.comp (hG.comp contDiff_fst)).clm_apply
    contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

lemma jointJet_hasFDerivAt (G : V → MetricDerivative (V := V))
    (hG : ContDiff ℝ ∞ G) (p : V) :
    HasFDerivAt (jointJet G) (ContinuousLinearMap.snd ℝ V V) (p,0) := by
  have hC := (christoffel_contDiff.comp (hG.comp contDiff_fst)).differentiable
    (by simp) (p, (0 : V))
  have hz := hasFDerivAt_snd (𝕜 := ℝ) (p := (p, (0 : V)))
  have h := hz.sub ((hC.hasFDerivAt.clm_apply hz |>.clm_apply hz).const_smul (1/2 : ℝ))
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp

def centeredMap (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (pz : V × V) : V × V :=
  (pz.1, pz.1 + B pz.1 (jointJet G pz))

lemma centeredMap_contDiff (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (centeredMap B G) := by
  exact contDiff_fst.prodMk (contDiff_fst.add
    ((hB.comp contDiff_fst).clm_apply (jointJet_contDiff G hG)))

lemma centeredMap_hasFDerivAt (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G) (p : V) :
    HasFDerivAt (centeredMap B G)
      ((ContinuousLinearMap.fst ℝ V V).prod
        (ContinuousLinearMap.fst ℝ V V + (B p).comp (ContinuousLinearMap.snd ℝ V V))) (p,0) := by
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (p, (0 : V)))).prodMk
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (p, (0 : V)))).add
      (((hB.comp contDiff_fst).differentiable (by simp) (p, (0 : V))).hasFDerivAt.clm_apply
        (jointJet_hasFDerivAt G hG p)))
  convert! h using 1
  ext u <;> simp [jointJet]

def centeredDerivative (B : V ≃L[ℝ] V) : (V × V) ≃L[ℝ] (V × V) :=
  (ContinuousLinearEquiv.refl ℝ V).skewProd B (ContinuousLinearMap.id ℝ V)

lemma centeredMap_hasStrictFDerivAt (B : V → V →L[ℝ] V)
    (G : V → MetricDerivative (V := V)) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    HasStrictFDerivAt (centeredMap B G) (centeredDerivative Bp).toContinuousLinearMap (p,0) := by
  have hs := ((centeredMap_contDiff B G hB hG).contDiffAt (x := (p, (0 : V)))).hasStrictFDerivAt (by simp)
  rw [(centeredMap_hasFDerivAt B G hB hG p).fderiv] at hs
  convert! hs using 1
  ext u <;> simp [centeredDerivative, ContinuousLinearEquiv.skewProd, hBp, add_comm]

def centeredChart (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    OpenPartialHomeomorph (V × V) (V × V) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (centeredMap B G)
    (centeredMap_hasStrictFDerivAt B G hB hG p Bp hBp)

lemma centeredChart_mem_source (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    (p,0) ∈ (centeredChart B G hB hG p Bp hBp).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (centeredMap_hasStrictFDerivAt B G hB hG p Bp hBp)

lemma centeredChart_mem_target (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    (p,p) ∈ (centeredChart B G hB hG p Bp hBp).target := by
  have h := (centeredChart B G hB hG p Bp hBp).map_source
    (centeredChart_mem_source B G hB hG p Bp hBp)
  simpa [centeredChart, HasStrictFDerivAt.toOpenPartialHomeomorph_coe,
    centeredMap, jointJet] using h

lemma centeredChart_symm_center (B : V → V →L[ℝ] V)
    (G : V → MetricDerivative (V := V)) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    (centeredChart B G hB hG p Bp hBp).symm (p,p) = (p,0) := by
  have hh := (centeredChart B G hB hG p Bp hBp).left_inv
    (centeredChart_mem_source B G hB hG p Bp hBp)
  simpa only [centeredChart,HasStrictFDerivAt.toOpenPartialHomeomorph_coe,
    centeredMap,jointJet,coordinateJet_zero,map_zero,add_zero] using hh

lemma centeredChart_symm_contDiffAt (B : V → V →L[ℝ] V)
    (G : V → MetricDerivative (V := V)) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (p : V) (Bp : V ≃L[ℝ] V) (hBp : B p = Bp) :
    ContDiffAt ℝ ∞ (centeredChart B G hB hG p Bp hBp).symm (p,p) := by
  apply (centeredChart B G hB hG p Bp hBp).contDiffAt_symm
    (f₀' := centeredDerivative Bp) (centeredChart_mem_target B G hB hG p Bp hBp)
  · rw [centeredChart_symm_center]
    exact (centeredMap_hasStrictFDerivAt B G hB hG p Bp hBp).hasFDerivAt
  · rw [centeredChart_symm_center]
    exact (centeredMap_contDiff B G hB hG).contDiffAt

end TamingCompatibility.GeometricHilbert.NormalJets


end

end OAI
