import Mathlib

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

abbrev MetricTensor := V →L[ℝ] V →L[ℝ] ℝ
abbrev MetricDerivative := V →L[ℝ] MetricTensor (V := V)

def christoffelValue (G : MetricDerivative (V := V)) (u v : V) : V :=
  (InnerProductSpace.toDual ℝ V).symm
    ((1/2 : ℝ) • (G u v + G v u - (G.flip u).flip v))

lemma christoffelValue_inner (G : MetricDerivative (V := V)) (u v w : V) :
    ⟪christoffelValue G u v,w⟫ = (G u v w + G v u w - G w u v)/2 := by
  simp only [christoffelValue, InnerProductSpace.toDual_symm_apply,
    smul_apply, sub_apply,
    add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

lemma christoffelValue_add_left (G : MetricDerivative (V := V)) (x y z : V) :
    christoffelValue G (x+y) z = christoffelValue G x z + christoffelValue G y z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, inner_add_left, map_add,
    add_apply]
  ring

lemma christoffelValue_smul_left (G : MetricDerivative (V := V)) (c : ℝ) (x z : V) :
    christoffelValue G (c • x) z = c • christoffelValue G x z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, real_inner_smul_left, map_smul,
    smul_apply, smul_eq_mul]
  ring

lemma christoffelValue_add_right (G : MetricDerivative (V := V)) (x y z : V) :
    christoffelValue G x (y+z) = christoffelValue G x y + christoffelValue G x z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, inner_add_left, map_add,
    add_apply]
  ring

lemma christoffelValue_smul_right (G : MetricDerivative (V := V)) (c : ℝ) (x z : V) :
    christoffelValue G x (c • z) = c • christoffelValue G x z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, real_inner_smul_left, map_smul,
    smul_apply, smul_eq_mul]
  ring

def christoffel (G : MetricDerivative (V := V)) : V →L[ℝ] V →L[ℝ] V :=
  (((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] V) ≃ₗ[ℝ] (V →L[ℝ] V)).toLinearMap).comp
    (LinearMap.mk₂ ℝ (christoffelValue G) (christoffelValue_add_left G)
      (christoffelValue_smul_left G) (christoffelValue_add_right G)
      (christoffelValue_smul_right G))).toContinuousLinearMap

@[simp] lemma christoffel_apply (G : MetricDerivative (V := V)) (u v : V) :
    christoffel G u v = christoffelValue G u v := rfl

lemma christoffel_symm (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v : V) :
    christoffel G u v = christoffel G v u := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG w u v]
  ring

lemma christoffel_metric (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (u v w : V) :
    ⟪christoffel G u v,w⟫ + ⟪v,christoffel G u w⟫ = G u v w := by
  rw [real_inner_comm (y := v)]
  simp only [christoffel_apply, christoffelValue_inner]
  rw [hG u w v, hG w u v, hG v u w]
  ring

def coordinateJet (G : MetricDerivative (V := V)) (z : V) : V :=
  z - (1/2 : ℝ) • christoffel G z z

@[simp] lemma coordinateJet_zero (G : MetricDerivative (V := V)) :
    coordinateJet G 0 = 0 := by simp [coordinateJet]

lemma coordinateJet_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (coordinateJet G) := by
  exact contDiff_id.sub (((christoffel G).contDiff.comp contDiff_id).clm_apply
    contDiff_id |>.const_smul (1/2 : ℝ))

lemma coordinateJet_hasFDerivAt (G : MetricDerivative (V := V)) (z : V) :
    HasFDerivAt (coordinateJet G)
      (ContinuousLinearMap.id ℝ V - (1/2 : ℝ) •
        (christoffel G z + (christoffel G).flip z)) z := by
  convert! (hasFDerivAt_id z).sub
    (((christoffel G).hasFDerivAt.clm_apply (hasFDerivAt_id z)).const_smul (1/2 : ℝ)) using 1

lemma coordinateJet_fderiv_zero (G : MetricDerivative (V := V)) :
    fderiv ℝ (coordinateJet G) 0 = ContinuousLinearMap.id ℝ V := by
  rw [(coordinateJet_hasFDerivAt G 0).fderiv]
  simp

def normalJacobian (G : MetricDerivative (V := V)) (z : V) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - christoffel G z

@[simp] lemma normalJacobian_zero (G : MetricDerivative (V := V)) :
    normalJacobian G 0 = ContinuousLinearMap.id ℝ V := by simp [normalJacobian]

lemma coordinateJet_hasFDerivAt_normal (G : MetricDerivative (V := V))
    (hG : ∀ u v w, G u v w = G u w v) (z : V) :
    HasFDerivAt (coordinateJet G) (normalJacobian G z) z := by
  convert coordinateJet_hasFDerivAt G z using 1
  ext v
  simp only [normalJacobian, sub_apply, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply]
  rw [christoffel_symm G hG v z]
  module

lemma normalJacobian_hasFDerivAt (G : MetricDerivative (V := V)) (z : V) :
    HasFDerivAt (normalJacobian G) (-christoffel G) z := by
  exact (christoffel G).hasFDerivAt.const_sub _

lemma normalJacobian_apply_hasFDerivAt (G : MetricDerivative (V := V)) (z v : V) :
    HasFDerivAt (fun y => normalJacobian G y v) (-(christoffel G).flip v) z := by
  exact ((christoffel G).flip v).hasFDerivAt.const_sub v

def pullbackMetric (g : V → MetricTensor (V := V)) (G : MetricDerivative (V := V))
    (z : V) : MetricTensor (V := V) :=
  (g (coordinateJet G z)).bilinearComp (normalJacobian G z) (normalJacobian G z)

@[simp] lemma pullbackMetric_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) : pullbackMetric g G 0 = g 0 := by
  ext v w
  simp [pullbackMetric, ContinuousLinearMap.bilinearComp_apply]

lemma pullbackMetric_scalar_hasFDerivAt_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hg0 : g 0 = innerSL ℝ) (hG : ∀ u v w, G u v w = G u w v) (v w : V) :
    HasFDerivAt (fun z => pullbackMetric g G z v w) (0 : V →L[ℝ] ℝ) 0 := by
  have hφ : HasFDerivAt (coordinateJet G) (ContinuousLinearMap.id ℝ V) 0 := by
    simpa using coordinateJet_hasFDerivAt_normal G hG 0
  have hg' : HasFDerivAt g G (coordinateJet G 0) := by simpa using hg
  have hgc := HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := V)
    (G := MetricTensor (V := V)) (f := coordinateJet G) (f' := ContinuousLinearMap.id ℝ V)
    (g := g) (g' := G) (0 : V) hg' hφ
  simp only [ContinuousLinearMap.comp_id] at hgc
  have h := (hgc.clm_apply (normalJacobian_apply_hasFDerivAt G 0 v)).clm_apply
    (normalJacobian_apply_hasFDerivAt G 0 w)
  convert! h using 1
  ext u
  simp only [Function.comp_apply, coordinateJet_zero, normalJacobian_zero, ContinuousLinearMap.id_apply,
    hg0, ContinuousLinearMap.comp_apply, add_apply, neg_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  change 0 = ⟪v, -christoffel G u w⟫ + (⟪-christoffel G u v,w⟫ + G u v w)
  simp only [inner_neg_left, inner_neg_right]
  have hm := christoffel_metric G hG u v w
  linarith

lemma coordinateJet_hasStrictFDerivAt_zero (G : MetricDerivative (V := V)) :
    HasStrictFDerivAt (coordinateJet G) (ContinuousLinearMap.id ℝ V) 0 := by
  rw [← coordinateJet_fderiv_zero G]
  exact (coordinateJet_contDiff G).contDiffAt.hasStrictFDerivAt (by simp)

lemma normalJacobian_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (normalJacobian G) := contDiff_const.sub (christoffel G).contDiff

lemma pullbackMetric_contDiffAt (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : ContDiffAt ℝ ∞ g 0) :
    ContDiffAt ℝ ∞ (pullbackMetric g G) 0 := by
  have hg' : ContDiffAt ℝ ∞ g (coordinateJet G 0) := by simpa using hg
  have hgc := hg'.comp (0 : V) (coordinateJet_contDiff G).contDiffAt
  have hj := (normalJacobian_contDiff G).contDiffAt (x := (0 : V))
  have hflip : ContDiff ℝ ∞ (fun h : MetricTensor (V := V) => h.flip) :=
    by
      rw [← contDiffOn_univ]
      apply contDiffOn_clm_apply.mpr
      intro v
      apply contDiffOn_clm_apply.mpr
      intro w
      change ContDiffOn ℝ ∞ (fun h : MetricTensor (V := V) => h w v) Set.univ
      exact ((contDiff_id.clm_apply contDiff_const).clm_apply contDiff_const).contDiffOn
  exact hflip.contDiffAt.comp (0 : V)
    ((hflip.contDiffAt.comp (0 : V) (hgc.clm_comp hj)).clm_comp hj)

lemma pullbackMetric_fderiv_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : ContDiffAt ℝ ∞ g 0)
    (hderiv : HasFDerivAt g G 0) (hg0 : g 0 = innerSL ℝ)
    (hG : ∀ u v w, G u v w = G u w v) :
    fderiv ℝ (pullbackMetric g G) 0 = 0 := by
  have hp := ((pullbackMetric_contDiffAt g G hg).differentiableAt (by simp)).hasFDerivAt
  ext u v w
  have h := (hp.clm_apply (hasFDerivAt_const v (0 : V))).clm_apply
    (hasFDerivAt_const w (0 : V))
  have he := h.unique (pullbackMetric_scalar_hasFDerivAt_zero g G hderiv hg0 hG v w)
  have he' := congrArg (fun L : V →L[ℝ] ℝ => L u) he
  simpa using he'

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
