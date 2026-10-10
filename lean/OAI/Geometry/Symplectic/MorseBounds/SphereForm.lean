import OAI.Geometry.Symplectic.MorseBounds.SphereCaps
import OAI.Geometry.Symplectic.MorseBounds.Symplectic

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SphereSymplectic
open MorseArnold.SphereCaps MorseArnold.Geometry
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
local instance sphereFormFinrank : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩

def areaBilinear (p : R3) : R3 →L[ℝ] R3 →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (LinearMap.mk₂ ℝ (standardArea p)
      (by intros; simp [standardArea]; ring)
      (by intros; simp [standardArea]; ring)
      (by intros; simp [standardArea]; ring)
      (by intros; simp [standardArea]; ring))).toContinuousLinearMap

@[simp] lemma areaBilinear_apply (p u v : R3) :
    areaBilinear p u v = standardArea p u v := rfl

def areaTrilinear : R3 →L[ℝ] R3 →L[ℝ] R3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := areaBilinear
    map_add' := by intros; ext u v; simp [standardArea]; ring
    map_smul' := by intros; ext u v; simp [standardArea]; ring }

@[simp] lemma areaTrilinear_apply (p u v : R3) :
    areaTrilinear p u v = standardArea p u v := rfl

def tangentInclusion (p : S2) : TangentSpace (𝓡 2) p →L[ℝ] R3 :=
  mvfderiv (𝓡 2) ((↑) : S2 → R3) p

def sphereArea : TwoForm (n := 2) (M := S2) := fun p =>
  (ContinuousLinearMap.precomp ℝ (tangentInclusion p)).comp
    ((areaBilinear (p : R3)).comp (tangentInclusion p))

@[simp] lemma sphereArea_apply (p : S2) (u v : TangentSpace (𝓡 2) p) :
    sphereArea p u v = standardArea (p : R3) (tangentInclusion p u)
      (tangentInclusion p v) := rfl

lemma sphereArea_alternating (p : S2) (u : TangentSpace (𝓡 2) p) :
    sphereArea p u u = 0 := by simp [standardArea]; ring

def cross (p u : R3) : R3 :=
  vec3 (p 1 * u 2 - p 2 * u 1)
    (p 2 * u 0 - p 0 * u 2) (p 0 * u 1 - p 1 * u 0)

lemma inner_formula (p u : R3) :
    inner ℝ p u = p 0 * u 0 + p 1 * u 1 + p 2 * u 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

lemma cross_orthogonal (p u : R3) : inner ℝ p (cross p u) = 0 := by
  simp [inner_formula, cross]; ring

lemma area_cross (p u : R3) :
    standardArea p u (cross p u) =
      (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) -
        (inner ℝ p u) ^ 2 := by
  simp [standardArea, cross, inner_formula]; ring

lemma tangent_orthogonal (p : S2) (u : TangentSpace (𝓡 2) p) :
    inner ℝ (p : R3) (tangentInclusion p u) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := 2) p]
  exact ⟨u,rfl⟩

lemma sphereArea_kernel (p : S2) (u : TangentSpace (𝓡 2) p)
    (hu : sphereArea p u = 0) : u = 0 := by
  have hc : cross (p : R3) (tangentInclusion p u) ∈
      (tangentInclusion p).range := by
    rw [tangentInclusion, range_mvfderiv_subtypeVal (n := 2) p]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (cross_orthogonal _ _)
  obtain ⟨v,hv⟩ := hc
  change tangentInclusion p v = cross (p : R3) (tangentInclusion p u) at hv
  have he := congrArg (fun L => L v) hu
  change standardArea (p : R3) (tangentInclusion p u) (tangentInclusion p v) = 0 at he
  rw [hv,area_cross,sphere_equation,tangent_orthogonal] at he
  simp only [one_mul, zero_pow (by omega : (2:ℕ) ≠ 0), sub_zero] at he
  have hzero : tangentInclusion p u = 0 := by
    ext i
    fin_cases i
    · change (tangentInclusion p u) 0 = 0
      nlinarith [sq_nonneg ((tangentInclusion p u) 1), sq_nonneg ((tangentInclusion p u) 2)]
    · change (tangentInclusion p u) 1 = 0
      nlinarith [sq_nonneg ((tangentInclusion p u) 0), sq_nonneg ((tangentInclusion p u) 2)]
    · change (tangentInclusion p u) 2 = 0
      nlinarith [sq_nonneg ((tangentInclusion p u) 0), sq_nonneg ((tangentInclusion p u) 1)]
  apply injective_mvfderiv_subtypeVal_sphere p
  simpa only [tangentInclusion, map_zero] using hzero

lemma sphereArea_nondegenerate (p : S2) : Function.Injective (sphereArea p) := by
  intro u v huv
  have hh : sphereArea p (u-v) = 0 := by rw [map_sub,huv,sub_self]
  have hz := sphereArea_kernel p (u-v) hh
  exact sub_eq_zero.mp hz

def chartEmbedding (p : S2) : Model 2 → R3 :=
  ((↑) : S2 → R3) ∘ (extChartAt (𝓡 2) p).symm

lemma chartEmbedding_smoothAt (p : S2) (y : Model 2)
    (hy : y ∈ (extChartAt (𝓡 2) p).target) :
    ContDiffAt ℝ ∞ (chartEmbedding p) y := by
  exact ((contMDiff_coe_sphere.contMDiffAt (x := (extChartAt (𝓡 2) p).symm y)).comp y
    ((contMDiffOn_extChartAt_symm p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy))).contDiffAt

lemma chartEmbedding_derivative (p : S2) (y : Model 2)
    (hy : y ∈ (extChartAt (𝓡 2) p).target) :
    fderiv ℝ (chartEmbedding p) y =
      (tangentInclusion ((extChartAt (𝓡 2) p).symm y)).comp
        (mfderiv (𝓡 2) (𝓡 2) (extChartAt (𝓡 2) p).symm y) := by
  have hc := ((contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) p y hy).contMDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := (contMDiff_coe_sphere (n := 2) (m := (∞ : ℕ∞ω))).mdifferentiable (by simp)
    ((extChartAt (𝓡 2) p).symm y)
  have hh := mfderiv_comp y he hc
  rw [mfderiv_eq_fderiv] at hh
  exact hh

lemma chartSphereArea_apply (p : S2) (y : Model 2)
    (hy : y ∈ (extChartAt (𝓡 2) p).target) (u v : Model 2) :
    chartTwoForm sphereArea p y u v = standardArea (chartEmbedding p y)
      (fderiv ℝ (chartEmbedding p) y u) (fderiv ℝ (chartEmbedding p) y v) := by
  rw [chartEmbedding_derivative p y hy]
  rfl

lemma chartSphereArea_alternating (p : S2) (y u : Model 2) :
    chartTwoForm sphereArea p y u u = 0 := by
  exact sphereArea_alternating _ _

lemma sphereArea_smoothAt (p : S2) (y : Model 2)
    (hy : y ∈ (extChartAt (𝓡 2) p).target) :
    ContDiffAt ℝ ∞ (chartTwoForm sphereArea p) y := by
  let f := chartEmbedding p
  let D := fderiv ℝ f
  let B : Model 2 → Model 2 →L[ℝ] Model 2 →L[ℝ] ℝ := fun z =>
    (ContinuousLinearMap.precomp ℝ (D z)).comp ((areaTrilinear (f z)).comp (D z))
  have hf : ContDiffAt ℝ ∞ f y := chartEmbedding_smoothAt p y hy
  have hD : ContDiffAt ℝ ∞ D y := hf.fderiv_right (by simp)
  let T : (Model 2 →L[ℝ] R3) →L[ℝ] (R3 →L[ℝ] ℝ) →L[ℝ] Model 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Model 2) R3 ℝ).flip
  have hT : ContDiff ℝ ∞ T :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model 2 →L[ℝ] R3)
      (F := (R3 →L[ℝ] ℝ) →L[ℝ] Model 2 →L[ℝ] ℝ) T
  have hp : ContDiffAt ℝ ∞ (fun z => T (D z)) y :=
    hT.contDiffAt.comp y hD
  have hA0 : ContDiff ℝ ∞ areaTrilinear :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := R3)
      (F := R3 →L[ℝ] R3 →L[ℝ] ℝ) areaTrilinear
  have hA : ContDiffAt ℝ ∞ (fun z => areaTrilinear (f z)) y :=
    hA0.contDiffAt.comp y hf
  have hAD : ContDiffAt ℝ ∞ (fun z => (areaTrilinear (f z)).comp (D z)) y :=
    hA.clm_comp hD
  have hB : ContDiffAt ℝ ∞ B y := hp.clm_comp hAD
  apply hB.congr_of_eventuallyEq
  filter_upwards [((isOpen_extChartAt_target p).mem_nhds hy)] with z hz
  ext u v
  exact chartSphereArea_apply p z hz u v

lemma derivative_alternating {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (hw : DifferentiableAt ℝ w x)
    (halt : ∀ y u, w y u u = 0) (z u : E) :
    fderiv ℝ w x z u u = 0 := by
  let A : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ u).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)
  have h := HasFDerivAt.comp (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (G := ℝ)
    x A.hasFDerivAt hw.hasFDerivAt
  have he : (fun _ : E => (0 : ℝ)) =ᶠ[𝓝 x] fun y => A (w y) :=
    Filter.Eventually.of_forall (fun y => (halt y u).symm)
  have hh := (h.congr_of_eventuallyEq he).fderiv
  simp only [fderiv_fun_const] at hh
  exact (congrArg (fun f : E →L[ℝ] ℝ => f z) hh).symm

def e2 (i : Fin 2) : Model 2 := EuclideanSpace.single i 1

lemma expand_model2 (u : Model 2) : u = u 0 • e2 0 + u 1 • e2 1 := by
  ext i
  fin_cases i <;> simp [e2]

lemma alternating_skew {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (h : ∀ v, B v v = 0) (u v : E) :
    B u v = -B v u := by
  have hh := h (u+v)
  simp only [map_add, add_apply, h, zero_add, add_zero] at hh
  linarith

lemma model2_cyclic_zero (D : Model 2 →L[ℝ] Model 2 →L[ℝ] Model 2 →L[ℝ] ℝ)
    (ha : ∀ z u, D z u u = 0) (u v w : Model 2) :
    D u v w + D v w u + D w u v = 0 := by
  have h01 (z : Model 2) := alternating_skew (D z) (ha z) (e2 0) (e2 1)
  conv_lhs => rw [expand_model2 u, expand_model2 v, expand_model2 w]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, ha, h01]
  ring

lemma sphereArea_closed (p : S2) (y : Model 2)
    (hy : y ∈ (extChartAt (𝓡 2) p).target) (u v w : Model 2) :
    fderiv ℝ (chartTwoForm sphereArea p) y u v w +
      fderiv ℝ (chartTwoForm sphereArea p) y v w u +
      fderiv ℝ (chartTwoForm sphereArea p) y w u v = 0 := by
  apply model2_cyclic_zero
  exact derivative_alternating _ y ((sphereArea_smoothAt p y hy).differentiableAt (by simp))
    (chartSphereArea_alternating p)

theorem scaled_standardSphere_symplectic (l : ℝ) (hl : 0 < l) :
    ∃ omega : SymplecticForm (n := 2) (M := S2),
      ∀ (p : S2) (u v : TangentSpace (𝓡 2) p),
        omega.form p u v = l * standardArea (p : R3)
          (mvfderiv (𝓡 2) ((↑) : S2 → R3) p u)
          (mvfderiv (𝓡 2) ((↑) : S2 → R3) p v) := by
  let W : TwoForm (n := 2) (M := S2) := fun p => l • sphereArea p
  have hchart (p : S2) : chartTwoForm W p = l • chartTwoForm sphereArea p := by
    ext y u v
    rfl
  have halt (p : S2) (u : TangentSpace (𝓡 2) p) : W p u u = 0 := by
    change l * sphereArea p u u = 0
    rw [sphereArea_alternating,mul_zero]
  have hnd (p : S2) : Function.Injective (W p) := by
    intro u v huv
    apply sphereArea_nondegenerate p
    change l • sphereArea p u = l • sphereArea p v at huv
    exact (smul_right_injective _ hl.ne') huv
  have hs (p : S2) : ContDiffOn ℝ ∞ (chartTwoForm W p)
      (extChartAt (𝓡 2) p).target := by
    rw [hchart]
    intro y hy
    have hscale (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
        ContDiff ℝ ∞ (fun form : E => l • form) := contDiff_const_smul l
    exact ((hscale (Model 2 →L[ℝ] Model 2 →L[ℝ] ℝ)).contDiffAt.comp y
      (sphereArea_smoothAt p y hy)).contDiffWithinAt
  have hc (p : S2) (y : Model 2) (hy : y ∈ (extChartAt (𝓡 2) p).target)
      (u v w : Model 2) :
      fderiv ℝ (chartTwoForm W p) y u v w +
      fderiv ℝ (chartTwoForm W p) y v w u +
      fderiv ℝ (chartTwoForm W p) y w u v = 0 := by
    rw [hchart]
    rw [fderiv_const_smul ((sphereArea_smoothAt p y hy).differentiableAt (by simp)) l]
    change l * fderiv ℝ (chartTwoForm sphereArea p) y u v w +
      l * fderiv ℝ (chartTwoForm sphereArea p) y v w u +
      l * fderiv ℝ (chartTwoForm sphereArea p) y w u v = 0
    rw [← mul_add, ← mul_add,sphereArea_closed p y hy,mul_zero]
  refine ⟨⟨W,halt,hnd,hs,hc⟩,?_⟩
  intro p u v
  rfl

end
end MorseArnold.SphereSymplectic

end

end OAI
