import Mathlib
import OAI.Geometry.SmoothYau.Geometry.SphereImmersionTangentSurjective
import OAI.Geometry.SmoothYau.Limits.ManifoldChartPush
import OAI.Geometry.SmoothYau.Spectrum.SphereProjection
import OAI.Geometry.SmoothYau.SphereMetric.RadialBaseEnvelope

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiffAt_coordinateVector (p : M) (i : CoordIndex E) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E => TotalSpace.mk' E ((chartAt E p).symm z) (coordinateVector p z i)) y := by
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E p).symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have hv : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E => TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) z (Module.finBasis ℝ E i : TangentSpace 𝓘(ℝ, E) z)) y := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun _ : E => Module.finBasis ℝ E i) y)
  exact hd.clm_apply_of_inCoordinates hv hf

lemma contDiffOn_metricCoefficient (g : SmoothMetric E M) (p : M) (i j : CoordIndex E) :
    ContDiffOn ℝ ∞ (fun y => metricCoefficients g p y i j) (chartAt E p).target := by
  intro y hy
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E p).symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
  have h : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun z => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) ((chartAt E p).symm z)
        (metricCoefficients g p z i j)) y := by
    exact (g.contMDiff.contMDiffAt.comp y hf).clm_bundle_apply₂
      (contMDiffAt_coordinateVector p i hy) (contMDiffAt_coordinateVector p j hy)
  rw [contMDiffAt_totalSpace] at h
  exact (contMDiffAt_iff_contDiffAt.mp h.2).contDiffWithinAt


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricCoefficients_posDef (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : (metricCoefficients g p y).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact g.symm _ _ _
  · intro a ha
    change (0 : ℝ) < a ⬝ᵥ (metricCoefficients g p y).mulVec a
    have he : (chartAt E p).MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨(contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp),
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp)⟩
    let D : E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y) :=
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
    have hinj : Function.Injective D := he.symm.mfderiv_injective hy
    have hn : D ((Module.finBasis ℝ E).equivFun.symm a) ≠ 0 := by
      intro h
      apply ha
      have hz : (Module.finBasis ℝ E).equivFun.symm a = 0 :=
        hinj (h.trans (map_zero _).symm)
      exact (Module.finBasis ℝ E).equivFun.symm.injective (hz.trans (map_zero _).symm)
    have hp : 0 < g.inner ((chartAt E p).symm y)
        (D ((Module.finBasis ℝ E).equivFun.symm a))
        (D ((Module.finBasis ℝ E).equivFun.symm a)) :=
      g.pos ((chartAt E p).symm y) _ hn
    rw [Module.Basis.equivFun_symm_apply] at hp
    have hD := map_sum D
      (fun i => a i • Module.finBasis ℝ E i) Finset.univ
    rw [hD] at hp
    simp only [map_smul, map_sum, sum_apply,
      smul_apply, smul_eq_mul] at hp
    have hb (i : CoordIndex E) : coordinateVector p y i = D (Module.finBasis ℝ E i) := rfl
    simpa [metricCoefficients, hb, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, g.symm] using hp

lemma metricCoefficients_det_pos (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : 0 < Matrix.det (metricCoefficients g p y) :=
  (metricCoefficients_posDef g p hy).det_pos

lemma contDiffOn_metricDet (g : SmoothMetric E M) (p : M) :
    ContDiffOn ℝ ∞ (fun y => Matrix.det (metricCoefficients g p y)) (chartAt E p).target := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_metricCoefficient g p _ _

lemma contDiffOn_metricDensity (g : SmoothMetric E M) (p : M) :
    ContDiffOn ℝ ∞ (fun y => Real.sqrt (Matrix.det (metricCoefficients g p y)))
      (chartAt E p).target :=
  (contDiffOn_metricDet g p).sqrt (fun _ hy => (metricCoefficients_det_pos g p hy).ne')


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffOn_metricAdjugate (g : SmoothMetric E M) (p : M) (i j : CoordIndex E) :
    ContDiffOn ℝ ∞ (fun y => (metricCoefficients g p y).adjugate i j) (chartAt E p).target := by
  classical
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro k _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact contDiffOn_metricCoefficient g p _ _

lemma contDiffOn_metricInverse (g : SmoothMetric E M) (p : M) (i j : CoordIndex E) :
    ContDiffOn ℝ ∞ (fun y => (metricCoefficients g p y)⁻¹ i j) (chartAt E p).target := by
  classical
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiffOn_metricDet g p).inv (fun _ hy => (metricCoefficients_det_pos g p hy).ne')).mul
    (contDiffOn_metricAdjugate g p i j)

lemma metricInverse_posDef (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : ((metricCoefficients g p y)⁻¹).PosDef :=
  (metricCoefficients_posDef g p hy).inv


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
open scoped Topology InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma quadratic_profile_fderiv {F : E → V} (hF : ContDiff ℝ ∞ F)
    (a b : V) (C : ℝ) (x v : E) :
    fderiv ℝ (fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2) x v =
      2*(inner ℝ a (F x)*inner ℝ a (fderiv ℝ F x v)+
        inner ℝ b (F x)*inner ℝ b (fderiv ℝ F x v)) := by
  have ha : ContDiff ℝ ∞ (fun y => inner ℝ a (F y)) := (innerSL ℝ a).contDiff.comp hF
  have hb : ContDiff ℝ ∞ (fun y => inner ℝ b (F y)) := (innerSL ℝ b).contDiff.comp hF
  have hsq {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
      fderiv ℝ (fun y => (f y)^2) x v = 2*f x*fderiv ℝ f x v := by
    simp only [pow_two]
    rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hf.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [fderiv_fun_add ((contDiff_const.add (ha.pow 2)).differentiable (by simp) x)
      ((hb.pow 2).differentiable (by simp) x),
    fderiv_fun_add (differentiableAt_const C) ((ha.pow 2).differentiable (by simp) x)]
  simp only [add_apply, fderiv_const_apply, zero_add]
  have hla := fderiv_clm_comp_apply (innerSL ℝ a) hF x v
  have hlb := fderiv_clm_comp_apply (innerSL ℝ b) hF x v
  simp only [innerSL_apply_apply] at hla hlb
  rw [hsq ha, hsq hb, hla, hlb]
  ring

omit [FiniteDimensional ℝ E] in
theorem sphere_quadratic_profile_fderiv_ne_zero (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w = inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (C : ℝ)
    (hr₀ : 0 < (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2)
    (hr₁ : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 < 1) :
    fderiv ℝ (fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2) x ≠ 0 := by
  let A := inner ℝ (F x) a
  let B := inner ℝ (F x) b
  obtain ⟨z,hz⟩ := sphere_immersion_tangent_surjective g hF hg hn hd
    (projectedPlaneMap_tangent (F x) a b hn.self_of_nhds (A,B))
  intro hzero
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L z) hzero
  rw [quadratic_profile_fderiv hF, hz] at hh
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  simp only [zero_apply, projectedPlaneMap, LinearMap.comp_apply,
    tangentProjection_apply, planePairMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_right, inner_add_right, inner_smul_right, ha, hb, hab, hba] at hh
  have he : 2*((A^2+B^2)*(1-(A^2+B^2))) = 0 := by
    dsimp only [A,B] at hh ⊢
    rw [real_inner_comm (F x) a, real_inner_comm (F x) b] at hh
    nlinarith only [hh]
  have hp : 0 < 2*((A^2+B^2)*(1-(A^2+B^2))) :=
    mul_pos (by norm_num) (mul_pos hr₀ (sub_pos.mpr hr₁))
  linarith

lemma coordinateMetricGradient_eq_zero_iff (g : SmoothMetric E E) (f : E → ℝ) (x : E) :
    coordinateMetricGradient g f x = 0 ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro h
    have hh := (selfMetricFlat_invertible g x).inverse_apply_eq.mp h
    simpa only [map_zero] using hh
  · intro h
    simp only [coordinateMetricGradient,h,map_zero]


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma positive_bilinear_bounded (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  obtain ⟨m, hm, hml⟩ := compact_positive_bilinear_lower (isCompact_singleton (x := ()))
    (fun _ : Unit => B) continuous_const (fun _ _ => hpos)
  rw [NormedSpace.isVonNBounded_iff ℝ]
  apply (Metric.isBounded_ball (x := (0 : E)) (r := Real.sqrt m⁻¹)).subset
  intro v hv
  change dist v 0 < Real.sqrt m⁻¹
  rw [dist_zero_right]
  apply (Real.lt_sqrt (norm_nonneg _)).mpr
  rw [← one_div m]
  apply (lt_div_iff₀ hm).mpr
  simpa only [mul_comm] using (hml () (mem_singleton ()) v).trans_lt hv

def flatMetricOfForm (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v) : SmoothMetric E E where
  inner x := B x
  symm := hsym
  pos := hpos
  isVonNBounded x := positive_bilinear_bounded (B x) (hpos x)
  contMDiff := by
    intro x
    erw [contMDiffAt_section x]
    have h := contMDiffAt_iff_contDiffAt.mpr (hB.contDiffAt (x := x))
    convert h using 1
    ext y v w
    have hy : y ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z => TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ) x).baseSet := by
      simp [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.coe_linearMapAt_of_mem _ hy]
    rfl

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local instance chartFormDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartFormDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartFormFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartFormFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def metricBasisCoordinate (i : CoordIndex E) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord i).toContinuousLinearMap

def metricMatrixForm (A : Matrix (CoordIndex E) (CoordIndex E) ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (metricBasisCoordinate i).smulRight (metricBasisCoordinate j)

lemma metricMatrixForm_apply (A : Matrix (CoordIndex E) (CoordIndex E) ℝ) (v w : E) :
    metricMatrixForm A v w =
      ∑ i, ∑ j, A i j * (Module.finBasis ℝ E).coord i v * (Module.finBasis ℝ E).coord j w := by
  simp [metricMatrixForm, metricBasisCoordinate, mul_assoc]

lemma metricMatrixForm_pos {A : Matrix (CoordIndex E) (CoordIndex E) ℝ}
    (hA : A.PosDef) {v : E} (hv : v ≠ 0) : 0 < metricMatrixForm A v v := by
  have hne : (Module.finBasis ℝ E).equivFun v ≠ 0 := by
    simpa only [ne_eq, (Module.finBasis ℝ E).equivFun.map_eq_zero_iff] using hv
  have h := hA.dotProduct_mulVec_pos hne
  simpa [metricMatrixForm_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Module.Basis.equivFun_apply, mul_comm, mul_left_comm, mul_assoc] using h

lemma metricMatrixForm_contDiffOn {A : E → Matrix (CoordIndex E) (CoordIndex E) ℝ}
    {O : Set E} (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O) :
    ContDiffOn ℝ ∞ (fun x => metricMatrixForm (A x)) O := by
  unfold metricMatrixForm
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hA i j).smul contDiffOn_const))

def chartMetricForm (g : SmoothMetric E M) (p : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  metricMatrixForm (metricCoefficients g p y)

lemma chartMetricForm_contDiffOn (g : SmoothMetric E M) (p : M) :
    ContDiffOn ℝ ∞ (chartMetricForm g p) (chartAt E p).target :=
  metricMatrixForm_contDiffOn (contDiffOn_metricCoefficient g p)

lemma chartMetricForm_pos (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) {v : E} (hv : v ≠ 0) :
    0 < chartMetricForm g p y v v :=
  metricMatrixForm_pos (metricCoefficients_posDef g p hy) hv

lemma chartMetricForm_pairing (g : SmoothMetric E M) (p : M) (y v w : E) :
    chartMetricForm g p y v w = g.inner ((chartAt E p).symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y w) := by
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E p).symm y)
  change metricMatrixForm (metricCoefficients g p y) v w = B (D v) (D w)
  rw [metricMatrixForm_apply]
  have hv : v = ∑ i, (Module.finBasis ℝ E).equivFun v i • Module.finBasis ℝ E i := by
    simpa only [Module.Basis.equivFun_symm_apply] using
      ((Module.finBasis ℝ E).equivFun.symm_apply_apply v).symm
  have hw : w = ∑ i, (Module.finBasis ℝ E).equivFun w i • Module.finBasis ℝ E i := by
    simpa only [Module.Basis.equivFun_symm_apply] using
      ((Module.finBasis ℝ E).equivFun.symm_apply_apply w).symm
  conv_rhs => rw [hv, hw]
  unfold metricCoefficients
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [coordinateVector, D, Module.Basis.equivFun_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [B, Module.Basis.coord_apply, mul_comm, mul_left_comm]
  ring_nf
  rfl

lemma chartMetricForm_symm (g : SmoothMetric E M) (p : M) (y v w : E) :
    chartMetricForm g p y v w = chartMetricForm g p y w v := by
  rw [chartMetricForm_pairing, chartMetricForm_pairing, g.symm]

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
variable {n : ℕ}

def sphereChartMetric (g : SmoothMetric (Euclidean n) (Sphere n)) (p : Sphere n) :
    SmoothMetric (Euclidean n) (Euclidean n) :=
  flatMetricOfForm (chartMetricForm g p)
    (contDiffOn_univ.mp (by simpa only [sphere_chart_target] using chartMetricForm_contDiffOn g p))
    (chartMetricForm_symm g p)
    (fun y v hv => chartMetricForm_pos g p (by rw [sphere_chart_target]; trivial) hv)

lemma sphereChartMetric_pairing (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) (y v w : Euclidean n) :
    (sphereChartMetric g p).inner y v w = chartMetricForm g p y v w := rfl

lemma sphereChartMetric_selfFlat (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) (y : Euclidean n) :
    selfMetricFlat (sphereChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply, sphereChartMetric_pairing]

lemma sphereChartMetric_round (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (y v w : Euclidean 3) :
    (sphereChartMetric g p).inner y v w =
      inner ℝ (fderiv ℝ (roundChart (p : Euclidean 4) (sphereFrame p)) y v)
        (fderiv ℝ (roundChart (p : Euclidean 4) (sphereFrame p)) y w) := by
  rw [sphereChartMetric_pairing, chartMetricForm_pairing, hg]
  rw [sphere_coordinate_embedding, sphere_coordinate_embedding]
  rfl

lemma sphereChart_norm_sq (p : Sphere n) (y : Euclidean n) :
    inner ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p) y)
      (roundChart (p : Euclidean (n+1)) (sphereFrame p) y) = 1 := by
  rw [← sphere_chart_symm]
  have hh := ((chartAt (Euclidean n) p).symm y).property
  rw [Metric.mem_sphere, dist_zero_right] at hh
  rw [real_inner_self_eq_norm_sq, hh]
  norm_num

def sphericalBaseProfile (a b : Euclidean 4) (t : ℝ) (q : Sphere 3) : ℝ :=
  Real.log t + (inner ℝ a (q : Euclidean 4))^2 +
    (inner ℝ b (q : Euclidean 4))^2 - t^2

lemma sphericalBaseProfile_smooth (a b : Euclidean 4) (t : ℝ) :
    ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalBaseProfile a b t) := by
  let : Fact (Module.finrank ℝ (Euclidean 4) = 3+1) := ⟨by simp [Euclidean]⟩
  unfold sphericalBaseProfile
  have h₁ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞
      (fun q : Sphere 3 => inner ℝ a (q : Euclidean 4)) :=
    (innerSL ℝ a).contDiff.contMDiff.comp contMDiff_coe_sphere
  have h₂ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞
      (fun q : Sphere 3 => inner ℝ b (q : Euclidean 4)) :=
    (innerSL ℝ b).contDiff.contMDiff.comp contMDiff_coe_sphere
  exact ((contMDiff_const.add (h₁.pow 2)).add (h₂.pow 2)).sub contMDiff_const

theorem sphericalBaseProfile_chart_hessian (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (y v w : Euclidean 3) :
    let F := roundChart (p : Euclidean 4) (sphereFrame p)
    actualCoordinateHessian (sphereChartMetric g p)
      (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y v w =
      2 * (inner ℝ a (fderiv ℝ F y v) * inner ℝ a (fderiv ℝ F y w) +
        inner ℝ b (fderiv ℝ F y v) * inner ℝ b (fderiv ℝ F y w)) -
      2 * ((inner ℝ a (F y))^2 + (inner ℝ b (F y))^2) *
        (sphereChartMetric g p).inner y v w := by
  intro F
  have he : sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm =
      fun z => (Real.log t-t^2) + (inner ℝ a (F z))^2 + (inner ℝ b (F z))^2 := by
    funext z
    dsimp [Function.comp_def, sphericalBaseProfile]
    rw [congrFun (sphere_chart_symm p) z]
    dsimp [F]
    ring
  rw [he]
  exact sphere_quadratic_profile_hessian (sphereChartMetric g p)
    (roundChart_smooth _ _) (Filter.Eventually.of_forall (sphereChartMetric_round g hg p))
    (Filter.Eventually.of_forall (sphereChart_norm_sq p)) (by simp [Euclidean])
    (innerSL ℝ a) (innerSL ℝ b) (Real.log t-t^2) v w

lemma sphericalBaseProfile_chart_eq (p : Sphere 3) (a b : Euclidean 4) (t : ℝ) :
    sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm =
      fun z => (Real.log t-t^2) +
        (inner ℝ a (roundChart (p : Euclidean 4) (sphereFrame p) z))^2 +
        (inner ℝ b (roundChart (p : Euclidean 4) (sphereFrame p) z))^2 := by
  funext z
  dsimp [Function.comp_def, sphericalBaseProfile]
  rw [congrFun (sphere_chart_symm p) z]
  ring

lemma sphericalBaseProfile_chart_smooth (p : Sphere 3) (a b : Euclidean 4) (t : ℝ) :
    ContDiff ℝ ∞ (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) := by
  rw [sphericalBaseProfile_chart_eq]
  exact (contDiff_const.add (((innerSL ℝ a).contDiff.comp (roundChart_smooth _ _)).pow 2)).add
    (((innerSL ℝ b).contDiff.comp (roundChart_smooth _ _)).pow 2)

theorem sphericalBaseProfile_chart_margins (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) (y : Euclidean 3)
    (hr : (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 ≤ 1/8) :
    let G := sphereChartMetric g p
    let f := sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm
    (∀ v, -(1/4 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) ∧
    (∃ P : Submodule ℝ (Euclidean 3), Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) := by
  dsimp only
  rw [sphericalBaseProfile_chart_eq]
  exact sphere_quadratic_hessian_margins_strong (sphereChartMetric g p) (roundChart_smooth _ _)
    (Filter.Eventually.of_forall (sphereChartMetric_round g hg p))
    (Filter.Eventually.of_forall (sphereChart_norm_sq p)) (by simp [Euclidean]) a b ha hb hab _ hr

lemma sphericalBaseProfile_chart_fderiv_ne_zero (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) (y : Euclidean 3)
    (hr₀ : 0 < (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2)
    (hr₁ : (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 < 1) :
    fderiv ℝ (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y ≠ 0 := by
  rw [sphericalBaseProfile_chart_eq]
  exact sphere_quadratic_profile_fderiv_ne_zero (sphereChartMetric g p) (roundChart_smooth _ _)
    (sphereChartMetric_round g hg p y)
    (Filter.Eventually.of_forall (sphereChart_norm_sq p)) (by simp [Euclidean]) a b ha hb hab _ hr₀ hr₁


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff

lemma sphericalBaseProfile_radius (a b : Euclidean 4) (t : ℝ) (q : Sphere 3) :
    sphericalBaseProfile a b t q = radialBaseEnvelope t (sphericalRadius a b q) := by
  rw [radialBaseEnvelope,sphericalRadius_sq]
  dsimp [sphericalBaseProfile]
  ring

def sphericalProfileGlue (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (ψ : Euclidean 3 → ℝ) : Sphere 3 → ℝ :=
  fun q => sphericalBaseProfile a b t q + manifoldChartPush p
    (fun y => ψ y-sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)) q

lemma sphericalProfileGlue_chart (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (ψ : Euclidean 3 → ℝ) :
    sphericalProfileGlue p a b t ψ ∘ (chartAt (Euclidean 3) p).symm = ψ := by
  funext y
  dsimp only [sphericalProfileGlue,Function.comp_def]
  rw [manifoldChartPush_apply p _ (by rw [sphere_chart_target]; trivial)]
  ring

lemma sphericalProfileGlue_smooth (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    {ψ : Euclidean 3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport (fun y => ψ y-
      sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y))) :
    ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalProfileGlue p a b t ψ) :=
  (sphericalBaseProfile_smooth a b t).add
    (contMDiff_manifoldChartPush p (hψ.sub (sphericalBaseProfile_chart_smooth p a b t)) hc
      (by rw [sphere_chart_target]; exact subset_univ _))

lemma sphericalProfileGlue_sub (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (ψ : Euclidean 3 → ℝ) :
    (fun q => sphericalProfileGlue p a b t ψ q-sphericalBaseProfile a b t q) =
      manifoldChartPush p (fun y => ψ y-
        sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)) := by
  funext q
  simp only [sphericalProfileGlue,add_sub_cancel_left]

lemma sphericalProfileGlue_tsupport (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    {ψ : Euclidean 3 → ℝ}
    (hc : HasCompactSupport (fun y => ψ y-
      sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)))
    {U : Set (Euclidean 3)} (hs : tsupport (fun y => ψ y-
      sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)) ⊆ U) :
    tsupport (fun q => sphericalProfileGlue p a b t ψ q-sphericalBaseProfile a b t q) ⊆
      (chartAt (Euclidean 3) p).symm '' U := by
  rw [sphericalProfileGlue_sub]
  exact (manifoldChartPush_tsupport p hc (by rw [sphere_chart_target]; exact subset_univ _)).trans
    (image_mono hs)

lemma sphericalProfileGlue_close (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    {ψ : Euclidean 3 → ℝ} {η : ℝ} (hη : 0 < η)
    (hclose : ∀ y, |ψ y-sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)| < η) :
    ∀ q, |sphericalProfileGlue p a b t ψ q-sphericalBaseProfile a b t q| < η := by
  intro q
  have he := congrFun (sphericalProfileGlue_sub p a b t ψ) q
  rw [he]
  by_cases hq : q ∈ (chartAt (Euclidean 3) p).source
  · simpa only [manifoldChartPush,Set.indicator_of_mem hq,Function.comp_apply] using
      hclose ((chartAt (Euclidean 3) p) q)
  · simpa only [manifoldChartPush,Set.indicator_of_notMem hq,abs_zero] using hη

theorem spherical_envelope_perturbation {U : Set (Sphere 3)}
    (hU : ∀ q ∈ U, (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo q ∧
      sphericalRadius sourceAxisOne sourceAxisTwo q < 1/8) :
    ∃ η > 0, ∀ t ∈ Icc (1/5 : ℝ) (3/10), ∀ φ : Sphere 3 → ℝ,
      tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆ U →
      (∀ q, |φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q| < η) →
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) := by
  obtain ⟨η,hη,hmargin⟩ := radialBaseEnvelope_uniform_sign_margin
  refine ⟨η,hη,?_⟩
  intro t ht φ hs hclose
  have he (q : Sphere 3) (hq : q ∉ U) :
      φ q = sphericalBaseProfile sourceAxisOne sourceAxisTwo t q := by
    have hz : φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z => φ z-
        sphericalBaseProfile sourceAxisOne sourceAxisTwo t z) (fun h => hq (hs h))
    linarith
  have ht0 : 0 < t := by linarith [ht.1]
  constructor
  · intro q hr hrt
    by_cases hq : q ∈ U
    · have hm := hmargin t ht (sphericalRadius sourceAxisOne sourceAxisTwo q)
        ⟨(hU q hq).1.le,(hU q hq).2.le⟩
      rw [← sphericalBaseProfile_radius] at hm
      have hl := (abs_lt.mp (hclose q)).1
      linarith
    · rw [he q hq,sphericalBaseProfile_radius]
      exact radialBaseEnvelope_inside ht0 ht.2 hr hrt
  · intro q htr
    have hq : q ∉ U := by
      intro hq
      have hh := (hU q hq).2
      linarith [ht.1]
    rw [he q hq,sphericalBaseProfile_radius]
    obtain ⟨ha,hb,hab⟩ := source_axes_orthonormal
    exact radialBaseEnvelope_outside ht0 ht.2 htr
      (sphericalRadius_le_one sourceAxisOne sourceAxisTwo ha hb hab q)



end YauCounterexamples
end

end OAI
