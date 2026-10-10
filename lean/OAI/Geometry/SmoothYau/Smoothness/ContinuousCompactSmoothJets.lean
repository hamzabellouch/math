import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartTensorCoordLocal1

namespace OAI

noncomputable section
namespace YauCounterexamples
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
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance mcfDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance mcfDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance mcfFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance mcfFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
private local instance mcfMatrixMapNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (Matrix ι κ ℝ →L[ℝ] CoordinateForm (E)) :=
  inferInstanceAs (NormedAddCommGroup ((ι → κ → ℝ) →L[ℝ] CoordinateForm (E)))
private local instance mcfMapMatrixNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (E →L[ℝ] Matrix ι κ ℝ) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] (ι → κ → ℝ)))

def metricMatrixFormCLM : Matrix (CoordIndex E) (CoordIndex E) ℝ →L[ℝ] CoordinateForm E :=
  ({ toFun := metricMatrixForm
     map_add' := by
       intro A B
       simp only [metricMatrixForm, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
     map_smul' := by
       intro c A
       simp only [metricMatrixForm, Matrix.smul_apply, smul_eq_mul, mul_smul,
         Finset.smul_sum, RingHom.id_apply] } :
    Matrix (CoordIndex E) (CoordIndex E) ℝ →ₗ[ℝ] CoordinateForm E).toContinuousLinearMap

lemma metricMatrixFormCLM_apply (A : Matrix (CoordIndex E) (CoordIndex E) ℝ) :
    metricMatrixFormCLM A = (metricMatrixForm A : CoordinateForm E) := rfl

omit [FiniteDimensional ℝ E] in
lemma matrix_fderiv_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : E → Matrix ι κ ℝ} {x : E} (hA : DifferentiableAt ℝ A x) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ i j, ‖fderiv ℝ (fun y => A y i j) x‖ ≤ ε) :
    ‖fderiv ℝ A x‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε (norm_nonneg v))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε (norm_nonneg v))).mpr
  intro j
  have he : fderiv ℝ (fun y => A y i j) x v = (fderiv ℝ A x v) i j := by
    rw [fderiv_apply (differentiableAt_pi.mp hA i) j, fderiv_apply hA i]
    rfl
  erw [← he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb i j) (norm_nonneg v))

theorem metricMatrixForm_first_jet_bound
    {A B : E → Matrix (CoordIndex E) (CoordIndex E) ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h₀ : ∀ i j, |A x i j-B x i j| ≤ ε)
    (h₁ : ∀ i j, ‖fderiv ℝ (fun y => A y i j-B y i j) x‖ ≤ ε) :
    ‖metricMatrixForm (A x)-metricMatrixForm (B x)‖ ≤ ‖metricMatrixFormCLM (E := E)‖*ε ∧
    ‖fderiv ℝ (fun y => metricMatrixForm (A y)) x-
      fderiv ℝ (fun y => metricMatrixForm (B y)) x‖ ≤ ‖metricMatrixFormCLM (E := E)‖*ε := by
  let L := metricMatrixFormCLM (E := E)
  have hF : DifferentiableAt ℝ (fun y => A y-B y) x := hA.sub hB
  have hn : ‖A x-B x‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro j
    exact h₀ i j
  have hDn : ‖fderiv ℝ (fun y => A y-B y) x‖ ≤ ε := matrix_fderiv_norm_le hF hε h₁
  constructor
  · change ‖L (A x)-L (B x)‖ ≤ ‖L‖*ε
    rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg L))
  · have hLA : DifferentiableAt ℝ (fun y => metricMatrixForm (A y)) x := L.differentiableAt.comp x hA
    have hLB : DifferentiableAt ℝ (fun y => metricMatrixForm (B y)) x := L.differentiableAt.comp x hB
    rw [← fderiv_fun_sub hLA hLB]
    have he : (fun y => metricMatrixForm (A y)-metricMatrixForm (B y)) = fun y => L (A y-B y) := by
      funext y
      exact (map_sub L _ _).symm
    rw [he]
    have hd : fderiv ℝ (fun y => L (A y-B y)) x = L.comp (fderiv ℝ (fun y => A y-B y) x) :=
      (L.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
    rw [hd]
    exact (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left hDn (norm_nonneg L))


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
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance hmsDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance hmsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance hmsFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmsFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmsDerivNorm : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance hmsDerivSpace : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance

abbrev HessianJetData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (CoordinateForm E × (E →L[ℝ] CoordinateForm E)) × ((E →L[ℝ] ℝ) × CoordinateForm E)

local instance hmsJetNorm : NormedAddCommGroup (HessianJetData E) := inferInstance
local instance hmsJetSpace : NormedSpace ℝ (HessianJetData E) := inferInstance

def christoffelFromJet (B : CoordinateForm E) (D : E →L[ℝ] CoordinateForm E) :
    E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) B.inverse).comp (coordinateKoszul D)

def metricHessianFromFullJet (z : HessianJetData E) : CoordinateForm E :=
  z.2.2 - (ContinuousLinearMap.compL ℝ E E ℝ z.2.1).comp (christoffelFromJet z.1.1 z.1.2)

lemma continuous_coordinateKoszul : Continuous
    (coordinateKoszul : (E →L[ℝ] CoordinateForm E) → E →L[ℝ] CoordinateForm E) := by
  have hDf : Continuous (fun D : E →L[ℝ] CoordinateForm E => D.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.continuous
  exact ((continuous_id.add hDf).sub (continuous_const.clm_comp hDf)).const_smul (1/2 : ℝ)

lemma continuousAt_metricHessianFromFullJet {z : HessianJetData E} (hB : z.1.1.IsInvertible) :
    ContinuousAt (metricHessianFromFullJet : HessianJetData E → CoordinateForm E) z := by
  have hp : ContinuousAt (fun w : HessianJetData E => w.1.1) z :=
    continuous_fst.fst.continuousAt
  have hi : ContinuousAt (fun w : HessianJetData E => w.1.1.inverse) z :=
    (hB.contDiffAt_map_inverse (n := ∞)).continuousAt.comp (f := fun w : HessianJetData E => w.1.1) (x := z) hp
  have hK : Continuous (fun z : HessianJetData E => coordinateKoszul z.1.2) :=
    continuous_coordinateKoszul.comp continuous_fst.snd
  have hΓ : ContinuousAt (fun z : HessianJetData E => christoffelFromJet z.1.1 z.1.2) z :=
    (continuousAt_const.clm_apply hi).clm_comp hK.continuousAt
  exact continuous_snd.snd.continuousAt.sub
    ((continuousAt_const.clm_apply continuous_snd.fst.continuousAt).clm_comp hΓ)

def metricScalarJet (g : SmoothMetric E E) (f : E → ℝ) (x : E) : HessianJetData E :=
  ((selfMetricFlat g x,fderiv ℝ (selfMetricFlat g) x),
    (fderiv ℝ f x,fderiv ℝ (fderiv ℝ f) x))

lemma metricHessianFromFullJet_metricScalarJet (g : SmoothMetric E E) (f : E → ℝ) (x : E) :
    metricHessianFromFullJet (metricScalarJet g f x) = actualCoordinateHessian g f x := rfl

omit [FiniteDimensional ℝ E] in
lemma continuous_metricScalarJet (g : SmoothMetric E E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (metricScalarJet g f) := by
  exact ((contDiff_selfMetricFlat g).continuous.prodMk
      ((contDiff_selfMetricFlat g).continuous_fderiv (by simp))).prodMk
    ((hf.continuous_fderiv (by simp)).prodMk
      ((hf.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)))

def hessianJetMarginSet : Set (HessianJetData E) :=
    {z | hessianMargins z.1.1 (metricHessianFromFullJet z)}

lemma metricScalarJet_margin_interior (g : SmoothMetric E E) (f : E → ℝ) (x : E)
    (h : hessianMargins (selfMetricFlat g x) (actualCoordinateHessian g f x)) :
    metricScalarJet g f x ∈ interior (hessianJetMarginSet (E := E)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hc : ContinuousAt (fun z : HessianJetData E => (z.1.1,metricHessianFromFullJet z))
      (metricScalarJet g f x) :=
    continuous_fst.fst.continuousAt.prodMk
      (continuousAt_metricHessianFromFullJet (selfMetricFlat_invertible g x))
  exact hc ((isOpen_hessianMargins (E := E)).mem_nhds h)

omit [FiniteDimensional ℝ E] in
lemma dist_metricScalarJet_lt (g g₀ : SmoothMetric E E) (f : E → ℝ) (x : E)
    {δ : ℝ} (hδ : 0 < δ)
    (h₀ : ‖selfMetricFlat g x-selfMetricFlat g₀ x‖ < δ)
    (h₁ : ‖fderiv ℝ (selfMetricFlat g) x-fderiv ℝ (selfMetricFlat g₀) x‖ < δ) :
    dist (metricScalarJet g f x) (metricScalarJet g₀ f x) < δ := by
  change max (max (dist (selfMetricFlat g x) (selfMetricFlat g₀ x))
    (dist (fderiv ℝ (selfMetricFlat g) x) (fderiv ℝ (selfMetricFlat g₀) x)))
    (dist (fderiv ℝ f x,fderiv ℝ (fderiv ℝ f) x)
      (fderiv ℝ f x,fderiv ℝ (fderiv ℝ f) x)) < δ
  rw [dist_self, dist_eq_norm, dist_eq_norm]
  exact max_lt (max_lt h₀ h₁) hδ

lemma compact_map_uniform_interior {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {K : Set X} (hK : IsCompact K) {F : X → Y} (hF : Continuous F) {U : Set Y}
    (hU : ∀ x ∈ K, F x ∈ interior U) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y, dist y (F x) < δ → y ∈ U := by
  have hi : F '' K ⊆ interior U := by
    rintro _ ⟨x,hx,rfl⟩
    exact hU x hx
  obtain ⟨δ,hδ,hδU⟩ := (hK.image hF).exists_thickening_subset_open isOpen_interior hi
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy
  exact interior_subset (hδU (mem_thickening_iff.mpr ⟨F x,⟨x,hx,rfl⟩,hy⟩))

theorem compact_hessianMargins_stability (g₀ : SmoothMetric E E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hmargin : ∀ x ∈ K, hessianMargins (selfMetricFlat g₀ x) (actualCoordinateHessian g₀ f x)) :
    ∃ δ > 0, ∀ g : SmoothMetric E E,
      (∀ x ∈ K, ‖selfMetricFlat g x-selfMetricFlat g₀ x‖ < δ ∧
        ‖fderiv ℝ (selfMetricFlat g) x-fderiv ℝ (selfMetricFlat g₀) x‖ < δ) →
      ∀ x ∈ K, hessianMargins (selfMetricFlat g x) (actualCoordinateHessian g f x) := by
  obtain ⟨δ,hδ,hstable⟩ := compact_map_uniform_interior hK
    (continuous_metricScalarJet g₀ hf)
    (fun x hx => metricScalarJet_margin_interior g₀ f x (hmargin x hx))
  refine ⟨δ,hδ,?_⟩
  intro g hg x hx
  exact hstable x hx (metricScalarJet g f x)
    (dist_metricScalarJet_lt g g₀ f x hδ (hg x hx).1 (hg x hx).2)


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
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {n : ℕ}
local instance spnENorm : NormedAddCommGroup (Euclidean n) := inferInstance
local instance spnESpace : NormedSpace ℝ (Euclidean n) := inferInstance
local instance spnDualNorm : NormedAddCommGroup (Euclidean n →L[ℝ] ℝ) := inferInstance
local instance spnDualSpace : NormedSpace ℝ (Euclidean n →L[ℝ] ℝ) := inferInstance
local instance spnFormNorm : NormedAddCommGroup (CoordinateForm (Euclidean n)) := inferInstance
local instance spnFormSpace : NormedSpace ℝ (CoordinateForm (Euclidean n)) := inferInstance
local instance spnDerivNorm : NormedAddCommGroup (Euclidean n →L[ℝ] CoordinateForm (Euclidean n)) := inferInstance
local instance spnDerivSpace : NormedSpace ℝ (Euclidean n →L[ℝ] CoordinateForm (Euclidean n)) := inferInstance
private local instance spnMatrixMapNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (Matrix ι κ ℝ →L[ℝ] CoordinateForm (Euclidean n)) :=
  inferInstanceAs (NormedAddCommGroup ((ι → κ → ℝ) →L[ℝ] CoordinateForm (Euclidean n)))

lemma sphere_metricCoefficients_smooth (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) : ContDiff ℝ ∞ (metricCoefficients g p) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiffOn_univ.mp (by
    simpa only [sphere_chart_target] using contDiffOn_metricCoefficient g p i j)

theorem sphere_metric_first_jet_neighborhood (g₀ : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) {K : Set (Euclidean n)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothNeighborhood g₀ {g | ∀ x ∈ K,
      ‖selfMetricFlat (sphereChartMetric g p) x-selfMetricFlat (sphereChartMetric g₀ p) x‖ < δ ∧
      ‖fderiv ℝ (selfMetricFlat (sphereChartMetric g p)) x-
        fderiv ℝ (selfMetricFlat (sphereChartMetric g₀ p)) x‖ < δ} := by
  let L := metricMatrixFormCLM (E := Euclidean n)
  let ε := δ/(‖L‖+1)
  have hden : 0 < ‖L‖+1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hmul : ‖L‖*ε < δ := by
    calc
      ‖L‖*ε < (‖L‖+1)*ε := mul_lt_mul_of_pos_right (by linarith) hε
      _ = δ := by dsimp [ε]; field_simp
  let test : Fin 2 × CoordIndex (Euclidean n) × CoordIndex (Euclidean n) →
      CoordinateTest (Euclidean n) (Sphere n) := fun q =>
    { center := p, compactSet := K, isCompact := hK,
      inTarget := by rw [sphere_chart_target]; exact subset_univ K,
      order := q.1.val, row := q.2.1, column := q.2.2 }
  let tests := (Finset.univ : Finset (Fin 2 × CoordIndex (Euclidean n) × CoordIndex (Euclidean n))).toList.map test
  refine ⟨tests,ε,hε,?_⟩
  intro g hg x hx
  have htest (k : Fin 2) (i j : CoordIndex (Euclidean n)) : test (k,i,j) ∈ tests := by
    exact List.mem_map.mpr ⟨(k,i,j),by simp,rfl⟩
  have h₀ (i j : CoordIndex (Euclidean n)) :
      |metricCoefficients g p x i j-metricCoefficients g₀ p x i j| ≤ ε := by
    have hh := hg (test (0,i,j)) (htest 0 i j) x hx
    simpa only [test,Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh.le
  have h₁ (i j : CoordIndex (Euclidean n)) :
      ‖fderiv ℝ (fun y => metricCoefficients g p y i j-metricCoefficients g₀ p y i j) x‖ ≤ ε := by
    have hh := hg (test (1,i,j)) (htest 1 i j) x hx
    simpa only [test,Fin.val_one,norm_iteratedFDeriv_one] using hh.le
  have hb := metricMatrixForm_first_jet_bound
    ((sphere_metricCoefficients_smooth g p).differentiable (by simp) x)
    ((sphere_metricCoefficients_smooth g₀ p).differentiable (by simp) x) hε.le h₀ h₁
  have he (g : SmoothMetric (Euclidean n) (Sphere n)) :
      selfMetricFlat (sphereChartMetric g p) = fun y => metricMatrixForm (metricCoefficients g p y) :=
    funext (sphereChartMetric_selfFlat g p)
  rw [he g,he g₀]
  exact ⟨hb.1.trans_lt hmul,hb.2.trans_lt hmul⟩

theorem sphericalBaseProfile_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : IsRound g₀) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) {K : Set (Euclidean 3)} (hK : IsCompact K)
    (hr : ∀ y ∈ K, (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 ≤ 1/8) :
    IsSmoothNeighborhood g₀ {g | ∀ y ∈ K,
      hessianMargins (selfMetricFlat (sphereChartMetric g p) y)
        (actualCoordinateHessian (sphereChartMetric g p)
          (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y)} := by
  have hm (y : Euclidean 3) (hy : y ∈ K) :
      hessianMargins (selfMetricFlat (sphereChartMetric g₀ p) y)
        (actualCoordinateHessian (sphereChartMetric g₀ p)
          (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y) := by
    have hh := sphericalBaseProfile_chart_margins g₀ hg₀ p a b ha hb hab t y (hr y hy)
    exact hessianMargins_of_strong _ _ (fun v hv => by
      rw [selfMetricFlat_apply]; exact (sphereChartMetric g₀ p).pos _ _ hv) hh.1 hh.2
  obtain ⟨δ,hδ,hstable⟩ := compact_hessianMargins_stability (sphereChartMetric g₀ p)
    (sphericalBaseProfile_chart_smooth p a b t) hK hm
  obtain ⟨tests,ε,hε,htests⟩ := sphere_metric_first_jet_neighborhood g₀ p hK hδ
  refine ⟨tests,ε,hε,?_⟩
  intro g hg
  exact hstable (sphereChartMetric g p) (htests g hg)


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
open Set Filter Manifold Metric
open scoped Topology ContDiff

lemma IsSmoothNeighborhood.mono {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] (g₀ : SmoothMetric E M) {N O : Set (SmoothMetric E M)}
    (hN : IsSmoothNeighborhood g₀ N) (hNO : N ⊆ O) : IsSmoothNeighborhood g₀ O := by
  obtain ⟨tests,ε,hε,h⟩ := hN
  exact ⟨tests,ε,hε,fun g hg => hNO (h g hg)⟩

lemma IsSmoothNeighborhood.inter {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] (g₀ : SmoothMetric E M) {N O : Set (SmoothMetric E M)}
    (hN : IsSmoothNeighborhood g₀ N) (hO : IsSmoothNeighborhood g₀ O) :
    IsSmoothNeighborhood g₀ (N ∩ O) := by
  obtain ⟨t,ε,hε,h⟩ := hN
  obtain ⟨s,δ,hδ,k⟩ := hO
  refine ⟨t++s,min ε δ,lt_min hε hδ,fun g hg => ⟨h g ?_,k g ?_⟩⟩
  · intro a ha y hy
    exact (hg a (List.mem_append_left _ ha) y hy).trans_le (min_le_left _ _)
  · intro a ha y hy
    exact (hg a (List.mem_append_right _ ha) y hy).trans_le (min_le_right _ _)

lemma chartMetricForm_domination_transfer {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] (g₀ g : SmoothMetric E M) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) (a : ℝ)
    (h : ∀ v : E, chartMetricForm g₀ p (chartAt E p x) v v ≤
      a*chartMetricForm g p (chartAt E p x) v v) :
    ∀ v : TangentSpace 𝓘(ℝ,E) x, g₀.inner x v v ≤ a*g.inner x v v := by
  let c := chartAt E p
  have hc : c.MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) :=
    ⟨mdifferentiableOn_atlas (chart_mem_atlas E p),mdifferentiableOn_atlas_symm (chart_mem_atlas E p)⟩
  have hh : ∀ v : TangentSpace 𝓘(ℝ,E) (c.symm (c x)),
      g₀.inner (c.symm (c x)) v v ≤ a*g.inner (c.symm (c x)) v v := by
    intro v
    obtain ⟨w,rfl⟩ := hc.symm.mfderiv_surjective (c.map_source hx) v
    have hw := h w
    erw [chartMetricForm_pairing, chartMetricForm_pairing] at hw
    exact hw
  have he : c.symm (c x) = x := c.left_inv hx
  exact he ▸ hh

lemma small_bilinear_difference_domination {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B G : E →L[ℝ] E →L[ℝ] ℝ) {m : ℝ} (hm : 0 < m)
    (hB : ∀ v, m*‖v‖^2 ≤ B v v) (hG : ‖G-B‖ < m/2) :
    ∀ v, B v v ≤ 4*G v v := by
  intro v
  have he : |G v v-B v v| ≤ (m/2)*‖v‖^2 := by
    calc
      _ = ‖(G-B) v v‖ := by simp
      _ ≤ ‖G-B‖*‖v‖*‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hG.le (sq_nonneg ‖v‖)]
  have hl := hB v
  have hmnorm : 0 ≤ B v v := (mul_nonneg hm.le (sq_nonneg _)).trans hl
  have ha := (abs_le.mp he).1
  nlinarith

def sphericalHalf (p : Sphere 3) : Set (Sphere 3) :=
  {q | 0 ≤ inner ℝ (p : Euclidean 4) (q : Euclidean 4)}

lemma sphericalHalf_compact (p : Sphere 3) : IsCompact (sphericalHalf p) :=
  (isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)).isCompact

lemma sphericalHalf_in_source (p : Sphere 3) : sphericalHalf p ⊆ (chartAt (Euclidean 3) p).source := by
  intro q hq
  rw [sphere_chart_source]
  change q ≠ -p
  intro he
  rw [he] at hq
  have hp : ‖(p : Euclidean 4)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using p.property
  change 0 ≤ inner ℝ (p : Euclidean 4) (-(p : Euclidean 4)) at hq
  rw [inner_neg_right,real_inner_self_eq_norm_sq,hp] at hq
  norm_num at hq

lemma sphericalHalves_cover (p q : Sphere 3) : q ∈ sphericalHalf p ∨ q ∈ sphericalHalf (-p) := by
  change 0 ≤ inner ℝ (p : Euclidean 4) (q : Euclidean 4) ∨
    0 ≤ inner ℝ (-(p : Euclidean 4)) (q : Euclidean 4)
  rw [inner_neg_left]
  exact le_total 0 _ |>.imp id (fun h => neg_nonneg.mpr h)

lemma sphericalHalf_domination_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (p : Sphere 3) : IsSmoothNeighborhood g₀ {g | ∀ x ∈ sphericalHalf p,
      ∀ v : TangentSpace 𝓘(ℝ,Euclidean 3) x, g₀.inner x v v ≤ 4*g.inner x v v} := by
  let c := chartAt (Euclidean 3) p
  let K := c '' sphericalHalf p
  have hK : IsCompact K := (sphericalHalf_compact p).image_of_continuousOn
    (c.continuousOn.mono (sphericalHalf_in_source p))
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower (sphereChartMetric g₀ p) hK
  apply IsSmoothNeighborhood.mono g₀ (sphere_metric_first_jet_neighborhood g₀ p hK (half_pos hm))
  intro g hg x hx
  apply chartMetricForm_domination_transfer g₀ g p (sphericalHalf_in_source p hx) 4
  have hxx : c x ∈ K := ⟨x,hx,rfl⟩
  have hdom := small_bilinear_difference_domination _ _ hm (hml _ hxx) (hg _ hxx).1
  simpa only [sphereChartMetric_selfFlat] using hdom

theorem spherical_domination_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    IsSmoothNeighborhood g₀ {g | ∀ x (v : TangentSpace 𝓘(ℝ,Euclidean 3) x),
      g₀.inner x v v ≤ 4*g.inner x v v} := by
  apply IsSmoothNeighborhood.mono g₀ (IsSmoothNeighborhood.inter g₀
    (sphericalHalf_domination_neighborhood g₀ sourcePole)
    (sphericalHalf_domination_neighborhood g₀ (-sourcePole)))
  intro g hg x v
  rcases sphericalHalves_cover sourcePole x with h | h
  · exact hg.1 x h v
  · exact hg.2 x h v


end

section
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma matrix_iteratedFDeriv_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {A : E → Matrix ι κ ℝ} {x : E} (hA : ContDiffAt ℝ ∞ A x)
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ i j, ‖iteratedFDeriv ℝ m (fun y => A y i j) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ m A x‖ ≤ ε := by
  apply ContinuousMultilinearMap.opNorm_le_bound hε
  intro v
  have hp := Finset.prod_nonneg (fun k (_ : k ∈ Finset.univ) => norm_nonneg (v k))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε hp)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε hp)).mpr
  intro j
  let L : Matrix ι κ ℝ →L[ℝ] ℝ := (ContinuousLinearMap.proj j : (κ → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : Matrix ι κ ℝ →L[ℝ] (κ → ℝ))
  have he : iteratedFDeriv ℝ m (fun y => A y i j) x v = (iteratedFDeriv ℝ m A x v) i j :=
    congrArg (fun T => T v) (L.iteratedFDeriv_comp_left hA (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
  rw [← he]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb i j) hp)

variable [FiniteDimensional ℝ E]
local instance matrixJetInst1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance matrixJetInst2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance matrixJetInst3 : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance matrixJetInst4 : NormedSpace ℝ (CoordinateForm E) := inferInstance
private local instance matrixJetMatrixMapNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (Matrix ι κ ℝ →L[ℝ] CoordinateForm (E)) :=
  inferInstanceAs (NormedAddCommGroup ((ι → κ → ℝ) →L[ℝ] CoordinateForm (E)))
lemma metricMatrixForm_iterated_jet_bound
    {A : E → Matrix (CoordIndex E) (CoordIndex E) ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ i j, ‖iteratedFDeriv ℝ m (fun y => A y i j) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ m (fun y => metricMatrixForm (A y)) x‖ ≤ ‖metricMatrixFormCLM (E:=E)‖*ε := by
  classical
  let L := metricMatrixFormCLM (E:=E)
  change ‖iteratedFDeriv ℝ m (L ∘ A) x‖ ≤ ‖L‖*ε
  erw [L.iteratedFDeriv_comp_left hA (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (matrix_iteratedFDeriv_norm_le hA m hε hb) (norm_nonneg L))
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise
section CompactSmoothContinuity
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma continuous_compactSmooth_of_jets (K : Compacts E) (f : P → 𝓓_{K}(E,F))
    (hf : ∀ n, Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt,(ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ K).tendsto_nhds]
  intro n ε hε
  have hj : Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f a₀) z.2) := by
    have he : (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f a₀) z.2) =
        (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2-iteratedFDeriv ℝ n (f a₀) z.2) := by
      funext z
      exact iteratedFDeriv_sub_apply
        ((f z.1).contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
        ((f a₀).contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    rw [he]
    exact (hf n).sub (((f a₀).contDiff.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp continuous_snd)
  have he : ∀ᶠ a in 𝓝 a₀, ∀ y ∈ (K : Set E),
      ‖iteratedFDeriv ℝ n (f a-f a₀) y‖ < ε/2 := by
    apply K.isCompact.eventually_forall_of_forall_eventually
    intro y hy
    exact hj.norm.continuousAt.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [he] with a ha
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (half_pos hε).le _ _).mpr
  intro y hy
  exact (ha y hy).le
end CompactSmoothContinuity
namespace ContinuousSmoothFamilyOn
variable {P E F ι : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
lemma pi {f : P → E → ι → F} {U : Set E}
    (hf : ∀ i, ContinuousSmoothFamilyOn (fun p x => f p x i) U) :
    ContinuousSmoothFamilyOn f U := by
  classical
  have hh := sum Finset.univ (fun i p x => Pi.single i (f p x i)) (fun i _ =>
    (hf i).postcomp (ContinuousLinearMap.single ℝ (fun _ : ι => F) i)
      (fun _ _ _ => (ContinuousLinearMap.single ℝ (fun _ : ι => F) i).contDiff.contDiffAt))
  have he : (fun p x => ∑ i, Pi.single i (f p x i)) = f := by
    funext p x i
    simp
  rwa [he] at hh
end ContinuousSmoothFamilyOn
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance compactSmoothContinuityInst1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance compactSmoothContinuityInst2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance compactSmoothContinuityInst3 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance compactSmoothContinuityInst4 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
omit [T2Space M] in
lemma continuous_chartTensorOfMetric (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
    (ht : (chartAt E p).target = univ) (q : P → SmoothMetric E M)
    (he : ∀ a x, x ∉ (chartAt E p).symm '' (K : Set E) → (q a).inner x=g₀.inner x)
    (hq : ∀ i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y i j) univ) :
    Continuous (fun a => chartTensorOfMetric g₀ p K ht (q a) (he a)) := by
  apply continuous_compactSmooth_of_jets
  have hf : ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y) univ :=
    ContinuousSmoothFamilyOn.pi (fun i => ContinuousSmoothFamilyOn.pi (hq i))
  have hfm := hf.postcomp (metricMatrixFormCLM (E:=E)) (fun _ _ _ => (metricMatrixFormCLM (E:=E)).contDiff.contDiffAt)
  have hfb : ContinuousSmoothFamilyOn (fun (_ : P) y => chartMetricForm g₀ p y) univ :=
    ContinuousSmoothFamilyOn.const (P:=P) (chartMetricForm g₀ p) (fun y _ =>
    (chartMetricForm_contDiffOn g₀ p).contDiffAt (ht ▸ univ_mem))
  intro n
  change Continuous (fun z : P × E => iteratedFDeriv ℝ n
    (fun y => chartMetricForm (q z.1) p y-chartMetricForm g₀ p y) z.2)
  simpa only [univ_prod_univ,continuousOn_univ,chartMetricForm,metricMatrixFormCLM_apply] using (hfm.sub hfb).jets n

end YauCounterexamples
end

end OAI
