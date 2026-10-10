import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoordinateMetricFirstCoefficient
import OAI.Geometry.SmoothYau.Smoothness.DistanceSquare
import OAI.Geometry.SmoothYau.Smoothness.LinearMetricForm
import OAI.Geometry.SmoothYau.Smoothness.NormIteratedFDerivCompLinear

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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix Manifold
open scoped Topology ContDiff
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def bilinearCoordinateMatrix (b : Module.Basis ι ℝ E) (T : E →L[ℝ] E →L[ℝ] ℝ) :
    Matrix ι ι ℝ := fun i j => T (b i) (b j)

omit [FiniteDimensional ℝ E] in
lemma bilinearCoordinateMatrix_comp (b c : Module.Basis ι ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    bilinearCoordinateMatrix b (T.bilinearComp A A) =
      (LinearMap.toMatrix b c A.toLinearMap).transpose * bilinearCoordinateMatrix c T *
        LinearMap.toMatrix b c A.toLinearMap := by
  ext i j
  change T (A (b i)) (A (b j)) = _
  rw [← c.sum_repr (A (b i)), ← c.sum_repr (A (b j))]
  simp only [map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix_apply, bilinearCoordinateMatrix,
    ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_reindex (e : ι ≃ κ) (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (u : E → ℝ) (x : E) :
    coordinateMetricLaplacian (b.reindex e) (fun y => Matrix.reindex e e (G y)) u x =
      coordinateMetricLaplacian b G u x := by
  have hf (y : E) (i : κ) :
      coordinateMetricFlux (b.reindex e) (fun y => Matrix.reindex e e (G y)) u y i =
        coordinateMetricFlux b G u y (e.symm i) := by
    simp only [coordinateMetricFlux]
    rw [Matrix.det_reindex_self,Matrix.inv_reindex]
    simp only [Matrix.reindex_apply,Module.Basis.reindex_apply,Matrix.submatrix_apply]
    exact congrArg (fun t : ℝ => Real.sqrt (G y).det * t)
      (e.symm.sum_comp (fun j => (G y)⁻¹ (e.symm i) j * fderiv ℝ u y (b j)))
  simp only [coordinateMetricLaplacian,Matrix.det_reindex_self]
  simp_rw [hf]
  simp only [Module.Basis.reindex_apply]
  exact congrArg (fun t : ℝ => (Real.sqrt (G x).det)⁻¹ * t)
    (e.symm.sum_comp (fun i => fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i)))

omit [FiniteDimensional ℝ E] in
lemma mixed_jacobianMatrix_id_isUnit (b c : Module.Basis ι ℝ E) (x : E) :
    IsUnit (mixed_jacobianMatrix b c (id : E → E) x).det := by
  have hp : LinearMap.toMatrix c b (LinearMap.id : E →ₗ[ℝ] E) *
      LinearMap.toMatrix b c (LinearMap.id : E →ₗ[ℝ] E) = 1 := by
    rw [← LinearMap.toMatrix_comp,LinearMap.id_comp,LinearMap.toMatrix_id]
  have hdet := congrArg Matrix.det hp
  rw [Matrix.det_mul,Matrix.det_one] at hdet
  apply isUnit_iff_ne_zero.mpr
  rw [mixed_jacobianMatrix,fderiv_id]
  exact right_ne_zero_of_mul_eq_one hdet

lemma coordinateVector_self (p y : E) (i : CoordIndex E) :
    coordinateVector p y i = Module.finBasis ℝ E i := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : E → E) y (Module.finBasis ℝ E i) = _
  rw [mfderiv_id]
  rfl

lemma metricCoefficients_self (g : SmoothMetric E E) (p y : E) (i j : CoordIndex E) :
    metricCoefficients g p y i j = g.inner y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  simp only [metricCoefficients,coordinateVector_self]
  rfl

lemma laplaceBeltrami_self (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    laplaceBeltrami g u x =
      coordinateMetricLaplacian (Module.finBasis ℝ E) (metricCoefficients g x) u x := by
  simp only [laplaceBeltrami,coordinateMetricLaplacian,coordinateMetricFlux,
    chartAt_self_eq,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,
    Function.comp_id,id_eq]


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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
lemma bilinearCoordinateMatrix_posDef (b : Module.Basis ι ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ v w, T v w = T w v)
    (hp : ∀ v, v ≠ 0 → 0 < T v v) : (bilinearCoordinateMatrix b T).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact hs _ _
  · intro a ha
    have hn : b.equivFun.symm a ≠ 0 := by
      intro h
      exact ha (b.equivFun.symm.injective (h.trans (map_zero _).symm))
    have h := hp _ hn
    rw [Module.Basis.equivFun_symm_apply] at h
    simpa [bilinearCoordinateMatrix,map_sum,map_smul,_root_.sum_apply,
      _root_.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,Finset.mul_sum,
      Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm,hs] using h

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
lemma contDiff_bilinearCoordinateMatrix (b : Module.Basis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (fun x => bilinearCoordinateMatrix b (T x)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (hT.clm_apply contDiff_const).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
lemma selfMetricMatrix_pullback (g : SmoothMetric E E) (b c : Module.Basis ι ℝ E)
    (f : E → E) (x : E) :
    pullbackMetricMatrix b c (fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)) f x =
      bilinearCoordinateMatrix b ((selfMetricFlat g (f x)).bilinearComp
        (fderiv ℝ f x) (fderiv ℝ f x)) :=
  (bilinearCoordinateMatrix_comp b c _ _).symm

omit [FiniteDimensional ℝ E] in
lemma selfMetricMatrix_change_basis (g : SmoothMetric E E) (b c : Module.Basis ι ℝ E) :
    pullbackMetricMatrix b c (fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)) id =
      (fun y => bilinearCoordinateMatrix b (selfMetricFlat g y)) := by
  funext x
  rw [selfMetricMatrix_pullback,fderiv_id]
  rfl

lemma coordinateMetricLaplacian_basis_independent (g : SmoothMetric E E)
    (b c : Module.Basis ι ℝ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    coordinateMetricLaplacian b (fun y => bilinearCoordinateMatrix b (selfMetricFlat g y)) u x =
      coordinateMetricLaplacian c (fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)) u x := by
  have hG := (contDiff_bilinearCoordinateMatrix c (contDiff_selfMetricFlat g)).differentiable (by simp) x
  have hp := (bilinearCoordinateMatrix_posDef c (selfMetricFlat g x)
    (selfMetricFlat_symm g x) (fun v hv => selfMetricFlat_pos g x hv)).det_pos
  have h := coordinateMetricLaplacian_pullback (f := (id : E → E)) contDiffAt_id hu hG hp b c
    (mixed_jacobianMatrix_id_isUnit b c x)
  rwa [selfMetricMatrix_change_basis,Function.comp_id] at h

theorem laplaceBeltrami_self_any_basis (g : SmoothMetric E E)
    (b : Module.Basis ι ℝ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    laplaceBeltrami g u x =
      coordinateMetricLaplacian b (fun y => bilinearCoordinateMatrix b (selfMetricFlat g y)) u x := by
  let e : CoordIndex E ≃ ι := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b)
  let c := (Module.finBasis ℝ E).reindex e
  have he (y : E) : Matrix.reindex e e (metricCoefficients g x y) =
      bilinearCoordinateMatrix c (selfMetricFlat g y) := by
    ext i j
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,bilinearCoordinateMatrix,
      c,Module.Basis.reindex_apply,selfMetricFlat_apply,metricCoefficients_self]
  rw [laplaceBeltrami_self,← coordinateMetricLaplacian_reindex e]
  simp_rw [he]
  exact coordinateMetricLaplacian_basis_independent g c b hu

lemma normalWaveMetric_pullback (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) :
    normalWaveMetric g q = pullbackMetricMatrix
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (fun y => bilinearCoordinateMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (selfMetricFlat g y))
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) := by
  funext x
  rw [selfMetricMatrix_pullback]
  ext i j
  exact normalMetricTensor_is_pullback g q.1 q.2 x _ _

theorem laplaceBeltrami_normal_coordinates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {u : NormalWaveSpace → ℝ} {x : NormalWaveSpace}
    (hu : ContDiffAt ℝ 2 u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
    (hx : IsUnit (mixed_jacobianMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x).det) :
    coordinateMetricLaplacian (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (normalWaveMetric g q)
      (u ∘ normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x =
      laplaceBeltrami g u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  rw [laplaceBeltrami_self_any_basis g b hu,normalWaveMetric_pullback]
  exact coordinateMetricLaplacian_pullback
    ((contDiff_normalJetMap _ _ _).of_le (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt hu
    ((contDiff_bilinearCoordinateMatrix b (contDiff_selfMetricFlat g)).differentiable (by simp) _)
    ((bilinearCoordinateMatrix_posDef b _ (selfMetricFlat_symm g _) (fun v hv => selfMetricFlat_pos g _ hv)).det_pos)
    b b hx
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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
section ComplexProjection
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma clm_fderiv_apply (L : ℂ →L[ℝ] F) {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun y => L (f y)) x v = L (fderiv ℝ f x v) := by
  erw [(L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

lemma clm_second_fderiv (L : ℂ →L[ℝ] F) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => L (f z)) y w) x v =
      L (fderiv ℝ (fun y => fderiv ℝ f y w) x v) := by
  have he : (fun y => fderiv ℝ (fun z => L (f z)) y w) =ᶠ[𝓝 x]
      (fun y => L (fderiv ℝ f y w)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact clm_fderiv_apply L (hy.differentiableAt (by norm_num)) w
  rw [he.fderiv_eq]
  apply clm_fderiv_apply
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const w)
end ComplexProjection
section ComplexMetric
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def complexLaplaceBeltrami (g : SmoothMetric E M) (u : M → ℂ) (x : M) : ℂ :=
  ⟨laplaceBeltrami g (Complex.re ∘ u) x, laplaceBeltrami g (Complex.im ∘ u) x⟩
end ComplexMetric
section ComplexCoordinate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def complexCoordinateMetricLaplacian (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (u : E → ℂ) (x : E) : ℂ :=
  ⟨coordinateMetricLaplacian b G (Complex.re ∘ u) x,
    coordinateMetricLaplacian b G (Complex.im ∘ u) x⟩

omit [FiniteDimensional ℝ E] in
lemma complexCoordinateMetricLaplacian_expansion (b : Module.Basis ι ℝ E)
    {G : E → Matrix ι ι ℝ} {u : E → ℂ} {x : E}
    (hG : DifferentiableAt ℝ G x) (hu : ContDiffAt ℝ 2 u x) (hp : 0 < (G x).det) :
    complexCoordinateMetricLaplacian b G u x =
      waveCoordinateOperator b (fun i j y => ((G y)⁻¹ i j : ℂ))
        (fun j y => (coordinateMetricFirstCoefficient b G y j : ℂ)) u x := by
  have hd := hu.differentiableAt (by norm_num)
  apply Complex.ext
  · change coordinateMetricLaplacian b G (Complex.re ∘ u) x = _
    have hur : ContDiffAt ℝ 2 (Complex.re ∘ u) x := Complex.reCLM.contDiff.contDiffAt.comp x hu
    rw [coordinateMetricLaplacian_expansion b hG hur hp]
    simp only [waveCoordinateOperator,waveDeriv,Complex.add_re,Complex.re_sum,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.reCLM hu _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.reCLM hd _
  · change coordinateMetricLaplacian b G (Complex.im ∘ u) x = _
    have hui : ContDiffAt ℝ 2 (Complex.im ∘ u) x := Complex.imCLM.contDiff.contDiffAt.comp x hu
    rw [coordinateMetricLaplacian_expansion b hG hui hp]
    simp only [waveCoordinateOperator,waveDeriv,Complex.add_im,Complex.im_sum,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.imCLM hu _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.imCLM hd _
end ComplexCoordinate

lemma normalWaveJacobian_isUnit (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {x : NormalWaveSpace} (hx : 0 < (normalWaveMetric g q x).det) :
    IsUnit (mixed_jacobianMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [normalWaveMetric_pullback] at hx
  simp only [pullbackMetricMatrix,Matrix.det_mul,Matrix.det_transpose,hz,zero_mul,mul_zero] at hx
  exact lt_irrefl (0 : ℝ) hx

lemma normalWave_complexCoordinate_expansion
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (q : NormalWaveParameter)
    {v : NormalWaveSpace → ℂ} {x : NormalWaveSpace}
    (hv : ContDiffAt ℝ 2 v x) (hx : 0 < (normalWaveMetric g q x).det) :
    waveCoordinateOperator (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
      (fun j y => (normalWaveFirstCoefficient g q y j : ℂ)) v x =
    complexCoordinateMetricLaplacian (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (normalWaveMetric g q) v x := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hG : DifferentiableAt ℝ (normalWaveMetric g q) x := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (contDiff_normalMetricTensor_apply g q.1 q.2 _ _).differentiable (by simp) x
  rw [complexCoordinateMetricLaplacian_expansion b hG hv hx]
  have hcoef (j) : coordinateMetricFirstCoefficient b (normalWaveMetric g q) x j =
      normalWaveFirstCoefficient g q x j := normalWaveDensity_firstCoefficient g q hx j
  change waveCoordinateOperator b _ _ v x = waveCoordinateOperator b _ _ v x
  simp only [waveCoordinateOperator,hcoef]

lemma complexCoordinateMetricLaplacian_normal_coordinates
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (q : NormalWaveParameter)
    {u : NormalWaveSpace → ℂ} {x : NormalWaveSpace}
    (hu : ContDiffAt ℝ 2 u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
    (hx : 0 < (normalWaveMetric g q x).det) :
    complexCoordinateMetricLaplacian (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (normalWaveMetric g q)
      (u ∘ normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x =
      complexLaplaceBeltrami g u
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) := by
  have hJ := normalWaveJacobian_isUnit g q hx
  simp only [complexCoordinateMetricLaplacian,complexLaplaceBeltrami,← Function.comp_assoc]
  apply congrArg₂ Complex.mk
  · have hur : ContDiffAt ℝ 2 (Complex.re ∘ u)
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) :=
      Complex.reCLM.contDiff.contDiffAt.comp _ hu
    exact laplaceBeltrami_normal_coordinates g q hur hJ
  · have hui : ContDiffAt ℝ 2 (Complex.im ∘ u)
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) :=
      Complex.imCLM.contDiff.contDiffAt.comp _ hu
    exact laplaceBeltrami_normal_coordinates g q hui hJ

theorem complexLaplaceBeltrami_normal_coordinates
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (q : NormalWaveParameter)
    {u : NormalWaveSpace → ℂ} {x : NormalWaveSpace}
    (hu : ContDiffAt ℝ 2 u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
    (hx : 0 < (normalWaveMetric g q x).det) :
    waveCoordinateOperator (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
      (fun j y => (normalWaveFirstCoefficient g q y j : ℂ))
      (u ∘ normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x =
      complexLaplaceBeltrami g u
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) := by
  have hF : ContDiffAt ℝ 2
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x :=
    ((contDiff_normalJetMap _ _ _).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  exact (normalWave_complexCoordinate_expansion g q (hu.comp x hF) hx).trans
    (complexCoordinateMetricLaplacian_normal_coordinates g q hu hx)
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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def selfWaveMatrix (g : SmoothMetric E E) (x : E) : Matrix (CoordIndex E) (CoordIndex E) ℝ :=
  bilinearCoordinateMatrix (Module.finBasis ℝ E) (selfMetricFlat g x)

lemma contDiff_selfWaveMatrix (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (selfWaveMatrix g) :=
  contDiff_bilinearCoordinateMatrix _ (contDiff_selfMetricFlat g)

lemma selfWaveMatrix_det_pos (g : SmoothMetric E E) (x : E) :
    0 < (selfWaveMatrix g x).det :=
  (bilinearCoordinateMatrix_posDef _ (selfMetricFlat g x)
    (selfMetricFlat_symm g x) (fun _ hv => selfMetricFlat_pos g x hv)).det_pos

lemma contDiff_selfWaveInverse (g : SmoothMetric E E) (i j : CoordIndex E) :
    ContDiff ℝ ∞ (fun x => (selfWaveMatrix g x)⁻¹ i j) := by
  have hG (i j : CoordIndex E) : ContDiff ℝ ∞ (fun x => selfWaveMatrix g x i j) :=
    contDiff_pi.mp (contDiff_pi.mp (contDiff_selfWaveMatrix g) i) j
  rw [←contDiffOn_univ]
  exact (contDiffOn_matrix_inv (selfWaveMatrix g) hG i j).mono
    (fun x _ => (selfWaveMatrix_det_pos g x).ne')

lemma contDiff_selfWaveFirst (g : SmoothMetric E E) (j : CoordIndex E) :
    ContDiff ℝ ∞ (fun x => coordinateMetricFirstCoefficient
      (Module.finBasis ℝ E) (selfWaveMatrix g) x j) := by
  have hρ : ContDiff ℝ ∞ (fun x => Real.sqrt (selfWaveMatrix g x).det) :=
    (contDiff_matrix_det (selfWaveMatrix g) (fun i j =>
      contDiff_pi.mp (contDiff_pi.mp (contDiff_selfWaveMatrix g) i) j)).sqrt
      (fun x => (selfWaveMatrix_det_pos g x).ne')
  apply (hρ.inv (fun x => (Real.sqrt_pos.mpr (selfWaveMatrix_det_pos g x)).ne')).mul
  apply ContDiff.sum
  intro i _
  exact ((hρ.mul (contDiff_selfWaveInverse g i j)).fderiv_right (by simp)).clm_apply contDiff_const

lemma complexLaplaceBeltrami_self_expansion (g : SmoothMetric E E) {u : E → ℂ}
    (hu : ContDiff ℝ ∞ u) (x : E) :
    complexLaplaceBeltrami g u x =
      waveCoordinateOperator (Module.finBasis ℝ E)
        (fun i j y => ((selfWaveMatrix g y)⁻¹ i j : ℂ))
        (fun j y => (coordinateMetricFirstCoefficient (Module.finBasis ℝ E) (selfWaveMatrix g) y j : ℂ))
        u x := by
  have huc : ContDiffAt ℝ 2 u x := (hu.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))).contDiffAt
  have he : complexLaplaceBeltrami g u x =
      complexCoordinateMetricLaplacian (Module.finBasis ℝ E) (selfWaveMatrix g) u x := by
    apply Complex.ext
    · exact laplaceBeltrami_self_any_basis g _ (Complex.reCLM.contDiff.contDiffAt.comp x huc)
    · exact laplaceBeltrami_self_any_basis g _ (Complex.imCLM.contDiff.contDiffAt.comp x huc)
  rw [he]
  exact complexCoordinateMetricLaplacian_expansion _
    ((contDiff_selfWaveMatrix g).differentiable (by simp) x) huc (selfWaveMatrix_det_pos g x)

lemma contDiff_complexLaplaceBeltrami_self (g : SmoothMetric E E) {u : E → ℂ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (complexLaplaceBeltrami g u) := by
  have he := funext (complexLaplaceBeltrami_self_expansion g hu)
  rw [he]
  exact contDiff_waveCoordinateOperator _ _ _
    (fun i j => Complex.ofRealCLM.contDiff.comp (contDiff_selfWaveInverse g i j))
    (fun j => Complex.ofRealCLM.contDiff.comp (contDiff_selfWaveFirst g j)) u hu

lemma complexLaplaceBeltrami_self_sum {I : Type*} (s : Finset I)
    (g : SmoothMetric E E) (u : I → E → ℂ) (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i)) (x : E) :
    complexLaplaceBeltrami g (fun y => ∑ i ∈ s, u i y) x =
      ∑ i ∈ s, complexLaplaceBeltrami g (u i) x := by
  rw [complexLaplaceBeltrami_self_expansion g (ContDiff.sum hu)]
  rw [waveCoordinateOperator_sum _ _ _ _ _ hu]
  exact Finset.sum_congr rfl (fun i hi => (complexLaplaceBeltrami_self_expansion g (hu i hi) x).symm)

lemma complexLaplaceBeltrami_self_const_mul (g : SmoothMetric E E)
    {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (a : ℂ) (x : E) :
    complexLaplaceBeltrami g (fun y => a*u y) x = a*complexLaplaceBeltrami g u x := by
  rw [complexLaplaceBeltrami_self_expansion g (contDiff_const.mul hu),
    complexLaplaceBeltrami_self_expansion g hu]
  exact waveCoordinateOperator_const_mul _ _ _ _ _ hu _

lemma finiteWaveSuperposition_residual {I : Type*} [Fintype I]
    (g : SmoothMetric E E) {U : I → Fin 3 → E → ℂ}
    (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ)) (γ : I → Fin 3 → ℂ) (lam : ℝ) :
    (fun x => laplaceBeltrami g (finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ) x +
      lam*finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ x) =
    (fun x => ∑ i, ∑ ℓ, (γ i ℓ*(complexLaplaceBeltrami g (U i ℓ) x+(lam : ℂ)*U i ℓ x)).re) := by
  classical
  have hs (x : E) := complexLaplaceBeltrami_self_sum Finset.univ g
    (fun i x => ∑ ℓ, γ i ℓ*U i ℓ x)
    (fun i _ => ContDiff.sum (fun ℓ _ => contDiff_const.mul (hU i ℓ))) x
  simp_rw [complexLaplaceBeltrami_self_sum Finset.univ g _
    (fun ℓ _ => contDiff_const.mul (hU _ ℓ)),
    complexLaplaceBeltrami_self_const_mul g (hU _ _) (γ _ _)] at hs
  have he : finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ = fun x => (∑ i, ∑ ℓ, γ i ℓ*U i ℓ x).re := by
    funext x; simp [finiteWaveSuperposition,Complex.re_sum]
  funext x
  rw [he]
  have hr := congrArg Complex.re (hs x)
  change laplaceBeltrami g (fun y => (∑ i, ∑ ℓ, γ i ℓ*U i ℓ y).re) x = _ at hr
  rw [hr]
  simp only [Complex.re_sum,mul_add,Complex.add_re,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro ℓ _
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring
end

section
open Set Filter Function Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma linearPullbackMetric_laplace (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : F) :
    laplaceBeltrami (linearPullbackMetric g L) (f ∘ L) x = laplaceBeltrami g f (L x) := by
  classical
  let b := Module.finBasis ℝ F
  let c := b.map L.toLinearEquiv
  let G := fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)
  have hmat : (fun y => bilinearCoordinateMatrix b (selfMetricFlat (linearPullbackMetric g L) y)) = G ∘ L := by
    funext y
    ext i j
    exact linearPullbackMetric_flat g L y (b i) (b j)
  have hcb (i : CoordIndex F) : c i=L (b i) := rfl
  have hflux (i : CoordIndex F) : (fun y => coordinateMetricFlux b (G ∘ L) (f ∘ L) y i) =
      (fun y => coordinateMetricFlux c G f y i) ∘ L := by
    funext y
    simp only [coordinateMetricFlux,Function.comp_apply,fderiv_linearEquiv_comp hf L,hcb]
  have h2 : ContDiff ℝ 2 f := hf.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
  have h2c : ContDiff ℝ 2 (f ∘ L) := h2.comp L.contDiff
  rw [laplaceBeltrami_self_any_basis _ b h2c.contDiffAt,
    laplaceBeltrami_self_any_basis _ c h2.contDiffAt,hmat]
  dsimp only [coordinateMetricLaplacian]
  change (Real.sqrt (G (L x)).det)⁻¹ * _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hflux]
  have hG := (contDiff_bilinearCoordinateMatrix c (contDiff_selfMetricFlat g)).differentiable (by simp) (L x)
  have hp := (bilinearCoordinateMatrix_posDef c (selfMetricFlat g (L x))
    (selfMetricFlat_symm g (L x)) (fun v hv => selfMetricFlat_pos g (L x) hv)).det_pos
  have hdi : DifferentiableAt ℝ (fun y => coordinateMetricFlux c G f y i) (L x) :=
    differentiableAt_pi.mp (differentiableAt_coordinateMetricFlux h2.contDiffAt hG hp c) i
  rw [fderiv_comp x hdi L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,hcb]
  rfl
end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma bilinearCoordinateMatrix_posDef_normed (b : Module.Basis ι ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ v w, T v w = T w v)
    (hp : ∀ v, v ≠ 0 → 0 < T v v) : (bilinearCoordinateMatrix b T).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact hs _ _
  · intro a ha
    have hn : b.equivFun.symm a ≠ 0 := by
      intro h
      exact ha (b.equivFun.symm.injective (h.trans (map_zero _).symm))
    have h := hp _ hn
    rw [Module.Basis.equivFun_symm_apply] at h
    simpa [bilinearCoordinateMatrix,map_sum,map_smul,_root_.sum_apply,
      _root_.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,Finset.mul_sum,
      Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm,hs] using h
lemma coordinateMetricLaplacian_change_basis_normed
    (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (hT : Differentiable ℝ T)
    (hs : ∀ x v w, T x v w=T x w v) (hp : ∀ x v, v≠0 → 0<T x v v)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    coordinateMetricLaplacian b (fun y => bilinearCoordinateMatrix b (T y)) u x =
      coordinateMetricLaplacian c (fun y => bilinearCoordinateMatrix c (T y)) u x := by
  classical
  let e : ι ≃ κ := Fintype.equivOfCardEq (by rw [←Module.finrank_eq_card_basis b,←Module.finrank_eq_card_basis c])
  let d := b.reindex e
  have hd (y : E) : Matrix.reindex e e (bilinearCoordinateMatrix b (T y)) = bilinearCoordinateMatrix d (T y) := by
    ext i j
    simp [d,Matrix.reindex_apply,Module.Basis.reindex_apply,bilinearCoordinateMatrix]
  rw [←coordinateMetricLaplacian_reindex e]
  simp_rw [hd]
  have hG : DifferentiableAt ℝ (fun y => bilinearCoordinateMatrix c (T y)) x :=
    differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
      ((hT x).clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hpos := (bilinearCoordinateMatrix_posDef_normed c (T x) (hs x) (hp x)).det_pos
  have hpb : pullbackMetricMatrix d c (fun y => bilinearCoordinateMatrix c (T y)) id =
      (fun y => bilinearCoordinateMatrix d (T y)) := by
    funext y
    rw [pullbackMetricMatrix, mixed_jacobianMatrix, fderiv_id]
    have he := bilinearCoordinateMatrix_comp d c (T y) (ContinuousLinearMap.id ℝ E)
    have hid : (T y).bilinearComp (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) = T y := by
      ext v w
      rfl
    simpa only [hid, id_eq] using he.symm
  have h := coordinateMetricLaplacian_pullback (f:=(id:E→E)) contDiffAt_id hu hG hpos d c
    (mixed_jacobianMatrix_id_isUnit d c x)
  rwa [hpb,Function.comp_id] at h
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma laplaceBeltrami_any_basis_univ (g : SmoothMetric E M) (p : M)
    (ht : (chartAt E p).target=univ) (b : Module.Basis ι ℝ E)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) :
    laplaceBeltrami g u p = coordinateMetricLaplacian b
      (fun y => bilinearCoordinateMatrix b (chartMetricForm g p y))
      (u ∘ (chartAt E p).symm) (chartAt E p p) := by
  have hmat (y : E) : metricCoefficients g p y =
      bilinearCoordinateMatrix (Module.finBasis ℝ E) (chartMetricForm g p y) := by
    ext i j
    rw [bilinearCoordinateMatrix,chartMetricForm_pairing]
    rfl
  have hs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (chartAt E p).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,E)) (n:=∞) (x:=p)
    rwa [ht,contMDiffOn_univ] at h
  have hT : Differentiable ℝ (chartMetricForm g p) := by
    have h := chartMetricForm_contDiffOn g p
    rw [ht,contDiffOn_univ] at h
    exact h.differentiable (by simp)
  change coordinateMetricLaplacian (Module.finBasis ℝ E) (metricCoefficients g p)
    (u ∘ (chartAt E p).symm) (chartAt E p p) = _
  rw [show metricCoefficients g p = (fun y => bilinearCoordinateMatrix (Module.finBasis ℝ E) (chartMetricForm g p y)) from funext hmat]
  apply coordinateMetricLaplacian_change_basis_normed _ _ _ hT
    (chartMetricForm_symm g p) (fun y v hv => chartMetricForm_pos g p (ht ▸ mem_univ y) hv)
  exact ((contMDiff_iff_contDiff.mp (hu.comp hs)).of_le (show (2:WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt

end YauCounterexamples
end

end OAI
