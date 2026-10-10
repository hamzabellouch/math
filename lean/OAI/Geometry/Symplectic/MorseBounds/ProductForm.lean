import OAI.Geometry.Symplectic.MorseBounds.Symplectic
import OAI.Geometry.Symplectic.MorseBounds.SphereForm
import OAI.Geometry.Symplectic.MorseBounds.CapProduct

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SymplecticProduct
open Set
open scoped Manifold ContDiff
noncomputable section
variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)

abbrev TwoForm := (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

def chartTwoForm (w : TwoForm I (M := M)) (x : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let c := extChartAt I x
  let dc := (mfderiv 𝓘(ℝ,E) I c.symm y).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.toContinuousLinearMap
  (ContinuousLinearMap.precomp ℝ dc).comp ((w (c.symm y)).comp dc)

structure SymplecticForm where
  form : TwoForm I (M := M)
  alternating : ∀ x v, form x v v = 0
  nondegenerate : ∀ x, Function.Injective (form x)
  smooth : ∀ x, ContDiffOn ℝ ∞ (chartTwoForm I form x) (extChartAt I x).target
  closed : ∀ x y, y ∈ (extChartAt I x).target → ∀ u v w : E,
    fderiv ℝ (chartTwoForm I form x) y u v w +
    fderiv ℝ (chartTwoForm I form x) y v w u +
    fderiv ℝ (chartTwoForm I form x) y w u v = 0

def prodForm (wM : TwoForm I (M := M)) (wN : TwoForm J (M := N)) :
    TwoForm (I.prod J) (M := M × N) := fun p =>
  (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.fst ℝ E F)).comp
    ((wM p.1).comp (ContinuousLinearMap.fst ℝ E F)) +
  (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.snd ℝ E F)).comp
    ((wN p.2).comp (ContinuousLinearMap.snd ℝ E F))

end
end MorseArnold.SymplecticProduct

namespace MorseArnold.SymplecticProduct
open scoped Manifold ContDiff

def ProductSymplecticExistence : Prop :=
  ∀ (E F H G M N : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    [I.Boundaryless] [J.Boundaryless]
    [IsManifold I ∞ M] [IsManifold J ∞ N],
    ∀ (wM : SymplecticForm I (M := M)) (wN : SymplecticForm J (M := N)),
      ∃ w : SymplecticForm (I.prod J) (M := M × N), w.form = prodForm I J wM.form wN.form
end MorseArnold.SymplecticProduct

namespace MorseArnold.SymplecticProduct
open Set Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {E F D H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

def pullBilin (j : D →L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ D (E →L[ℝ] ℝ) (D →L[ℝ] ℝ)
    (ContinuousLinearMap.precomp ℝ j)).comp
    ((ContinuousLinearMap.compL ℝ D E (E →L[ℝ] ℝ)).flip j)

@[simp] lemma pullBilin_apply (j : D →L[ℝ] E) (w : E →L[ℝ] E →L[ℝ] ℝ)
    (u v : D) : pullBilin j w u v = w (j u) (j v) := rfl

omit [I.Boundaryless] [IsManifold I ∞ M] in
lemma chartTwoForm_apply (w : TwoForm I (M := M)) (x : M) (y u v : E) :
    chartTwoForm I w x y u v = w ((extChartAt I x).symm y)
      (mfderiv 𝓘(ℝ,E) I (extChartAt I x).symm y u)
      (mfderiv 𝓘(ℝ,E) I (extChartAt I x).symm y v) := rfl

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N] in
lemma prodForm_apply (wM : TwoForm I (M := M)) (wN : TwoForm J (M := N))
    (p : M × N) (u v : TangentSpace (I.prod J) p) :
    prodForm I J wM wN p u v = wM p.1 u.1 v.1 + wN p.2 u.2 v.2 := rfl

lemma chart_prod_derivative (p : M × N) {y : E × F}
    (hy : y ∈ (extChartAt (I.prod J) p).target) :
    mfderiv 𝓘(ℝ,E × F) (I.prod J) (extChartAt (I.prod J) p).symm y =
      (mfderiv 𝓘(ℝ,E) I (extChartAt I p.1).symm y.1).prodMap
      (mfderiv 𝓘(ℝ,F) J (extChartAt J p.2).symm y.2) := by
  have hy' : y.1 ∈ (extChartAt I p.1).target ∧ y.2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  have h1 : MDifferentiableAt 𝓘(ℝ,E) I (extChartAt I p.1).symm y.1 :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p.1) _ hy'.1).contMDiffAt
      ((isOpen_extChartAt_target p.1).mem_nhds hy'.1) |>.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ,F) J (extChartAt J p.2).symm y.2 :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p.2) _ hy'.2).contMDiffAt
      ((isOpen_extChartAt_target p.2).mem_nhds hy'.2) |>.mdifferentiableAt (by simp)
  rw [extChartAt_prod]
  change mfderiv 𝓘(ℝ,E × F) (I.prod J)
    (Prod.map (extChartAt I p.1).symm (extChartAt J p.2).symm) y = _
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mfderiv_prodMap h1 h2

lemma chart_prod (wM : TwoForm I (M := M)) (wN : TwoForm J (M := N))
    (p : M × N) {y : E × F} (hy : y ∈ (extChartAt (I.prod J) p).target) :
    chartTwoForm (I.prod J) (prodForm I J wM wN) p y =
      pullBilin (ContinuousLinearMap.fst ℝ E F) (chartTwoForm I wM p.1 y.1) +
      pullBilin (ContinuousLinearMap.snd ℝ E F) (chartTwoForm J wN p.2 y.2) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [chartTwoForm_apply, chart_prod_derivative p hy]
  change wM ((extChartAt I p.1).symm y.1)
      (mfderiv 𝓘(ℝ,E) I (extChartAt I p.1).symm y.1 u.1)
      (mfderiv 𝓘(ℝ,E) I (extChartAt I p.1).symm y.1 v.1) +
    wN ((extChartAt J p.2).symm y.2)
      (mfderiv 𝓘(ℝ,F) J (extChartAt J p.2).symm y.2 u.2)
      (mfderiv 𝓘(ℝ,F) J (extChartAt J p.2).symm y.2 v.2) = _
  rfl

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N] in
lemma prod_alternating (wM : SymplecticForm I (M := M)) (wN : SymplecticForm J (M := N)) :
    ∀ p v, prodForm I J wM.form wN.form p v v = 0 := by
  intro p v
  exact (prodForm_apply wM.form wN.form p v v).trans
    ((congrArg₂ (fun a b : ℝ => a + b) (wM.alternating p.1 v.1)
      (wN.alternating p.2 v.2)).trans (zero_add 0))

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N] in
lemma prod_nondegenerate (wM : SymplecticForm I (M := M)) (wN : SymplecticForm J (M := N)) :
    ∀ p, Function.Injective (prodForm I J wM.form wN.form p) := by
  intro p u v h
  apply Prod.ext
  · apply wM.nondegenerate p.1
    ext a
    have hh := congrArg (fun f : (E × F) →L[ℝ] ℝ => f (a,0)) h
    change wM.form p.1 u.1 a + wN.form p.2 u.2 0 =
      wM.form p.1 v.1 a + wN.form p.2 v.2 0 at hh
    simpa only [map_zero, add_zero] using hh
  · apply wN.nondegenerate p.2
    ext b
    have hh := congrArg (fun f : (E × F) →L[ℝ] ℝ => f (0,b)) h
    change wM.form p.1 u.1 0 + wN.form p.2 u.2 b =
      wM.form p.1 v.1 0 + wN.form p.2 v.2 b at hh
    simpa only [map_zero, zero_add] using hh

lemma chart_prod_eventually (wM : TwoForm I (M := M)) (wN : TwoForm J (M := N))
    (p : M × N) {y : E × F} (hy : y ∈ (extChartAt (I.prod J) p).target) :
    chartTwoForm (I.prod J) (prodForm I J wM wN) p =ᶠ[𝓝 y]
      (fun z => pullBilin (ContinuousLinearMap.fst ℝ E F) (chartTwoForm I wM p.1 z.1) +
        pullBilin (ContinuousLinearMap.snd ℝ E F) (chartTwoForm J wN p.2 z.2)) := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact chart_prod wM wN p hz

@[reducible] local instance prodBilinNorm : NormedAddCommGroup ((E × F) →L[ℝ] (E × F) →L[ℝ] ℝ) :=
  inferInstance
@[reducible] local instance prodBilinSpace : NormedSpace ℝ ((E × F) →L[ℝ] (E × F) →L[ℝ] ℝ) :=
  inferInstance

lemma prod_chart_smooth (wM : SymplecticForm I (M := M))
    (wN : SymplecticForm J (M := N)) (p : M × N) {y : E × F}
    (hy : y ∈ (extChartAt (I.prod J) p).target) :
    ContDiffAt ℝ ∞ (chartTwoForm (I.prod J) (prodForm I J wM.form wN.form) p) y := by
  have hy' : y.1 ∈ (extChartAt I p.1).target ∧ y.2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  have hM : ContDiffAt ℝ ∞ (chartTwoForm I wM.form p.1) y.1 :=
    (wM.smooth p.1 y.1 hy'.1).contDiffAt
    ((isOpen_extChartAt_target p.1).mem_nhds hy'.1)
  have hN : ContDiffAt ℝ ∞ (chartTwoForm J wN.form p.2) y.2 :=
    (wN.smooth p.2 y.2 hy'.2).contDiffAt
    ((isOpen_extChartAt_target p.2).mem_nhds hy'.2)
  have hM' : ContDiffAt ℝ ∞ (fun z : E × F => chartTwoForm I wM.form p.1 z.1) y :=
    hM.comp y (contDiffAt_fst (𝕜 := ℝ) (n := ∞))
  have hN' : ContDiffAt ℝ ∞ (fun z : E × F => chartTwoForm J wN.form p.2 z.2) y :=
    hN.comp y (contDiffAt_snd (𝕜 := ℝ) (n := ∞))
  have hP : ContDiff ℝ ∞ (pullBilin (ContinuousLinearMap.fst ℝ E F)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ) (n := ∞)
      (pullBilin (ContinuousLinearMap.fst ℝ E F))
  have hQ : ContDiff ℝ ∞ (pullBilin (ContinuousLinearMap.snd ℝ E F)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := F →L[ℝ] F →L[ℝ] ℝ)
      (F := (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ) (n := ∞)
      (pullBilin (ContinuousLinearMap.snd ℝ E F))
  have hL : ContDiffAt ℝ ∞
      (fun z : E × F => pullBilin (ContinuousLinearMap.fst ℝ E F)
        (chartTwoForm I wM.form p.1 z.1)) y :=
    hP.comp_contDiffAt y hM'
  have hR : ContDiffAt ℝ ∞
      (fun z : E × F => pullBilin (ContinuousLinearMap.snd ℝ E F)
        (chartTwoForm J wN.form p.2 z.2)) y :=
    hQ.comp_contDiffAt y hN'
  have hh := hL.add hR
  exact hh.congr_of_eventuallyEq (chart_prod_eventually wM.form wN.form p hy)

lemma prod_chart_deriv (wM : SymplecticForm I (M := M))
    (wN : SymplecticForm J (M := N)) (p : M × N) {y : E × F}
    (hy : y ∈ (extChartAt (I.prod J) p).target) :
    fderiv ℝ (chartTwoForm (I.prod J) (prodForm I J wM.form wN.form) p) y =
      (pullBilin (ContinuousLinearMap.fst ℝ E F)).comp
        ((fderiv ℝ (chartTwoForm I wM.form p.1) y.1).comp (ContinuousLinearMap.fst ℝ E F)) +
      (pullBilin (ContinuousLinearMap.snd ℝ E F)).comp
        ((fderiv ℝ (chartTwoForm J wN.form p.2) y.2).comp (ContinuousLinearMap.snd ℝ E F)) := by
  have hy' : y.1 ∈ (extChartAt I p.1).target ∧ y.2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  have hM := ((wM.smooth p.1 y.1 hy'.1).contDiffAt
    ((isOpen_extChartAt_target p.1).mem_nhds hy'.1)).differentiableAt (by simp)
  have hN := ((wN.smooth p.2 y.2 hy'.2).contDiffAt
    ((isOpen_extChartAt_target p.2).mem_nhds hy'.2)).differentiableAt (by simp)
  have hh := (((pullBilin (ContinuousLinearMap.fst ℝ E F)).hasFDerivAt).comp y
      (hM.hasFDerivAt.comp y (ContinuousLinearMap.fst ℝ E F).hasFDerivAt)).add
      (((pullBilin (ContinuousLinearMap.snd ℝ E F)).hasFDerivAt).comp y
        (hN.hasFDerivAt.comp y (ContinuousLinearMap.snd ℝ E F).hasFDerivAt))
  exact (hh.congr_of_eventuallyEq (chart_prod_eventually wM.form wN.form p hy)).fderiv

lemma prod_closed (wM : SymplecticForm I (M := M))
    (wN : SymplecticForm J (M := N)) (p : M × N) {y : E × F}
    (hy : y ∈ (extChartAt (I.prod J) p).target) (u v w : E × F) :
    fderiv ℝ (chartTwoForm (I.prod J) (prodForm I J wM.form wN.form) p) y u v w +
    fderiv ℝ (chartTwoForm (I.prod J) (prodForm I J wM.form wN.form) p) y v w u +
    fderiv ℝ (chartTwoForm (I.prod J) (prodForm I J wM.form wN.form) p) y w u v = 0 := by
  have hy' : y.1 ∈ (extChartAt I p.1).target ∧ y.2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  rw [prod_chart_deriv wM wN p hy]
  change (fderiv ℝ (chartTwoForm I wM.form p.1) y.1 u.1 v.1 w.1 +
    fderiv ℝ (chartTwoForm J wN.form p.2) y.2 u.2 v.2 w.2) +
    (fderiv ℝ (chartTwoForm I wM.form p.1) y.1 v.1 w.1 u.1 +
    fderiv ℝ (chartTwoForm J wN.form p.2) y.2 v.2 w.2 u.2) +
    (fderiv ℝ (chartTwoForm I wM.form p.1) y.1 w.1 u.1 v.1 +
    fderiv ℝ (chartTwoForm J wN.form p.2) y.2 w.2 u.2 v.2) = 0
  linarith [wM.closed p.1 y.1 hy'.1 u.1 v.1 w.1,
    wN.closed p.2 y.2 hy'.2 u.2 v.2 w.2]

def symplecticProd (wM : SymplecticForm I (M := M)) (wN : SymplecticForm J (M := N)) :
    SymplecticForm (I.prod J) (M := M × N) where
  form := prodForm I J wM.form wN.form
  alternating := prod_alternating wM wN
  nondegenerate := prod_nondegenerate wM wN
  smooth := fun p _ hy => (prod_chart_smooth wM wN p hy).contDiffWithinAt
  closed := fun p _ hy u v w => prod_closed wM wN p hy u v w

theorem productSymplecticExistence : ProductSymplecticExistence := by
  intro E F H G M N _ _ _ _ _ _ _ _ _ _ I J _ _ _ _ wM wN
  exact ⟨symplecticProd wM wN, rfl⟩

end
end MorseArnold.SymplecticProduct

end

end OAI
