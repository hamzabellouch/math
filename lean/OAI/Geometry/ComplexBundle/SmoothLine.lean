import OAI.Geometry.BundleTests.Bundles
import OAI.Geometry.ComplexBundle.Projective
import OAI.Geometry.ComplexBundle.RealModel
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

noncomputable section

/-! Smooth projective lines, product lines, finite sums, and restrictions. -/

section
open Matrix Topology
open scoped Manifold ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

theorem contDiff_graphLineVector (F : GraphFrame 1 k) : ContDiff ℝ ∞ (graphLineVector F) := by
  have h : ContDiff ℂ ∞ (graphLineVector F) := by
    apply (EuclideanSpace.equiv (Fin (1+k)) ℂ).symm.contDiff.comp
    apply F.symm.toContinuousLinearEquiv.contDiff.comp
    exact contDiff_const.prodMk (contDiff_id.clm_apply contDiff_const)
  exact h.restrict_scalars ℝ

theorem contDiff_vectorOuter {d : ℕ} : ContDiff ℝ ∞ (vectorOuter (d := d)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hi : ContDiff ℝ ∞ (fun v : EuclideanSpace ℂ (Fin d) => v i) :=
    ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  have hj : ContDiff ℝ ∞ (fun v : EuclideanSpace ℂ (Fin d) => v j) :=
    ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  exact hi.mul (Complex.conjCLE.contDiff.comp hj)

theorem contDiff_graphLineProjection_val (F : GraphFrame 1 k) :
    ContDiff ℝ ∞ (fun A => (graphLineProjection F A).val) := by
  apply contDiff_vectorOuter.comp
  exact (((contDiff_graphLineVector F).norm ℂ (graphLineVector_ne_zero F)).inv
    (fun A => norm_ne_zero_iff.mpr (graphLineVector_ne_zero F A))).smul (contDiff_graphLineVector F)

-- Use the topology of the chosen matrix norm for both manifold models.
local instance : TopologicalSpace (Matrix (Fin (1+k)) (Fin (1+k)) ℂ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin (1+k)) (Fin (1+k)) ℂ)).toUniformSpace.toTopologicalSpace

/-- The actual projector matrix of a line is a smooth function on complex
projective space, viewed as a real manifold. -/
theorem contMDiff_projectiveProjection_matrix :
    ContMDiff 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,Matrix (Fin (1+k)) (Fin (1+k)) ℂ) ∞
      (fun P : Grassmann 1 k => ((projectiveProjectionEquiv k).symm P).val) := by
  intro P
  obtain ⟨F,hF⟩ := grassmann_atlas_covers P
  have hchart : ContMDiffAt 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,GraphSlope 1 k) ∞ (grassmannChart F) P :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (Set.mem_range_self F)) hF
  have hc := (contDiff_graphLineProjection_val F).contDiffAt.contMDiffAt.comp P hchart
  apply hc.congr_of_eventuallyEq
  filter_upwards [(grassmannChart F).open_source.mem_nhds hF] with Q hQ
  have he : (projectiveProjectionEquiv k).symm Q = graphLineProjection F (grassmannChart F Q) := by
    apply (projectiveProjectionEquiv k).injective
    rw [Equiv.apply_symm_apply]
    exact ((graphLineProjection_point F _).trans (slopePoint_coordinate F Q hQ)).symm
  exact congrArg Subtype.val he

end Kaplansky.ComplexGrassmann

end

section
open Bundle Topology NormedSpace
open scoped Manifold ContDiff Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def projectiveProjectionMap (k : ℕ) : C(Grassmann 1 k,projectionSpace (1+k) 1) :=
  ⟨(projectiveProjectionEquiv k).symm,continuous_projectiveProjectionEquiv_symm⟩

def projectiveHyperplaneCore (k : ℕ) :=
  pullbackLineCore (projectionDualLineCore (1+k)) (projectiveProjectionMap k)

def matrixColumnLinear {d : ℕ} (i : Fin d) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun A := WithLp.toLp 2 (fun j => A j i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contMDiff_projectiveColumn (i : Fin (1+k)) :
    ContMDiff 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,EuclideanSpace ℂ (Fin (1+k))) ∞
      (fun P => projectionColumn (projectiveProjectionMap k P) i) := by
  intro P
  exact ((matrixColumnLinear i).toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp P
    (contMDiff_projectiveProjection_matrix P)

theorem contDiffAt_normalize {d : ℕ} {v : EuclideanSpace ℂ (Fin d)} (hv : v≠0) :
    ContDiffAt ℝ ∞ (normalize (V := EuclideanSpace ℂ (Fin d))) v := by
  exact ((contDiffAt_id.norm ℂ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id

theorem contMDiffOn_projectiveUnitColumn (i : Fin (1+k)) :
    ContMDiffOn 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,EuclideanSpace ℂ (Fin (1+k))) ∞
      (fun P => unitProjectionColumn (projectiveProjectionMap k P) i)
      ((projectiveHyperplaneCore k).baseSet i) := by
  intro P hP
  exact ((contDiffAt_normalize hP).contMDiffAt.comp P (contMDiff_projectiveColumn i P)).contMDiffWithinAt

/-- The actual dual tautological-line transitions are real smooth. -/
theorem projectiveHyperplaneCore_transition_smooth (a b : Fin (1+k)) :
    ContMDiffOn 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,ℂ →L[ℂ] ℂ) ∞
      ((projectiveHyperplaneCore k).coordChange a b)
      ((projectiveHyperplaneCore k).baseSet a ∩ (projectiveHyperplaneCore k).baseSet b) := by
  intro P hP
  have ha := ((contMDiffOn_projectiveUnitColumn a).mono Set.inter_subset_left) P hP
  have hb := ((contMDiffOn_projectiveUnitColumn b).mono Set.inter_subset_right) P hP
  have hi := (contDiff_inner (𝕜 := ℂ)).contDiffAt.contMDiffAt.comp_contMDiffWithinAt P (hb.prodMk_space ha)
  have hs := Complex.conjCLE.contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt P hi
  let g : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ ℂ)
  exact (g.restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt P hs

end Kaplansky.ComplexGrassmann

end

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky.ComplexGrassmann

section
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

def productLineChartIndex : Option ι → Type
  | none => Unit
  | some i => Fin (1+K i)

/-- L₀ is trivial; Lᵢ is the actual hyperplane line pulled back from factor i. -/
def productLineCore (i : Option ι) :
    VectorBundleCore ℂ (ProjectiveProduct K) ℂ (productLineChartIndex K i) :=
  match i with
  | none => trivialLineCore (ProjectiveProduct K)
  | some i => pullbackLineCore (projectiveHyperplaneCore (K i)) ⟨fun P => P i,continuous_apply i⟩

theorem productLineCore_transition_smooth (i : Option ι)
    (a b : productLineChartIndex K i) :
    ContMDiffOn 𝓘(ℝ,ProjectiveProductModel K) 𝓘(ℝ,ℂ →L[ℂ] ℂ) ∞
      ((productLineCore K i).coordChange a b)
      ((productLineCore K i).baseSet a ∩ (productLineCore K i).baseSet b) := by
  cases i with
  | none => exact contMDiffOn_const
  | some i =>
    exact (projectiveHyperplaneCore_transition_smooth a b).comp
      (contMDiff_projectiveProduct_apply K i).contMDiffOn (fun _ hx => hx)

omit [Fintype ι] in
theorem productLineCore_unitary (i : Option ι)
    (a b : productLineChartIndex K i) (P : ProjectiveProduct K)
    (ha : P ∈ (productLineCore K i).baseSet a)
    (hb : P ∈ (productLineCore K i).baseSet b) (z w : ℂ) :
    inner ℂ ((productLineCore K i).coordChange a b P z)
      ((productLineCore K i).coordChange a b P w) = inner ℂ z w := by
  cases i with
  | none => rfl
  | some i =>
    apply complex_unit_mul_inner
    simpa only [star_star,mul_comm,ContinuousMap.coe_mk] using
      projectionLineTransition_unitary a b (projectiveProjectionMap (K i) (P i)) ha hb

instance productLineCore_contMDiffVectorBundle (i : Option ι) :
    ContMDiffVectorBundle ∞ ℂ (productLineCore K i).Fiber 𝓘(ℝ,ProjectiveProductModel K) :=
  complexCore_contMDiffVectorBundle _ _ (productLineCore_transition_smooth K i)

end

variable {ι S : Type*} [Fintype ι] [Fintype S] (K : ι → ℕ) (label : S → Option ι)

/-- The ordinary smooth Hermitian direct sum of the specified hyperplane
pullbacks and trivial lines on the actual projective product. -/
def smoothLineSumCore := finiteLineSumCore (fun s => productLineCore K (label s))
abbrev SmoothLineSumBundle := (smoothLineSumCore K label).Fiber

instance smoothLineSum_norm (P : ProjectiveProduct K) :
    NormedAddCommGroup (SmoothLineSumBundle K label P) := finiteLineSumFiberNormedAddCommGroup _ P
instance smoothLineSum_inner (P : ProjectiveProduct K) :
    InnerProductSpace ℂ (SmoothLineSumBundle K label P) := finiteLineSumFiberInnerProductSpace _ P

instance smoothLineSum_contMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℂ S) (SmoothLineSumBundle K label)
      𝓘(ℝ,ProjectiveProductModel K) :=
  complexCore_contMDiffVectorBundle _ _
    (finiteLineSumCore_transition_smooth _ _ (fun s => productLineCore_transition_smooth K (label s)))

omit [Fintype ι] in
theorem smoothLineSum_finrank (P : ProjectiveProduct K) :
    Module.finrank ℂ (SmoothLineSumBundle K label P) = Fintype.card S := by
  change Module.finrank ℂ (EuclideanSpace ℂ S) = _
  simp

omit [Fintype ι] in
theorem smoothLineSum_inner_continuousOn (A : Set (ProjectiveProduct K))
    (v w : ∀ P, SmoothLineSumBundle K label P)
    (hv : ContinuousOn (fun P => TotalSpace.mk' (EuclideanSpace ℂ S) P (v P)) A)
    (hw : ContinuousOn (fun P => TotalSpace.mk' (EuclideanSpace ℂ S) P (w P)) A) :
    ContinuousOn (fun P => inner ℂ (v P) (w P)) A :=
  finiteLineSum_inner_continuousOn _ (fun s => productLineCore_unitary K (label s)) A v w hv hw

end Kaplansky.ComplexGrassmann

end

open Bundle Topology
namespace Kaplansky.ComplexGrassmann
variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [TopologicalSpace X]
  (K : κ → ℕ) (f : ι → κ)

def projectiveRestrict : C(ProjectiveProduct K, ProjectiveProduct (fun i => K (f i))) :=
  ⟨fun x i => x (f i), continuous_pi (fun i => continuous_apply (f i))⟩

omit [Fintype ι] [Fintype κ] in
/-- Restricting the base preserves the actual local line coordinates, for
both the trivial line and every hyperplane pullback. -/
theorem continuous_productLine_restrict_iff (i : Option ι)
    (g : X → ProjectiveProduct K) (v : X → ℂ) (hg : Continuous g) :
    Continuous (fun x => TotalSpace.mk' ℂ (E := (productLineCore K (i.map f)).Fiber) (g x) (v x)) ↔
    Continuous (fun x => TotalSpace.mk' ℂ (E := (productLineCore (fun i => K (f i)) i).Fiber)
      (projectiveRestrict K f (g x)) (v x)) := by
  cases i with
  | none =>
    constructor <;> intro h <;> apply continuous_iff_continuousAt.mpr <;> intro x
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨((projectiveRestrict K f).continuous.comp hg).continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨hg.continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩
  | some i =>
    constructor <;> intro h <;> apply continuous_iff_continuousAt.mpr <;> intro x
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨((projectiveRestrict K f).continuous.comp hg).continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩
    · rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨hg.continuousAt,
        ((FiberBundle.continuousAt_totalSpace ℂ _).mp (h.continuousAt)).2⟩

omit [Fintype ι] [Fintype κ] in
/-- The finite orthogonal sum has the ordinary pullback topology under
coordinate restriction. The base and fiber coordinates are explicit. -/
theorem continuous_lineSum_restrict_iff {S : Type*} [Fintype S]
    (label : S → Option ι) (g : X → ProjectiveProduct K)
    (v : X → EuclideanSpace ℂ S) (hg : Continuous g) :
    Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S)
      (E := SmoothLineSumBundle K (fun s => (label s).map f)) (g x) (v x)) ↔
    Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S)
      (E := SmoothLineSumBundle (fun i => K (f i)) label)
      (projectiveRestrict K f (g x)) (v x)) := by
  constructor
  · intro h
    have hc := (continuous_finiteLineSum_iff
      (fun s => productLineCore K ((label s).map f)) _).mp h
    apply (continuous_finiteLineSum_iff
      (fun s => productLineCore (fun i => K (f i)) (label s)) _).mpr
    refine ⟨(projectiveRestrict K f).continuous.comp hg,fun s => ?_⟩
    exact (continuous_productLine_restrict_iff K f (label s) g (fun x => v x s) hg).mp (hc.2 s)
  · intro h
    have hc := (continuous_finiteLineSum_iff
      (fun s => productLineCore (fun i => K (f i)) (label s)) _).mp h
    apply (continuous_finiteLineSum_iff
      (fun s => productLineCore K ((label s).map f)) _).mpr
    refine ⟨hg,fun s => ?_⟩
    exact (continuous_productLine_restrict_iff K f (label s) g (fun x => v x s) hg).mpr (hc.2 s)

end Kaplansky.ComplexGrassmann

end

end OAI
