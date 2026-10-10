import OAI.Geometry.ComplexBundle.LineStage
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace OAI

noncomputable section

/-! Continuous orthonormal frames and orthogonal complements. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

section
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ} {d : ℕ}

structure ContinuousIndependentStageFrame (a : LineStage K) (d : ℕ) where
  vector : ∀ y, Fin d → a.Fiber y
  continuous_vector : ∀ i, Continuous (fun y => TotalSpace.mk' a.Model y (vector y i))
  independent : ∀ y, LinearIndependent ℂ (vector y)

structure ContinuousOrthonormalStageFrame (a : LineStage K) (d : ℕ) where
  vector : ∀ y, Fin d → a.Fiber y
  continuous_vector : ∀ i, Continuous (fun y => TotalSpace.mk' a.Model y (vector y i))
  orthonormal : ∀ y, Orthonormal ℂ (vector y)

namespace ContinuousIndependentStageFrame
variable {a : LineStage K}

theorem continuous_gram (f : ContinuousIndependentStageFrame a d) :
    Continuous (fun y => Matrix.gram ℂ (f.vector y)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_lineStage_inner_over a id continuous_id (fun y => f.vector y i)
    (fun y => f.vector y j) (f.continuous_vector i) (f.continuous_vector j)

def normalize (f : ContinuousIndependentStageFrame a d) : ContinuousOrthonormalStageFrame a d where
  vector y := metricFrame (f.vector y)
  orthonormal y := metricFrame_orthonormal _ (f.independent y)
  continuous_vector j := by
    have hc := continuous_metricFrame_coefficients _ f.continuous_gram
      (fun y => Matrix.posDef_gram_of_linearIndependent (f.independent y))
    apply continuousOn_univ.mp
    unfold metricFrame frameMul
    apply continuousOn_bundle_sum (𝕜 := ℂ)
    intro i _
    apply continuousOn_bundle_smul
    · exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).continuousOn
    · exact (f.continuous_vector i).continuousOn

theorem normalize_span (f : ContinuousIndependentStageFrame a d) (y : ProjectiveProduct K) :
    Submodule.span ℂ (Set.range (f.normalize.vector y)) =
      Submodule.span ℂ (Set.range (f.vector y)) :=
  span_metricFrame _ (f.independent y)

end ContinuousIndependentStageFrame
end

open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ} {d : ℕ} {a : LineStage K}
namespace ContinuousOrthonormalStageFrame

variable (f : ContinuousOrthonormalStageFrame a d)

abbrev ImageTotal := {z : TotalSpace a.Model a.Fiber //
  z.2 ∈ Submodule.span ℂ (Set.range (f.vector z.proj))}

theorem continuous_synthesis :
    Continuous (fun z : ProjectiveProduct K × EuclideanSpace ℂ (Fin d) =>
      TotalSpace.mk' a.Model z.1 (frameSynthesis (f.vector z.1) z.2)) := by
  apply continuousOn_univ.mp
  change ContinuousOn (fun z : ProjectiveProduct K × EuclideanSpace ℂ (Fin d) =>
    TotalSpace.mk' a.Model z.1 (∑ i, z.2 i • f.vector z.1 i)) Set.univ
  apply continuousOn_bundle_sum_over (𝕜 := ℂ) _ continuous_fst.continuousOn
  intro i _
  apply continuousOn_bundle_smul_over _ continuous_fst.continuousOn
  · exact ((continuous_apply i).comp ((EuclideanSpace.equiv _ ℂ).continuous.comp continuous_snd)).continuousOn
  · exact ((f.continuous_vector i).comp continuous_fst).continuousOn

theorem continuous_analysis :
    Continuous (fun z : TotalSpace a.Model a.Fiber => frameAnalysis (f.vector z.proj) z.2) := by
  have hc : Continuous (fun z : TotalSpace a.Model a.Fiber => fun i : Fin d =>
      inner ℂ (f.vector z.proj i) z.2) := by
    apply continuous_pi
    intro i
    exact continuous_lineStage_inner_over a _ (FiberBundle.continuous_proj _ _)
      (fun z => f.vector z.proj i) (fun z => z.2)
      ((f.continuous_vector i).comp (FiberBundle.continuous_proj _ _)) continuous_id
  exact (EuclideanSpace.equiv (Fin d) ℂ).symm.continuous.comp hc

/-- A homeomorphism with the subspace topology inherited from the actual
ambient bundle, not a separately declared topology on an abstract image. -/
def imageTotalHomeomorph : ProjectiveProduct K × EuclideanSpace ℂ (Fin d) ≃ₜ f.ImageTotal where
  toFun z := ⟨⟨z.1,frameSynthesis (f.vector z.1) z.2⟩,frameSynthesis_mem_span _ _⟩
  invFun z := (z.val.proj,frameAnalysis (f.vector z.val.proj) z.val.2)
  left_inv z := Prod.ext rfl (frameAnalysis_synthesis _ (f.orthonormal z.1) z.2)
  right_inv z := by
    apply Subtype.ext
    obtain ⟨⟨y,v⟩,hv⟩ := z
    exact congrArg (TotalSpace.mk' a.Model y) (frameSynthesis_analysis _ (f.orthonormal y) hv)
  continuous_toFun := f.continuous_synthesis.subtype_mk _
  continuous_invFun :=
    ((FiberBundle.continuous_proj _ _).comp continuous_subtype_val).prodMk
      (f.continuous_analysis.comp continuous_subtype_val)

@[simp] theorem imageTotalHomeomorph_base
    (z : ProjectiveProduct K × EuclideanSpace ℂ (Fin d)) :
    (f.imageTotalHomeomorph z).val.proj=z.1 := rfl

theorem imageTotalHomeomorph_fiber_linear (y : ProjectiveProduct K) :
    ∃ L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] a.Fiber y,
      ∀ v, (f.imageTotalHomeomorph (y,v)).val.2=L v :=
  ⟨frameSynthesis (f.vector y),fun _ => rfl⟩

def projection (y : ProjectiveProduct K) : a.Fiber y →ₗ[ℂ] a.Fiber y :=
  (frameSynthesis (f.vector y)).comp (frameAnalysis (f.vector y))

theorem projection_idempotent (y : ProjectiveProduct K) (v : a.Fiber y) :
    f.projection y (f.projection y v)=f.projection y v := by
  exact congrArg (frameSynthesis (f.vector y))
    (frameAnalysis_synthesis _ (f.orthonormal y) (frameAnalysis (f.vector y) v))

theorem projection_mem (y : ProjectiveProduct K) (v : a.Fiber y) :
    f.projection y v ∈ Submodule.span ℂ (Set.range (f.vector y)) := frameSynthesis_mem_span _ _

theorem projection_eq_self (y : ProjectiveProduct K) (v : a.Fiber y) :
    f.projection y v = v ↔ v ∈ Submodule.span ℂ (Set.range (f.vector y)) := by
  constructor
  · intro h
    rw [← h]
    exact f.projection_mem y v
  · exact frameSynthesis_analysis _ (f.orthonormal y)

theorem continuous_projection :
    Continuous (fun z : TotalSpace a.Model a.Fiber =>
      TotalSpace.mk' a.Model z.proj (f.projection z.proj z.2)) :=
  f.continuous_synthesis.comp ((FiberBundle.continuous_proj _ _).prodMk f.continuous_analysis)

theorem image_finrank (y : ProjectiveProduct K) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (f.vector y)))=d :=
  frameSpan_finrank _ (f.orthonormal y)

end ContinuousOrthonormalStageFrame
end Kaplansky

end

section
open scoped BigOperators
namespace Kaplansky
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem frameSynthesis_inner (v : Fin d → E) (hv : Orthonormal ℂ v)
    (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (frameSynthesis v x) (frameSynthesis v y)=inner ℂ x y := by
  have h := hv.inner_sum (fun i => x i) (fun i => y i) Finset.univ
  change inner ℂ (∑ i, x i • v i) (∑ i, y i • v i) = _
  rw [h]
  change (∑ i, star (x i)*y i) = ∑ i, inner ℂ (x i) (y i)
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

def frameSynthesisIsometry (v : Fin d → E) (hv : Orthonormal ℂ v) :
    EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] E where
  toLinearMap := frameSynthesis v
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (frameSynthesis_inner v hv)

open ComplexGrassmann
namespace ContinuousOrthonormalStageFrame
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K}

theorem projection_error_inner (f : ContinuousOrthonormalStageFrame a d)
    (y : ProjectiveProduct K) (v : a.Fiber y) (i : Fin d) :
    inner ℂ (f.vector y i) (v-f.projection y v)=0 := by
  have hi := congrArg (fun x : EuclideanSpace ℂ (Fin d) => x i)
    (frameAnalysis_synthesis (f.vector y) (f.orthonormal y) (frameAnalysis (f.vector y) v))
  change inner ℂ (f.vector y i) (f.projection y v)=inner ℂ (f.vector y i) v at hi
  exact (inner_sub_right (𝕜 := ℂ) (f.vector y i) v (f.projection y v)).trans
    (sub_eq_zero.mpr hi.symm)

end ContinuousOrthonormalStageFrame
end Kaplansky

end

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
namespace ContinuousOrthonormalStageFrame
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)

def complementProjection (y : ProjectiveProduct K) : a.Fiber y →ₗ[ℂ] a.Fiber y :=
  LinearMap.id - f.projection y

theorem complementProjection_mem (y : ProjectiveProduct K) (v : a.Fiber y) :
    f.complementProjection y v ∈ (Submodule.span ℂ (Set.range (f.vector y)))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact f.projection_error_inner y v i
  | zero => exact inner_zero_left _
  | add u w hu hw ihu ihw =>
    exact (inner_add_left u w _).trans (by rw [ihu, ihw, zero_add])
  | smul c u hu ihu =>
    exact (inner_smul_left u _ c).trans (by rw [ihu, mul_zero])

theorem projection_eq_zero_of_orthogonal (y : ProjectiveProduct K) (v : a.Fiber y)
    (hv : v ∈ (Submodule.span ℂ (Set.range (f.vector y)))ᗮ) : f.projection y v=0 := by
  have ha : frameAnalysis (f.vector y) v=0 := by
    apply (EuclideanSpace.equiv (Fin d) ℂ).injective
    funext i
    exact (Submodule.mem_orthogonal _ _).mp hv _ (Submodule.subset_span ⟨i,rfl⟩)
  change frameSynthesis (f.vector y) (frameAnalysis (f.vector y) v)=0
  exact (congrArg (frameSynthesis (f.vector y)) ha).trans
    (frameSynthesis (f.vector y)).map_zero

theorem complementProjection_range (y : ProjectiveProduct K) :
    LinearMap.range (f.complementProjection y) = (Submodule.span ℂ (Set.range (f.vector y)))ᗮ := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    exact f.complementProjection_mem y v
  · intro v hv
    refine ⟨v,?_⟩
    change v-f.projection y v=v
    rw [f.projection_eq_zero_of_orthogonal y v hv,sub_zero]

theorem continuous_complementProjection :
    Continuous (fun z : TotalSpace a.Model a.Fiber =>
      TotalSpace.mk' a.Model z.proj (f.complementProjection z.proj z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,?_⟩
  let e := trivializationAt a.Model a.Fiber z.proj
  have hc := ((FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := z)).mp (continuous_id (X := TotalSpace a.Model a.Fiber)).continuousAt).2
  have hp := ((FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := z)).mp f.continuous_projection.continuousAt).2
  apply (hc.sub hp).congr_of_eventuallyEq
  have hn := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt a.Model a.Fiber z.proj)
  filter_upwards [(FiberBundle.continuous_proj a.Model a.Fiber).continuousAt hn] with w hw
  exact (e.linear ℂ hw).map_sub w.2 (f.projection w.proj w.2)

theorem complement_finrank (y : ProjectiveProduct K) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (f.vector y)))ᗮ + d = Fintype.card a.Slot := by
  let V : Fin d → EuclideanSpace ℂ a.Slot := f.vector y
  have hV : Orthonormal ℂ V := f.orthonormal y
  change Module.finrank ℂ (Submodule.span ℂ (Set.range V))ᗮ + d = _
  have h := (Submodule.span ℂ (Set.range V)).finrank_add_finrank_orthogonal
  rw [frameSpan_finrank V hV, finrank_euclideanSpace] at h
  omega

end ContinuousOrthonormalStageFrame
end Kaplansky

end

end OAI
