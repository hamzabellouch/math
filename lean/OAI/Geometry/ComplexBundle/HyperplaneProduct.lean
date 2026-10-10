import OAI.Geometry.ComplexBundle.Hyperplane
import OAI.Geometry.ComplexBundle.LineStage

namespace OAI

noncomputable section

/-! Hyperplane product sections and regular zeros. -/

section
open Bundle Topology
namespace Kaplansky

/-- Pullback of a genuine continuous section through the actual line-core
pullback construction. -/
theorem continuous_pullbackLineCore_section {B X J : Type*} [TopologicalSpace B] [TopologicalSpace X]
    (C : VectorBundleCore ℂ B ℂ J) (g : C(X,B)) (s : ∀ b, C.Fiber b)
    (hs : Continuous (fun b => TotalSpace.mk' ℂ b (s b))) :
    Continuous (fun x => TotalSpace.mk' ℂ x (show (pullbackLineCore C g).Fiber x from s (g x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_section]
  exact ((FiberBundle.continuousAt_section ℂ (g x)).mp (hs.continuousAt (x := g x))).comp g.continuous.continuousAt

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Exactly K_i copies of each actual pulled-back hyperplane line. -/
def hyperplaneProductStage : LineStage K :=
  ⟨Σ i, Fin (K i),inferInstance,fun s => some s.1⟩

def hyperplaneProductLineSection (s : (hyperplaneProductStage K).Slot) (P : ProjectiveProduct K) :
    (productLineCore K (some s.1)).Fiber P :=
  hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate (K s.1) s.2))
    (projectiveProjectionMap (K s.1) (P s.1))

theorem continuous_hyperplaneProductLineSection (s : (hyperplaneProductStage K).Slot) :
    Continuous (fun P => TotalSpace.mk' ℂ P (hyperplaneProductLineSection K s P)) := by
  have h := continuous_pullbackLineCore_section (projectionDualLineCore (1+K s.1))
    (projectiveProjectionMap (K s.1))
    (hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate (K s.1) s.2)))
    (continuous_hyperplaneFunctionalSection _)
  exact continuous_pullbackLineCore_section (projectiveHyperplaneCore (K s.1))
    ⟨fun P : ProjectiveProduct K => P s.1,continuous_apply s.1⟩ _ h

def hyperplaneProductSection (P : ProjectiveProduct K) : (hyperplaneProductStage K).Fiber P :=
  WithLp.toLp 2 (fun s => hyperplaneProductLineSection K s P)

theorem continuous_hyperplaneProductSection :
    Continuous (fun P => TotalSpace.mk' (hyperplaneProductStage K).Model P (hyperplaneProductSection K P)) := by
  apply (continuous_finiteLineSum_iff (fun s : (hyperplaneProductStage K).Slot =>
    productLineCore K (some s.1)) _).mpr
  exact ⟨continuous_id,continuous_hyperplaneProductLineSection K⟩

def firstCoordinateProduct : ProjectiveProduct K :=
  fun i => projectiveProjectionEquiv (K i) (firstCoordinateProjection (K i))

/-- The canonical section of the actual rank-sum(K_i) hyperplane sum has
one zero on the actual projective-product base. No cohomology identification
or invariance under changes of section is asserted by this zero-set theorem. -/
theorem hyperplaneProductSection_eq_zero_iff (P : ProjectiveProduct K) :
    hyperplaneProductSection K P=0 ↔ P=firstCoordinateProduct K := by
  constructor
  · intro h
    funext i
    apply (projectiveProjectionEquiv (K i)).symm.injective
    change projectiveProjectionMap (K i) (P i)=
      (projectiveProjectionEquiv (K i)).symm (projectiveProjectionEquiv (K i) (firstCoordinateProjection (K i)))
    rw [Equiv.symm_apply_apply]
    apply (hyperplaneCoordinateSections_common_zero _).mp
    intro j
    exact congrArg (fun v : (hyperplaneProductStage K).Fiber P => (show EuclideanSpace ℂ (Σ i, Fin (K i)) from v) ⟨i,j⟩) h
  · rintro rfl
    change (show EuclideanSpace ℂ (Σ i, Fin (K i)) from hyperplaneProductSection K (firstCoordinateProduct K))=0
    ext s
    exact (hyperplaneCoordinateSections_common_zero
      (projectiveProjectionMap (K s.1) (firstCoordinateProduct K s.1))).mpr
      ((projectiveProjectionEquiv (K s.1)).symm_apply_apply _) s.2

theorem hyperplaneProductStage_rank (P : ProjectiveProduct K) :
    Module.finrank ℂ ((hyperplaneProductStage K).Fiber P)=∑ i, K i := by
  change Module.finrank ℂ (EuclideanSpace ℂ (Σ i, Fin (K i)))=_
  simp

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} (K : ι → ℕ)

def canonicalProductGraphPoint (A : ProjectiveProductModel K) : ProjectiveProduct K :=
  fun i => slopePoint (standardLineGraphFrame (K i)) (A i)

theorem canonicalProductGraphPoint_zero :
    canonicalProductGraphPoint K 0=firstCoordinateProduct K := by
  funext i
  apply (projectiveProjectionEquiv (K i)).symm.injective
  change (projectiveProjectionEquiv (K i)).symm (slopePoint (standardLineGraphFrame (K i)) 0)=
    (projectiveProjectionEquiv (K i)).symm (projectiveProjectionEquiv (K i) (firstCoordinateProjection (K i)))
  rw [projectiveProjectionEquiv_symm_slopePoint,standard_graphProjection_zero,Equiv.symm_apply_apply]

variable [Fintype ι]

/-- The actual global product section expressed componentwise in the
constructed graph evaluation trivializations. -/
def canonicalProductSectionCoordinates (A : ProjectiveProductModel K) : (Σ i, Fin (K i)) → ℂ :=
  fun s => (graphHyperplaneTrivialization (standardLineGraphFrame (K s.1))
    ⟨A s.1,hyperplaneProductLineSection K s (canonicalProductGraphPoint K A)⟩).2

theorem canonicalProductSectionCoordinates_eq (A : ProjectiveProductModel K) :
    canonicalProductSectionCoordinates K A = fun s => A s.1 (fun _ => 1) s.2 := by
  funext s
  have he : (show ℂ from hyperplaneProductLineSection K s (canonicalProductGraphPoint K A))=
      hyperplaneFunctionalSection (graphVerticalFunctional (standardLineGraphFrame (K s.1)) s.2)
        (graphLineProjection (standardLineGraphFrame (K s.1)) (A s.1)) := by
    change (show ℂ from hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate (K s.1) s.2))
      ((projectiveProjectionEquiv (K s.1)).symm (slopePoint (standardLineGraphFrame (K s.1)) (A s.1))))=_
    rw [projectiveProjectionEquiv_symm_slopePoint,standard_verticalFunctional]
  change (graphHyperplaneTrivialization (standardLineGraphFrame (K s.1))
    ⟨A s.1,show ℂ from hyperplaneProductLineSection K s (canonicalProductGraphPoint K A)⟩).2=_
  rw [he]
  exact congrFun (graphHyperplaneSectionCoordinates_eq (standardLineGraphFrame (K s.1)) (A s.1)) s.2

def productSlopeEvaluationEquiv : ProjectiveProductModel K ≃L[ℂ] ((Σ i, Fin (K i)) → ℂ) :=
  ((LinearEquiv.piCongrRight (fun i => (slopeEvaluationOneEquiv (K i)).toLinearEquiv)).trans
    (LinearEquiv.piCurry ℂ (fun i (_ : Fin (K i)) => ℂ)).symm).toContinuousLinearEquiv

/-- The unique zero of the actual product section has an invertible complex
linear derivative in the genuine graph bundle coordinates. The Euler-index
invariance and Chern-class identification are not assumed or proved here. -/
theorem canonicalProductSection_regular_zero :
    HasFDerivAt (canonicalProductSectionCoordinates K)
      (productSlopeEvaluationEquiv K).toContinuousLinearMap 0 ∧
      Function.Bijective (productSlopeEvaluationEquiv K) := by
  have he : canonicalProductSectionCoordinates K=productSlopeEvaluationEquiv K :=
    funext (canonicalProductSectionCoordinates_eq K)
  rw [he]
  exact ⟨(productSlopeEvaluationEquiv K).toContinuousLinearMap.hasFDerivAt,
    (productSlopeEvaluationEquiv K).bijective⟩

theorem canonicalProductSection_regular_zero_real :
    HasFDerivAt (canonicalProductSectionCoordinates K)
      ((productSlopeEvaluationEquiv K).toContinuousLinearMap.restrictScalars ℝ) 0 :=
  (canonicalProductSection_regular_zero K).1.restrictScalars ℝ

end Kaplansky

end

end OAI
