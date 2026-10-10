import OAI.AlgebraicTopology.IntegralHomology.GraphNormalization
import OAI.Geometry.ComplexBundle.Tensor

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky

section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

/-- The auxiliary factor for the stable obstruction has dimension h. -/
def twistedProjectiveDimensions : Option ι → ℕ
  | none => h
  | some i => K i

abbrev TwistedHyperplaneSlot := Fin h ⊕ (Σ i, Fin (K i))

def twistedOldLabel : TwistedHyperplaneSlot K h → Option (Option ι)
  | .inl _ => none
  | .inr s => some (some s.1)

/-- The summands of (trivial(h) ⊕ H) tensored with the hyperplane line
from the auxiliary factor. This is an explicit vector-bundle core. -/
def twistedHyperplaneLineCore (s : TwistedHyperplaneSlot K h) :=
  tensorLineCore
    (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s))
    (productLineCore (twistedProjectiveDimensions K h) (some none))

def twistedHyperplaneSumCore := finiteLineSumCore (twistedHyperplaneLineCore K h)

theorem twistedHyperplaneSum_finrank (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    Module.finrank ℂ ((twistedHyperplaneSumCore K h).Fiber P) = h + ∑ i, K i := by
  change Module.finrank ℂ (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) = _
  simp

theorem twistedHyperplaneLines_unitary : LineCoreIsUnitary (twistedHyperplaneLineCore K h) :=
  tensorLineSum_unitary _ _
    (fun s => productLineCore_unitary _ (twistedOldLabel K h s))
    (fun _ => productLineCore_unitary _ (some none))

def twistedCoordinateSection (i : Option ι)
    (j : Fin (1 + twistedProjectiveDimensions K h i))
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (productLineCore (twistedProjectiveDimensions K h) (some i)).Fiber P :=
  hyperplaneFunctionalSection (coordinateFunctional j)
    (projectiveProjectionMap (twistedProjectiveDimensions K h i) (P i))

omit [Fintype ι] in
theorem continuous_twistedCoordinateSection (i : Option ι)
    (j : Fin (1 + twistedProjectiveDimensions K h i)) :
    Continuous (fun P => TotalSpace.mk' ℂ P (twistedCoordinateSection K h i j P)) := by
  have hsec := continuous_pullbackLineCore_section (projectionDualLineCore _)
    (projectiveProjectionMap (twistedProjectiveDimensions K h i))
    (hyperplaneFunctionalSection (coordinateFunctional j))
    (continuous_hyperplaneFunctionalSection _)
  exact continuous_pullbackLineCore_section (projectiveHyperplaneCore _)
    ⟨fun P : ProjectiveProduct (twistedProjectiveDimensions K h) => P i, continuous_apply i⟩ _ hsec

def twistedOldSection (s : TwistedHyperplaneSlot K h)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P :=
  match s with
  | .inl _ => (1 : ℂ)
  | .inr s => twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2) P

def twistedNewSection (s : TwistedHyperplaneSlot K h)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (productLineCore (twistedProjectiveDimensions K h) (some none)).Fiber P :=
  match s with
  | .inl j => twistedCoordinateSection K h none (positiveCoordinate h j) P
  | .inr _ => twistedCoordinateSection K h none 0 P

omit [Fintype ι] in
theorem continuous_twistedOldSection (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P (twistedOldSection K h s P)) := by
  cases s with
  | inl j =>
    apply continuous_iff_continuousAt.mpr
    intro P
    rw [FiberBundle.continuousAt_section]
    exact continuousAt_const
  | inr s => exact continuous_twistedCoordinateSection K h _ _

omit [Fintype ι] in
theorem continuous_twistedNewSection (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P (twistedNewSection K h s P)) := by
  cases s <;> exact continuous_twistedCoordinateSection K h _ _

/-- A concrete section: auxiliary positive coordinates on the h trivial
summands, and old positive coordinates multiplied by auxiliary coordinate 0
on the other summands. Its topological nonvanishing remains to be proved. -/
def twistedHyperplaneSection (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  WithLp.toLp 2 (fun s => tensorLinePair _ _ P (twistedOldSection K h s P) (twistedNewSection K h s P))

theorem continuous_twistedHyperplaneSection :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedHyperplaneSection K h P)) := by
  apply (continuous_finiteLineSum_iff (twistedHyperplaneLineCore K h) _).mpr
  exact ⟨continuous_id, fun s => continuous_tensorLinePair_section _ _
    (twistedOldSection K h s) (twistedNewSection K h s)
    (continuous_twistedOldSection K h s) (continuous_twistedNewSection K h s)⟩

end

open ComplexGrassmann

theorem hyperplaneFirstCoordinateSection_ne_zero (k : ℕ) :
    hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+k)))
      (firstCoordinateProjection k) ≠ 0 := by
  let v : projectionLine (firstCoordinateProjection k) := ⟨firstCoordinateVector k, by
    rw [firstCoordinateProjection_line]
    exact Submodule.subset_span (Set.mem_singleton _)⟩
  intro hz
  have he := congrArg (fun z => projectionDualLineFiberEquiv (firstCoordinateProjection k) z v) hz
  rw [hyperplaneFunctionalSection_realization, map_zero] at he
  simp [v,coordinateFunctional,firstCoordinateVector] at he

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

omit [Fintype ι] in
theorem twistedCoordinateSection_positive_zero_iff
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) (i : Option ι) :
    (∀ j : Fin (twistedProjectiveDimensions K h i),
      twistedCoordinateSection K h i (positiveCoordinate _ j) P = 0) ↔
      P i = firstCoordinateProduct (twistedProjectiveDimensions K h) i := by
  change (∀ j, hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate _ j))
    (projectiveProjectionMap _ (P i)) = 0) ↔ _
  rw [hyperplaneCoordinateSections_common_zero]
  constructor
  · intro hp
    have he := congrArg (projectiveProjectionEquiv (twistedProjectiveDimensions K h i)) hp
    simpa [projectiveProjectionMap, firstCoordinateProduct] using he
  · intro hp
    rw [hp]
    exact (projectiveProjectionEquiv _).symm_apply_apply _

/-- The explicit twisted section has exactly one zero on the actual
augmented projective product. This is geometry, not a nonzero Euler map. -/
theorem twistedHyperplaneSection_eq_zero_iff
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    twistedHyperplaneSection K h P = 0 ↔
      P = firstCoordinateProduct (twistedProjectiveDimensions K h) := by
  constructor
  · intro hz
    have hnew : P none = firstCoordinateProduct (twistedProjectiveDimensions K h) none := by
      apply (twistedCoordinateSection_positive_zero_iff K h P none).mp
      intro j
      have he := congrArg (fun v : (twistedHyperplaneSumCore K h).Fiber P =>
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v) (.inl j)) hz
      change (1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) P) = 0 at he
      change (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) P) = 0
      exact (one_mul (show ℂ from twistedCoordinateSection K h none
        (positiveCoordinate h j) P)).symm.trans he
    have hnew0 : twistedCoordinateSection K h none 0 P ≠ 0 := by
      change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
        (projectiveProjectionMap h (P none)) ≠ 0
      rw [hnew]
      change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
        ((projectiveProjectionEquiv h).symm
          (projectiveProjectionEquiv h (firstCoordinateProjection h))) ≠ 0
      rw [Equiv.symm_apply_apply]
      exact hyperplaneFirstCoordinateSection_ne_zero h
    funext i
    cases i with
    | none => exact hnew
    | some i =>
      apply (twistedCoordinateSection_positive_zero_iff K h P (some i)).mp
      intro j
      have he := congrArg (fun v : (twistedHyperplaneSumCore K h).Fiber P =>
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v) (.inr ⟨i,j⟩)) hz
      change (show ℂ from twistedCoordinateSection K h (some i) (positiveCoordinate (K i) j) P) *
        (show ℂ from twistedCoordinateSection K h none 0 P) = 0 at he
      exact (mul_eq_zero.mp he).resolve_right hnew0
  · rintro rfl
    change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
      twistedHyperplaneSection K h (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0
    ext s
    cases s with
    | inl j =>
      have he := (twistedCoordinateSection_positive_zero_iff K h
        (firstCoordinateProduct (twistedProjectiveDimensions K h)) none).mpr rfl j
      change (1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0
      change (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0 at he
      exact (congrArg (fun z : ℂ => 1*z) he).trans (mul_zero _)
    | inr s =>
      have he := (twistedCoordinateSection_positive_zero_iff K h
        (firstCoordinateProduct (twistedProjectiveDimensions K h)) (some s.1)).mpr rfl s.2
      change (show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) * _ = 0
      change (show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0 at he
      exact (congrArg (fun z : ℂ => z * (show ℂ from twistedNewSection K h (.inr s)
        (firstCoordinateProduct (twistedProjectiveDimensions K h)))) he).trans (zero_mul _)

end Kaplansky

end

section
open Bundle Topology Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ)
  (U : Set (ProjectiveProduct K)) (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (K i))
  (hF : U ⊆ (projectiveProductGraphChart K F).source)

def productGraphLineProjection (i : ι) : C(A,projectionSpace (1+K i) 1) :=
  (projectiveProjectionMap (K i)).comp
    ((⟨fun P : ProjectiveProduct K => P i,continuous_apply i⟩ :
      C(ProjectiveProduct K,Grassmann 1 (K i))).comp (chartBaseMap U e))

def productGraphLineVector (i : ι) (a : A) :=
  graphLineVector (F i) (slopeCoordinate (F i) ((chartBaseMap U e a) i))

omit [Fintype ι] in
theorem productGraphLineVector_mem [Fintype ι]
    (hF : U ⊆ (projectiveProductGraphChart K F).source) (i : ι) (a : A) :
    productGraphLineVector K U e F i a ∈ projectionLine (productGraphLineProjection K U e i a) := by
  have hp : InGraphChart (F i) ((chartBaseMap U e a) i).val :=
    hF (e.symm a).property i (mem_univ i)
  have he : productGraphLineProjection K U e i a =
      graphLineProjection (F i) (slopeCoordinate (F i) ((chartBaseMap U e a) i)) := by
    rw [← projectiveProjectionEquiv_symm_slopePoint,slopePoint_coordinate _ _ hp]
    rfl
  rw [he]
  exact graphLineVector_mem _ _

omit [Fintype ι] in
theorem productGraphLineVector_ne_zero (i : ι) (a : A) :
    productGraphLineVector K U e F i a ≠ 0 := graphLineVector_ne_zero _ _

omit [Fintype ι] in
theorem continuous_productGraphLineVector [Fintype ι]
    (hF : U ⊆ (projectiveProductGraphChart K F).source) (i : ι) :
    Continuous (productGraphLineVector K U e F i) := by
  apply (continuous_graphLineVector (F i)).comp
  exact (grassmannChart (F i)).continuousOn.comp_continuous
    ((continuous_apply i).comp (chartBaseMap U e).continuous)
    (fun a => hF (e.symm a).property i (mem_univ i))

def productGraphLineEvaluation (i : ι) (a : A) :
    (pullbackLineCore (productLineCore K (some i)) (chartBaseMap U e)).Fiber a ≃ₗ[ℂ] ℂ :=
  pullbackEvaluationEquiv (productGraphLineProjection K U e i)
    (productGraphLineVector K U e F i) (productGraphLineVector_mem K U e F hF i)
    (productGraphLineVector_ne_zero K U e F i) a

/-- The graph evaluation unit also covers zero-dimensional factors. -/
def productGraphLineUnit (i : Option ι) (a : A) :
    (pullbackLineCore (productLineCore K i) (chartBaseMap U e)).Fiber a :=
  match i with
  | none => (1 : ℂ)
  | some i => (productGraphLineEvaluation K U e F hF i a).symm 1

theorem productGraphLineUnit_ne_zero (i : Option ι) (a : A) :
    productGraphLineUnit K U e F hF i a ≠ 0 := by
  cases i with
  | none => exact (one_ne_zero : (1 : ℂ) ≠ 0)
  | some i => exact fun hz => one_ne_zero ((productGraphLineEvaluation K U e F hF i a).symm.map_eq_zero_iff.mp hz)

theorem continuous_productGraphLineUnit (i : Option ι) :
    Continuous (fun a => TotalSpace.mk' ℂ a (productGraphLineUnit K U e F hF i a)) := by
  cases i with
  | none =>
    apply continuous_iff_continuousAt.mpr
    intro a
    rw [FiberBundle.continuousAt_section]
    exact continuousAt_const
  | some i =>
    exact (hyperplaneEvaluationHomeomorph (productGraphLineProjection K U e i)
      (productGraphLineVector K U e F i) (productGraphLineVector_mem K U e F hF i)
      (productGraphLineVector_ne_zero K U e F i) (continuous_productGraphLineVector K U e F hF i)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)

end Kaplansky

end

section
open Bundle Topology Set CategoryTheory
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
  (hF : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source)

instance twistedHyperplaneFiberNormedAddCommGroup
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    NormedAddCommGroup ((twistedHyperplaneSumCore K h).Fiber P) :=
  finiteLineSumFiberNormedAddCommGroup (twistedHyperplaneLineCore K h) P

instance twistedHyperplaneFiberInnerProductSpace
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    InnerProductSpace ℂ ((twistedHyperplaneSumCore K h).Fiber P) :=
  finiteLineSumFiberInnerProductSpace (twistedHyperplaneLineCore K h) P

abbrev twistedGraphBundleDomain :=
  {z : TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
    (twistedHyperplaneSumCore K h).Fiber | z.proj ∈ U}

def twistedGraphLineUnit (s : TwistedHyperplaneSlot K h) (a : A) :
    (pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e)).Fiber a :=
  tensorLinePair
    (pullbackLineCore (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)) (chartBaseMap U e))
    (pullbackLineCore (productLineCore (twistedProjectiveDimensions K h) (some none)) (chartBaseMap U e)) a
    (productGraphLineUnit (twistedProjectiveDimensions K h) U e F hF (twistedOldLabel K h s) a)
    (productGraphLineUnit (twistedProjectiveDimensions K h) U e F hF (some none) a)

theorem twistedGraphLineUnit_ne_zero (s : TwistedHyperplaneSlot K h) (a : A) :
    twistedGraphLineUnit K h U e F hF s a ≠ 0 :=
  tensorLinePair_ne_zero _ _ _ _ _
    (productGraphLineUnit_ne_zero _ _ _ _ _ _ _) (productGraphLineUnit_ne_zero _ _ _ _ _ _ _)

theorem continuous_twistedGraphLineUnit (s : TwistedHyperplaneSlot K h) :
    Continuous (fun a => TotalSpace.mk' ℂ a (twistedGraphLineUnit K h U e F hF s a)) := by
  exact continuous_tensorLinePair_section _ _ _ _
    (continuous_productGraphLineUnit _ _ _ _ _ _) (continuous_productGraphLineUnit _ _ _ _ _ _)

/-- Genuine linear coordinates for the original twisted bundle, over
any subset of any product graph chart. -/
def twistedGraphBundleCoordinates : twistedGraphBundleDomain K h U ≃ₜ
    A × (TwistedHyperplaneSlot K h → ℂ) :=
  (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm.trans
    (finiteLineFrameHomeomorph
      (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
      (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
      (continuous_twistedGraphLineUnit K h U e F hF))

theorem twistedGraphBundleCoordinates_base (z : twistedGraphBundleDomain K h U) :
    (twistedGraphBundleCoordinates K h U e F hF z).1 = e ⟨z.1.proj,z.2⟩ := rfl

theorem twistedGraphBundleCoordinates_zero_iff (z : twistedGraphBundleDomain K h U) :
    (twistedGraphBundleCoordinates K h U e F hF z).2 = 0 ↔ z.1.2 = 0 :=
  (finiteLineFrameEquiv _ (twistedGraphLineUnit K h U e F hF)
    (twistedGraphLineUnit_ne_zero K h U e F hF) _).map_eq_zero_iff

def twistedGraphBundleRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (twistedGraphBundleCoordinates K h U e F hF)
    (Subtype.val ⁻¹' nonzeroBundle) {z : A × (TwistedHyperplaneSlot K h → ℂ) | z.2 ≠ 0}
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K h U e F hF z)).symm) n

def twistedGraphBundleNormalization (n : ℕ) :=
  (twistedGraphBundleRelativeIso K h U e F hF n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

theorem div_linearEquiv_inverse_one (L : ℂ ≃ₗ[ℂ] ℂ) (z : ℂ) :
    z / L.symm 1 = L z := by
  have hn : L.symm 1 ≠ 0 := fun hz => one_ne_zero (L.symm.map_eq_zero_iff.mp hz)
  apply (div_eq_iff hn).mpr
  have he := L.symm.map_smul (L z) (1 : ℂ)
  change L.symm (L z * 1) = L z * L.symm 1 at he
  simpa only [mul_one, L.symm_apply_apply] using he

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSlotEquiv : TwistedHyperplaneSlot K h ≃
    (Σ i, Fin (twistedProjectiveDimensions K h i)) where
  toFun
    | .inl j => ⟨none,j⟩
    | .inr s => ⟨some s.1,s.2⟩
  invFun
    | ⟨none,j⟩ => .inl j
    | ⟨some i,j⟩ => .inr ⟨i,j⟩
  left_inv s := by cases s <;> rfl
  right_inv s := by obtain ⟨i,j⟩ := s; cases i <;> rfl

def twistedSlopeEvaluationEquiv : ProjectiveProductModel (twistedProjectiveDimensions K h) ≃L[ℂ]
    (TwistedHyperplaneSlot K h → ℂ) :=
  (productSlopeEvaluationEquiv (twistedProjectiveDimensions K h)).trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (twistedSlotEquiv K h).symm).toContinuousLinearEquiv

def twistedStandardFrames (i : Option ι) := standardLineGraphFrame (twistedProjectiveDimensions K h i)

abbrev twistedStandardChart := canonicalProductGraphChart (twistedProjectiveDimensions K h)
abbrev twistedStandardChartHomeomorph := canonicalProductChartHomeomorph (twistedProjectiveDimensions K h)

def twistedStandardLineUnit (s : TwistedHyperplaneSlot K h)
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :=
  twistedGraphLineUnit K h (twistedStandardChart K h).source
    (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl s A

/-- Actual section coordinates in the proved tensor graph trivialization. -/
def twistedStandardSectionCoordinates
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) : TwistedHyperplaneSlot K h → ℂ :=
  fun s => (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
    twistedHyperplaneSection K h (canonicalProductGraphPoint (twistedProjectiveDimensions K h) A)) s /
    (show ℂ from twistedStandardLineUnit K h s A)

theorem twistedStandard_coordinate_evaluation
    (i : Option ι) (j : Fin (1+twistedProjectiveDimensions K h i))
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :
    (show ℂ from twistedCoordinateSection K h i j
        (canonicalProductGraphPoint (twistedProjectiveDimensions K h) A)) /
      (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl (some i) A) =
      coordinateFunctional j (graphLineVector (twistedStandardFrames K h i) (A i)) := by
  rw [show (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl (some i) A) =
      (show ℂ ≃ₗ[ℂ] ℂ from productGraphLineEvaluation (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl i A).symm 1 from rfl,
    div_linearEquiv_inverse_one]
  change projectionDualLineFiberEquiv _ (hyperplaneFunctionalSection (coordinateFunctional j) _)
    ⟨productGraphLineVector (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) i A,_⟩ = _
  rw [hyperplaneFunctionalSection_realization]
  change coordinateFunctional j (graphLineVector (twistedStandardFrames K h i)
    (slopeCoordinate (twistedStandardFrames K h i) (slopePoint (twistedStandardFrames K h i) (A i)))) = _
  rw [slopeCoordinate_point]

theorem twistedStandardSectionCoordinates_eq
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :
    twistedStandardSectionCoordinates K h A = twistedSlopeEvaluationEquiv K h A := by
  funext s
  cases s with
  | inl j =>
    change ((1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) _)) /
      (1 * (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some none) A)) = A none (fun _ => 1) j
    rw [one_mul, one_mul]
    refine (twistedStandard_coordinate_evaluation K h none (positiveCoordinate h j) A).trans ?_
    exact (congrArg (fun f : EuclideanSpace ℂ (Fin (1+h)) →ₗ[ℂ] ℂ =>
      f (graphLineVector (standardLineGraphFrame h) (A none)))
      (standard_verticalFunctional h j).symm).trans
        (graphVerticalFunctional_vector (standardLineGraphFrame h) (A none) j)
  | inr s =>
    change ((show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2) _) *
      (show ℂ from twistedCoordinateSection K h none 0 _)) /
      ((show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some (some s.1)) A) *
       (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some none) A)) = A (some s.1) (fun _ => 1) s.2
    rw [mul_div_mul_comm]
    refine (congrArg₂ (fun x y : ℂ => x * y)
      (twistedStandard_coordinate_evaluation K h (some s.1) (positiveCoordinate (K s.1) s.2) A)
      (twistedStandard_coordinate_evaluation K h none 0 A)).trans ?_
    have hzero : coordinateFunctional (0 : Fin (1+h))
        (graphLineVector (standardLineGraphFrame h) (A none)) = 1 := by
      change (graphLineVector (standardLineGraphFrame h) (A none)) 0 = 1
      have he := graphLineVector_coordinates (standardLineGraphFrame h) (show GraphSlope 1 h from A none)
      have hh := congrArg (fun v => (standardLineGraphFrame h v).1 (0 : Fin 1)) he
      simp only [standardLineGraphFrame_horizontal,LinearEquiv.apply_symm_apply] at hh
      exact hh
    change coordinateFunctional (positiveCoordinate (K s.1) s.2)
      (graphLineVector (standardLineGraphFrame (K s.1)) (A (some s.1))) *
      coordinateFunctional (0 : Fin (1+h)) (graphLineVector (standardLineGraphFrame h) (A none)) = _
    rw [hzero,mul_one,← standard_verticalFunctional]
    exact graphVerticalFunctional_vector (standardLineGraphFrame (K s.1)) (A (some s.1)) s.2

theorem twistedStandardSection_regular_zero :
    HasFDerivAt (twistedStandardSectionCoordinates K h)
      (twistedSlopeEvaluationEquiv K h).toContinuousLinearMap 0 ∧
      Function.Bijective (twistedSlopeEvaluationEquiv K h) := by
  have he : twistedStandardSectionCoordinates K h = twistedSlopeEvaluationEquiv K h :=
    funext (twistedStandardSectionCoordinates_eq K h)
  rw [he]
  exact ⟨(twistedSlopeEvaluationEquiv K h).toContinuousLinearMap.hasFDerivAt,
    (twistedSlopeEvaluationEquiv K h).bijective⟩

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSourceLabel : TwistedHyperplaneSlot K h → Option ι
  | .inl _ => none
  | .inr s => some s.1

def twistedSourceStage : LineStage K :=
  ⟨TwistedHyperplaneSlot K h,inferInstance,twistedSourceLabel K h⟩

def twistedOldBase : C(ProjectiveProduct (twistedProjectiveDimensions K h),ProjectiveProduct K) :=
  ⟨fun P i => P (some i),continuous_pi (fun i => continuous_apply (some i))⟩

theorem continuous_twistedOldComponent
    (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (hv : Continuous (fun y => TotalSpace.mk' (twistedSourceStage K h).Model y (v y)))
    (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P
      (show (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P from
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v (twistedOldBase K h P)) s)) := by
  have hc := ((continuous_finiteLineSumComponent
    (fun s => productLineCore K (twistedSourceLabel K h s)) s).comp hv).comp
    (twistedOldBase K h).continuous
  apply continuous_iff_continuousAt.mpr
  intro P
  rw [FiberBundle.continuousAt_section]
  have hh := (FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := P)).mp hc.continuousAt |>.2
  cases s with
  | inl j => exact hh
  | inr s => exact hh

/-- Tensor an arbitrary old section with a homogeneous auxiliary
coordinate, preserving the original bundle topologies. -/
def twistedSectionFromVector (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (j : Fin (1+h)) (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  WithLp.toLp 2 (fun s => tensorLinePair _ _ P
    (show (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P from
      (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v (twistedOldBase K h P)) s)
    (twistedCoordinateSection K h none j P))

theorem continuous_twistedSectionFromVector
    (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (hv : Continuous (fun y => TotalSpace.mk' (twistedSourceStage K h).Model y (v y)))
    (j : Fin (1+h)) :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedSectionFromVector K h v j P)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨continuous_id,fun s => ?_⟩
  exact continuous_tensorLinePair_section _ _ _ _
    (continuous_twistedOldComponent K h v hv s) (continuous_twistedCoordinateSection K h none j)

omit [Fintype ι] in
theorem twistedCoordinateSections_not_all_zero
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    ¬ (∀ j : Fin (1+h), twistedCoordinateSection K h none j P = 0) := by
  intro hz
  have hp := (twistedCoordinateSection_positive_zero_iff K h P none).mp
    (fun j => hz (positiveCoordinate h j))
  have he := hz 0
  change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
    (projectiveProjectionMap h (P none)) = 0 at he
  rw [hp] at he
  change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
    ((projectiveProjectionEquiv h).symm (projectiveProjectionEquiv h (firstCoordinateProjection h))) = 0 at he
  rw [Equiv.symm_apply_apply] at he
  exact hyperplaneFirstCoordinateSection_ne_zero h he

variable {d : ℕ}

def twistedFrameSection (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d)
    (hd : 1+h ≤ d) (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  ∑ j : Fin (1+h), twistedSectionFromVector K h
    (fun y => f.vector y (Fin.castLE hd j)) j P

theorem continuous_twistedFrameSection
    (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) (hd : 1+h ≤ d) :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedFrameSection K h f hd P)) := by
  apply continuousOn_univ.mp
  apply continuousOn_bundle_sum (𝕜 := ℂ)
  intro j _
  exact (continuous_twistedSectionFromVector K h _ (f.continuous_vector _) j).continuousOn

theorem twistedFrameSection_ne_zero
    (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) (hd : 1+h ≤ d)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    twistedFrameSection K h f hd P ≠ 0 := by
  intro hz
  have hind := (f.orthonormal (twistedOldBase K h P)).linearIndependent.comp
    (Fin.castLE hd) (Fin.castLE_injective hd)
  have he : (∑ j : Fin (1+h),
      (show ℂ from twistedCoordinateSection K h none j P) •
        f.vector (twistedOldBase K h P) (Fin.castLE hd j)) = 0 := by
    change (∑ j : Fin (1+h),
      (show ℂ from twistedCoordinateSection K h none j P) •
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
          f.vector (twistedOldBase K h P) (Fin.castLE hd j))) = 0
    change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
      twistedFrameSection K h f hd P) = 0 at hz
    convert hz using 1
    apply Finset.sum_congr rfl
    intro j _
    ext s
    exact mul_comm _ _
  have hc := Fintype.linearIndependent_iff.mp hind _ he
  exact twistedCoordinateSections_not_all_zero K h P hc

end Kaplansky

end

end OAI
