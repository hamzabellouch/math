import Mathlib
import OAI.Geometry.Borsuk.Support.BalancedChart
import OAI.Geometry.Borsuk.LocalParity.RegularBase
import OAI.Geometry.Borsuk.MatrixGeometry.BlockLine
import OAI.Geometry.Borsuk.LocalParity.RegularPatch

namespace OAI

open Set MeasureTheory
namespace BorsukNine
noncomputable def raySet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) : Set E :=
  {v | v = (‖v‖ / ‖y‖) • y}
lemma raySet_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) :
    IsClosed (raySet y) := isClosed_eq continuous_id ((continuous_norm.div_const _).smul continuous_const)
lemma mem_raySet_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v y : E} (hv : v ≠ 0) (hy : y ≠ 0) : v ∈ raySet y ↔ ∃ d : ℝ, 0 < d ∧ v = d • y := by
  constructor
  · intro h
    exact ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),h⟩
  · rintro ⟨d,hd,rfl⟩
    change d • y = (‖d • y‖ / ‖y‖) • y
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd,mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hy)]
end BorsukNine

namespace BorsukNine
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixFibres
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix (Fin (k+1)) (Fin (k+1)) ℝ
local notation "T" => traceSphere (Fin (k+1))
local notation "Y" => EuclideanSpace ℝ ι
local notation "op" => Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)
noncomputable def matrixRayFibre (F : T → Y) (y : Y) (c : E) : Set T :=
  {A | F A ∈ raySet y ∧ A.val⁺ = Matrix.trace A.val⁺ • rankOne c}
omit [DecidableEq ι] in
lemma matrixRayFibre_closed (F : T → Y) (hF : Continuous F) (y : Y) (c : E) :
    IsClosed (matrixRayFibre F y c) := by
  have hp : Continuous (fun A : T => A.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1)
  exact ((raySet_isClosed y).preimage hF).inter
    (isClosed_eq hp ((matrix_trace_continuous.comp hp).smul continuous_const))
lemma Admissible.facet_support {f : E → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : W} (hz : z ∈ simplexInterior k)
    {c : E} (hc : f c = facetPoint a z) : positiveSupport f c = I := by
  ext i
  rw [mem_positiveSupport,hc]
  by_cases hi : i ∈ I
  · exact iff_of_true (facetPoint_pos a hz i hi) hi
  · rw [facetPoint_zero a z hi]
    simp [hi]
omit [DecidableEq ι] in
lemma matrixRayFibre_representative {F : T → Y} {y : Y} {w c : E} (hc : ‖c‖ = 1)
    (hwc : 0 < ⟪w,c⟫) {A : T} (hline : HasPositiveLine A.val)
    (hK : A ∈ matrixRayFibre F y c) : lineRepresentative w A.val = c :=
  lineRepresentative_split hc (hasPositiveLine_trace_pos hline) hK.2 hwc
omit [DecidableEq ι] in
lemma Admissible.matrixRayFibre_subset_patch {f : E → ι → ℝ} (_hf : Admissible f)
    {F : T → Y} {y : Y} {w c : E} (hc : ‖c‖ = 1) (hwc : 0 < ⟪w,c⟫)
    {I : Finset ι} (hp : ∀ i ∈ I, 0 < f c i)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {δ : ℝ} (hδ : 0 < δ)
    {A : T} (hK : A ∈ matrixRayFibre F y c)
    (hU : IsUnit A.val) (hline : HasPositiveLine A.val) (hAw : op A.val⁺ w ≠ 0) :
    A ∈ regularPatch f I w c e δ := by
  have hr := matrixRayFibre_representative hc hwc hline hK
  have ht := hasPositiveLine_trace_pos hline
  refine ⟨hU,hline,hAw,?_,?_,?_,?_,?_⟩
  · simpa only [hr] using hp
  · rw [hr,real_inner_self_eq_norm_sq,hc]; norm_num
  · rw [hr,hemisphereInverse,adjoint_normal c e he,smul_zero,norm_zero]
    exact hδ
  · rw [blockScalar_positiveLine A.property.1 hc ht hK.2]
    exact ht
  · exact blockCompress_negative e A.property.1 hU hc he hes ht hK.2
end MatrixFibres
end BorsukNine

end OAI
