import OAI.Analysis.MatrixScaling.Continuous
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.VectorBundle.Basic

namespace OAI

noncomputable section

/-! Hermitian frames, synthesis, and unitary transition functions. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix
namespace Kaplansky
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Change a finite frame by a matrix acting on its coefficient columns. -/
def frameMul (v : Fin d → E) (A : Matrix (Fin d) (Fin d) ℂ) : Fin d → E :=
  fun j => ∑ i, A i j • v i

theorem gram_frameMul (v : Fin d → E) (A : Matrix (Fin d) (Fin d) ℂ) :
    gram ℂ (frameMul v A) = Aᴴ * gram ℂ v * A := by
  ext i j
  simp only [gram_apply, frameMul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [← starRingEnd_apply]
  ring

/-- The inverse positive square root orthonormalizes a positive Gram matrix. -/
theorem inverse_sqrt_gram_identity {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef) :
    (CFC.sqrt G)⁻¹ᴴ * G * (CFC.sqrt G)⁻¹ = 1 := by
  obtain ⟨hu,he⟩ := matrix_sqrt_factor hG
  have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
  have hi : (CFC.sqrt G)⁻¹ᴴ = (CFC.sqrt G)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hs]
  rw [hi]
  conv_lhs => arg 1; arg 2; rw [← he, hs]
  have hl := Matrix.nonsing_inv_mul (CFC.sqrt G) ((CFC.sqrt G).isUnit_iff_isUnit_det.mp hu)
  have hr := Matrix.mul_nonsing_inv (CFC.sqrt G) ((CFC.sqrt G).isUnit_iff_isUnit_det.mp hu)
  simp only [← Matrix.mul_assoc, hl, Matrix.one_mul, hr]

def metricFrame (v : Fin d → E) : Fin d → E :=
  frameMul v (CFC.sqrt (gram ℂ v))⁻¹

theorem metricFrame_orthonormal (v : Fin d → E) (hv : LinearIndependent ℂ v) :
    Orthonormal ℂ (metricFrame v) := by
  apply Matrix.gram_eq_one_iff_orthonormal.mp
  rw [metricFrame, gram_frameMul]
  exact inverse_sqrt_gram_identity (Matrix.posDef_gram_of_linearIndependent hv)

/-- Coefficient continuity is valid on open charts by restricting the base. -/
theorem continuous_metricFrame_coefficients {Y : Type*} [TopologicalSpace Y]
    (G : Y → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hp : ∀ y, (G y).PosDef) :
    Continuous (fun y => (CFC.sqrt (G y))⁻¹) :=
  continuous_matrix_inverse _ (continuous_matrix_sqrt G hG hp)
    (fun y => (matrix_sqrt_factor (hp y)).1)

theorem frameMul_mul (v : Fin d → E) (A B : Matrix (Fin d) (Fin d) ℂ) :
    frameMul (frameMul v A) B = frameMul v (A * B) := by
  funext j
  simp only [frameMul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem frameMul_one (v : Fin d → E) : frameMul v 1 = v := by
  classical
  funext j
  simp [frameMul, Matrix.one_apply]

theorem span_frameMul_le (v : Fin d → E) (A : Matrix (Fin d) (Fin d) ℂ) :
    Submodule.span ℂ (Set.range (frameMul v A)) ≤ Submodule.span ℂ (Set.range v) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

theorem span_metricFrame (v : Fin d → E) (hv : LinearIndependent ℂ v) :
    Submodule.span ℂ (Set.range (metricFrame v)) = Submodule.span ℂ (Set.range v) := by
  apply le_antisymm (span_frameMul_le v _)
  have hu := (matrix_sqrt_factor (Matrix.posDef_gram_of_linearIndependent hv)).1
  have he : frameMul (metricFrame v) (CFC.sqrt (gram ℂ v)) = v := by
    rw [metricFrame, frameMul_mul, Matrix.nonsing_inv_mul _
      ((CFC.sqrt (gram ℂ v)).isUnit_iff_isUnit_det.mp hu), frameMul_one]
  calc
    Submodule.span ℂ (Set.range v) =
        Submodule.span ℂ (Set.range (frameMul (metricFrame v) (CFC.sqrt (gram ℂ v)) )) := by rw [he]
    _ ≤ _ := span_frameMul_le _ _

/-- An ordinary linear basis supplies the complete orthonormal basis;
no orthonormal-frame existence hypothesis is used. -/
def metricBasis (b : Module.Basis (Fin d) ℂ E) : OrthonormalBasis (Fin d) ℂ E :=
  OrthonormalBasis.mk (metricFrame_orthonormal b b.linearIndependent)
    (by rw [span_metricFrame b b.linearIndependent, b.span_eq])

theorem metricBasis_apply (b : Module.Basis (Fin d) ℂ E) (i : Fin d) :
    metricBasis b i = metricFrame b i := by
  simp only [metricBasis, OrthonormalBasis.coe_mk]

end Kaplansky

end

section
open scoped BigOperators InnerProductSpace
namespace Kaplansky
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def frameSynthesis (v : Fin d → E) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E where
  toFun x := ∑ i, x i • v i
  map_add' x y := by simp [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [PiLp.smul_apply,Finset.smul_sum,smul_smul]

def frameAnalysis (v : Fin d → E) : E →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun x := WithLp.toLp 2 (fun i => inner ℂ (v i) x)
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' c x := by ext i; simp [inner_smul_right]

theorem frameAnalysis_synthesis (v : Fin d → E) (hv : Orthonormal ℂ v)
    (x : EuclideanSpace ℂ (Fin d)) : frameAnalysis v (frameSynthesis v x)=x := by
  ext i
  exact hv.inner_right_sum (fun j => x j) (Finset.mem_univ i)

theorem frameSynthesis_mem_span (v : Fin d → E) (x : EuclideanSpace ℂ (Fin d)) :
    frameSynthesis v x ∈ Submodule.span ℂ (Set.range v) := by
  change (∑ i, x i • v i) ∈ Submodule.span ℂ (Set.range v)
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ (x i) (Submodule.subset_span (show v i ∈ Set.range v from ⟨i,rfl⟩)))

theorem frameSynthesis_analysis (v : Fin d → E) (hv : Orthonormal ℂ v)
    {x : E} (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    frameSynthesis v (frameAnalysis v x)=x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    change (∑ j, inner ℂ (v j) (v i) • v j)=v i
    simp [orthonormal_iff_ite.mp hv]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx,ihy]
  | smul c x hx ih => simp [ih]

def frameSpanEquiv (v : Fin d → E) (hv : Orthonormal ℂ v) :
    EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] Submodule.span ℂ (Set.range v) where
  toFun x := ⟨frameSynthesis v x,frameSynthesis_mem_span v x⟩
  invFun x := frameAnalysis v x
  map_add' x y := Subtype.ext (map_add (frameSynthesis v) x y)
  map_smul' c x := Subtype.ext (map_smul (frameSynthesis v) c x)
  left_inv := frameAnalysis_synthesis v hv
  right_inv x := Subtype.ext (frameSynthesis_analysis v hv x.property)

theorem frameSpan_finrank (v : Fin d → E) (hv : Orthonormal ℂ v) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range v))=d := by
  rw [← (frameSpanEquiv v hv).finrank_eq]
  simp

end Kaplansky

end

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Bundle Topology
namespace Kaplansky
variable {d : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E : Y → Type*} [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]

/-- Continuity of a Hermitian metric, expressed by its values on local
continuous sections of an ordinary complex vector bundle. -/
def ContinuousHermitianMetric : Prop :=
  ∀ (s : Set Y) (v w : ∀ y, E y),
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (v y)) s →
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (w y)) s →
    ContinuousOn (fun y => inner ℂ (v y) (w y)) s

/-- The ordinary frame obtained from a linear trivialization. -/
def bundleChartFrame (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (i : Fin d) : E y :=
  e.symmₗ ℂ y (Pi.single i 1)

def bundleChartBasis (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) : Module.Basis (Fin d) ℂ (E y) :=
  (Pi.basisFun ℂ (Fin d)).map (e.linearEquivAt ℂ y hy).symm

theorem bundleChartBasis_apply (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) (i : Fin d) :
    bundleChartBasis e y hy i = bundleChartFrame e y i := by
  simp [bundleChartBasis, bundleChartFrame, hy]

theorem bundleChartFrame_independent (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) :
    LinearIndependent ℂ (bundleChartFrame e y) := by
  have he : (bundleChartBasis e y hy : Fin d → E y) = bundleChartFrame e y :=
    funext (bundleChartBasis_apply e y hy)
  rw [← he]
  exact (bundleChartBasis e y hy).linearIndependent

theorem continuousOn_bundleChartFrame
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (i : Fin d) :
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (bundleChartFrame e y i)) e.baseSet := by
  have hc := e.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
    (show Set.MapsTo (fun y : Y => (y, (Pi.single i (1 : ℂ) : Fin d → ℂ))) e.baseSet
      (e.baseSet ×ˢ Set.univ) from fun y hy => ⟨hy, Set.mem_univ _⟩)
  apply hc.congr
  intro y hy
  simp [bundleChartFrame, hy, Trivialization.mk_symm]

theorem continuousOn_bundleGram
    (hm : ContinuousHermitianMetric (d := d) (E := E))
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] :
    ContinuousOn (fun y => gram ℂ (bundleChartFrame e y)) e.baseSet := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact hm e.baseSet (fun y => bundleChartFrame e y i) (fun y => bundleChartFrame e y j)
    (continuousOn_bundleChartFrame e i) (continuousOn_bundleChartFrame e j)

/-- The actual orthonormal frame on the chart, extended by zero outside. -/
def bundleOrthonormalFrame
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (y : Y) : Fin d → E y :=
  metricFrame (bundleChartFrame e y)

theorem bundleOrthonormalFrame_eq
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (y : Y) (j : Fin d) :
    bundleOrthonormalFrame e y j =
      e.symmₗ ℂ y (fun i => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹ i j) := by
  unfold bundleOrthonormalFrame metricFrame frameMul bundleChartFrame
  simp only [← map_smul, ← map_sum]
  congr 1
  classical
  ext k
  simp [Pi.single_apply]

theorem bundleOrthonormalFrame_orthonormal
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ]
    (y : Y) (hy : y ∈ e.baseSet) : Orthonormal ℂ (bundleOrthonormalFrame e y) :=
  metricFrame_orthonormal _ (bundleChartFrame_independent e y hy)

def bundleOrthonormalBasis
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ]
    (y : Y) (hy : y ∈ e.baseSet) : OrthonormalBasis (Fin d) ℂ (E y) :=
  metricBasis (bundleChartBasis e y hy)

theorem bundleOrthonormalBasis_apply
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ]
    (y : Y) (hy : y ∈ e.baseSet) (i : Fin d) :
    bundleOrthonormalBasis e y hy i = bundleOrthonormalFrame e y i := by
  rw [bundleOrthonormalBasis, metricBasis_apply]
  congr 2
  funext j
  exact bundleChartBasis_apply e y hy j

theorem continuousOn_bundleOrthonormalFrame
    (hm : ContinuousHermitianMetric (d := d) (E := E))
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (j : Fin d) :
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (bundleOrthonormalFrame e y j))
      e.baseSet := by
  have hG := continuousOn_bundleGram hm e
  have hc : ContinuousOn (fun y => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹) e.baseSet := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_metricFrame_coefficients _
      (continuousOn_iff_continuous_domRestrict.mp hG)
      (fun y => Matrix.posDef_gram_of_linearIndependent (bundleChartFrame_independent e y y.property))
  have hv : ContinuousOn (fun y i => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹ i j)
      e.baseSet := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hh := e.continuousOn_symm.comp (continuousOn_id.prodMk hv)
    (show Set.MapsTo (fun y => (y, fun i => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹ i j))
      e.baseSet (e.baseSet ×ˢ Set.univ) from fun y hy => ⟨hy, Set.mem_univ _⟩)
  apply hh.congr
  intro y hy
  simp [bundleOrthonormalFrame_eq, hy]

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Bundle Topology
namespace Kaplansky
variable {d : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E : Y → Type*} [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]

/-- Transition from the orthonormalization of chart a to that of chart b. -/
def bundleUnitaryTransition
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => inner ℂ (bundleOrthonormalFrame b y i) (bundleOrthonormalFrame a y j)

theorem bundleUnitaryTransition_eq
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
    bundleUnitaryTransition a b y =
      (bundleOrthonormalBasis b y hb).toBasis.toMatrix (bundleOrthonormalBasis a y ha) := by
  ext i j
  simp only [bundleUnitaryTransition, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    bundleOrthonormalBasis_apply]

theorem bundleUnitaryTransition_unitary
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
    (bundleUnitaryTransition a b y)ᴴ * bundleUnitaryTransition a b y = 1 ∧
      bundleUnitaryTransition a b y * (bundleUnitaryTransition a b y)ᴴ = 1 := by
  rw [bundleUnitaryTransition_eq a b y ha hb]
  exact ⟨OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self _ _,
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose _ _⟩

theorem bundleUnitaryTransition_self
    (a : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) : bundleUnitaryTransition a a y = 1 := by
  rw [bundleUnitaryTransition_eq a a y ha ha]
  exact (bundleOrthonormalBasis a y ha).toBasis.toMatrix_self

theorem bundleUnitaryTransition_comp
    (a b c : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [a.IsLinear ℂ] [b.IsLinear ℂ] [c.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) (hc : y ∈ c.baseSet) :
    bundleUnitaryTransition b c y * bundleUnitaryTransition a b y =
      bundleUnitaryTransition a c y := by
  rw [bundleUnitaryTransition_eq b c y hb hc, bundleUnitaryTransition_eq a b y ha hb,
    bundleUnitaryTransition_eq a c y ha hc]
  exact Module.Basis.toMatrix_mul_toMatrix
    (bundleOrthonormalBasis c y hc).toBasis (bundleOrthonormalBasis b y hb).toBasis
    (bundleOrthonormalBasis a y ha)

theorem continuousOn_bundleUnitaryTransition
    (hm : ContinuousHermitianMetric (d := d) (E := E))
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ] :
    ContinuousOn (bundleUnitaryTransition a b) (a.baseSet ∩ b.baseSet) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact hm _ (fun y => bundleOrthonormalFrame b y i) (fun y => bundleOrthonormalFrame a y j)
    ((continuousOn_bundleOrthonormalFrame hm b i).mono Set.inter_subset_right)
    ((continuousOn_bundleOrthonormalFrame hm a j).mono Set.inter_subset_left)

end Kaplansky

end

end OAI
