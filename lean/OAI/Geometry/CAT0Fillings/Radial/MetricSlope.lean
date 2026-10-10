import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.MetricDerivative
import OAI.Geometry.CAT0Fillings.Radial.UniformSlope

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix Set Metric
open scoped BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev MetricRadialParameters (ι : Type*) := Matrix ι ι ℝ × RadialParameters ι

def metricSpatialRadialSlope (t : ℝ) (p : MetricRadialParameters ι) : Matrix ι ι ℝ :=
  (-2*p.2.1.1+t*p.2.1.1^2) • p.1-
    ((1-t*p.2.1.1)*p.2.1.2) • (vecMulVec p.2.2.1 p.2.2.2+vecMulVec p.2.2.2 p.2.2.1)+
      (t*p.2.1.2^2) • vecMulVec p.2.2.2 p.2.2.2

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_metricSpatialRadialSlope :
    Continuous (fun q : ℝ × MetricRadialParameters ι => metricSpatialRadialSlope q.1 q.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [metricSpatialRadialSlope,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
lemma metricSpatialRadialForm_sub_original (t : ℝ) (p : MetricRadialParameters ι) :
    metricSpatialRadialForm p.1 p.2.1.1 p.2.1.2 t p.2.2.1 p.2.2.2-p.1 =
      t • metricSpatialRadialSlope t p := by
  ext i j
  simp only [metricSpatialRadialForm,metricSpatialRadialSlope,Matrix.add_apply,
    Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  ring

theorem metricSpatialRadialForm_uniform_slope_bound (B δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : MetricRadialParameters ι, ‖p‖ ≤ B → δ ≤ p.1.det →
      ∀ t ∈ Icc (0:ℝ) 1,
        |Real.sqrt (metricSpatialRadialForm p.1 p.2.1.1 p.2.1.2 t p.2.2.1 p.2.2.2).det /
          Real.sqrt p.1.det-1| ≤ C*t := by
  let K : Set (ℝ × MetricRadialParameters ι) := Icc (0:ℝ) 1 ×ˢ closedBall 0 B
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 B)
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (f := fun q : ℝ × MetricRadialParameters ι => (fun i j => metricSpatialRadialSlope q.1 q.2 i j))
    continuous_metricSpatialRadialSlope.continuousOn
  let R : ℝ := max D 0
  let V : ℝ := max B 0
  have hR : 0 ≤ R := le_max_right _ _
  have hV : 0 ≤ V := le_max_right _ _
  let detM : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    ⟨Matrix.detRowAlternating.toMultilinearMap,continuous_id.matrix_det⟩
  let D' := ‖detM‖*(Fintype.card ι : ℝ)*(R+V)^(Fintype.card ι-1)*R
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  refine ⟨D'/δ,div_nonneg hD' hδ.le,?_⟩
  intro p hp hdet t ht
  have hQ : ‖metricSpatialRadialSlope t p‖ ≤ R :=
    (hD (t,p) ⟨ht,by simpa only [mem_closedBall,dist_zero_right] using hp⟩).trans (le_max_left _ _)
  let A := metricSpatialRadialForm p.1 p.2.1.1 p.2.1.2 t p.2.2.1 p.2.2.2
  have hdiff : ‖A-p.1‖ ≤ R*t := by
    rw [show A-p.1 = t • metricSpatialRadialSlope t p from metricSpatialRadialForm_sub_original t p,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hQ ht.1
  have hG : ‖p.1‖ ≤ V := (norm_fst_le p).trans (hp.trans (le_max_left _ _))
  have hA : ‖A‖ ≤ R+V := by
    have hh := norm_add_le (A-p.1) p.1
    rw [sub_add_cancel] at hh
    have hRt : R*t ≤ R := (mul_le_mul_of_nonneg_left ht.2 hR).trans_eq (mul_one R)
    linarith
  have hmax : max ‖A‖ ‖p.1‖ ≤ R+V := max_le hA (by linarith)
  have hh := detM.norm_image_sub_le (fun i j => A i j) (fun i j => p.1 i j)
  change ‖A.det-p.1.det‖ ≤
    ‖detM‖*(Fintype.card ι : ℝ)*max ‖A‖ ‖p.1‖^(Fintype.card ι-1)*‖A-p.1‖ at hh
  rw [Real.norm_eq_abs] at hh
  have hb : |A.det-p.1.det| ≤ D'*t := by
    calc
      _ ≤ ‖detM‖*(Fintype.card ι : ℝ)*max ‖A‖ ‖p.1‖^(Fintype.card ι-1)*‖A-p.1‖ := hh
      _ ≤ ‖detM‖*(Fintype.card ι : ℝ)*(R+V)^(Fintype.card ι-1)*(R*t) := by gcongr
      _ = D'*t := by dsimp [D']; ring
  have hGpos : 0 < p.1.det := hδ.trans_le hdet
  rw [←Real.sqrt_div' _ hGpos.le]
  calc
    |Real.sqrt (A.det/p.1.det)-1| ≤ |A.det/p.1.det-1| := abs_sqrt_sub_one_le _
    _ = |A.det-p.1.det|/p.1.det := by rw [div_sub_one hGpos.ne',abs_div,abs_of_pos hGpos]
    _ ≤ |A.det-p.1.det|/δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ hdet
    _ ≤ (D'*t)/δ := div_le_div_of_nonneg_right hb hδ.le
    _ = D'/δ*t := by ring

end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

local instance : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

end CAT0Fillings
end
end

end OAI
