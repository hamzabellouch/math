import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.SpatialForm

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
open Set Metric Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma abs_sqrt_sub_one_le (a : ℝ) : |Real.sqrt a-1| ≤ |a-1| := by
  by_cases ha : 0 ≤ a
  · have hs := Real.sq_sqrt ha
    have hn := Real.sqrt_nonneg a
    by_cases h : 1 ≤ Real.sqrt a
    · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (by nlinarith : 0 ≤ a-1)]
      nlinarith
    · have h' : Real.sqrt a ≤ 1 := le_of_not_ge h
      rw [abs_of_nonpos (sub_nonpos.mpr h'),abs_of_nonpos (by nlinarith : a-1 ≤ 0)]
      nlinarith [sq_nonneg (Real.sqrt a-1)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ha)]
    rw [abs_of_nonpos (by norm_num : (0:ℝ)-1 ≤ 0),
      abs_of_nonpos (by linarith : a-1 ≤ 0)]
    linarith

abbrev RadialParameters (ι : Type*) := (ℝ × ℝ) × ((ι → ℝ) × (ι → ℝ))

def spatialRadialSlope (t : ℝ) (p : RadialParameters ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (-2*p.1.1+t*p.1.1^2)*(if i=j then 1 else 0)-
    (1-t*p.1.1)*p.1.2*(p.2.1 i*p.2.2 j+p.2.2 i*p.2.1 j)+
    t*p.1.2^2*p.2.2 i*p.2.2 j

omit [Fintype ι] in
lemma continuous_spatialRadialSlope :
    Continuous (fun q : ℝ × RadialParameters ι => spatialRadialSlope q.1 q.2) := by
  unfold spatialRadialSlope
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fun_prop

omit [Fintype ι] in
lemma spatialRadialForm_sub_identity (t : ℝ) (p : RadialParameters ι) :
    spatialRadialForm p.1.1 p.1.2 t p.2.1 p.2.2 - 1 = t • spatialRadialSlope t p := by
  ext i j
  simp only [spatialRadialForm,spatialRadialSlope,Matrix.sub_apply,Matrix.one_apply,
    Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
  split_ifs <;> ring

theorem spatialRadialForm_uniform_slope_bound (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadialParameters ι, ‖p‖ ≤ B →
      ∀ t ∈ Icc (0:ℝ) 1,
        |Real.sqrt (spatialRadialForm p.1.1 p.1.2 t p.2.1 p.2.2).det-1| ≤ C*t := by
  let K : Set (ℝ × RadialParameters ι) := Icc (0:ℝ) 1 ×ˢ closedBall 0 B
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 B)
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (f := fun q : ℝ × RadialParameters ι => (fun i j => spatialRadialSlope q.1 q.2 i j))
    continuous_spatialRadialSlope.continuousOn
  let R : ℝ := max D 0
  have hR : 0 ≤ R := le_max_right _ _
  let detM : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    ⟨Matrix.detRowAlternating.toMultilinearMap,continuous_id.matrix_det⟩
  let C := ‖detM‖*(Fintype.card ι : ℝ)*(R+1)^(Fintype.card ι-1)*R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp t ht
  have hQ : ‖spatialRadialSlope t p‖ ≤ R :=
    (hD (t,p) ⟨ht,by simpa only [mem_closedBall,dist_zero_right] using hp⟩).trans (le_max_left _ _)
  let A := spatialRadialForm p.1.1 p.1.2 t p.2.1 p.2.2
  have hdiff : ‖A-1‖ ≤ R*t := by
    rw [show A-1 = t • spatialRadialSlope t p from spatialRadialForm_sub_identity t p,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hQ ht.1
  have hId : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
    apply (Matrix.norm_le_iff zero_le_one).2
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hA : ‖A‖ ≤ R+1 := by
    have hh := norm_add_le (A-1) (1 : Matrix ι ι ℝ)
    rw [sub_add_cancel] at hh
    have hRt : R*t ≤ R := (mul_le_mul_of_nonneg_left ht.2 hR).trans_eq (mul_one R)
    linarith
  have hmax : max ‖A‖ ‖(1 : Matrix ι ι ℝ)‖ ≤ R+1 := max_le hA (by linarith)
  have hh := detM.norm_image_sub_le (fun i j => A i j) (fun i j => (1 : Matrix ι ι ℝ) i j)
  change ‖A.det-(1 : Matrix ι ι ℝ).det‖ ≤
    ‖detM‖*(Fintype.card ι : ℝ)*max ‖A‖ ‖(1 : Matrix ι ι ℝ)‖^(Fintype.card ι-1)*‖A-1‖ at hh
  rw [Matrix.det_one,Real.norm_eq_abs] at hh
  calc
    _ ≤ |A.det-1| := abs_sqrt_sub_one_le A.det
    _ ≤ ‖detM‖*(Fintype.card ι : ℝ)*max ‖A‖ ‖(1 : Matrix ι ι ℝ)‖^(Fintype.card ι-1)*‖A-1‖ := hh
    _ ≤ ‖detM‖*(Fintype.card ι : ℝ)*(R+1)^(Fintype.card ι-1)*(R*t) := by gcongr
    _ = C*t := by dsimp [C]; ring

end CAT0Fillings

end
end

end OAI
