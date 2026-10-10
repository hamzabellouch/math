import Mathlib

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaussianTools
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def scalarRow (d : ℕ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

lemma row_memLp {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun a : Fin d → ℝ => ∑ j,a j*v j) 2 (scalarRow d) := by
  apply memLp_finsetSum
  intro j _
  exact ((memLp_id_gaussianReal (2 : NNReal)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)).mul_const (v j)

lemma row_integral {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (∫ a : Fin d → ℝ,∑ j,a j*v j ∂scalarRow d)=0 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi (j : Fin d) : Integrable (fun a : Fin d → ℝ => a j*v j) (scalarRow d) :=
    (((memLp_id_gaussianReal (2 : NNReal)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)).mul_const (v j)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_mul_const,scalarRow,integral_eval,integral_id_gaussianReal,zero_mul,Finset.sum_const_zero]

lemma row_energy {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (∫ a : Fin d → ℝ,(∑ j,a j*v j)^2 ∂scalarRow d)=‖v‖^2 := by
  have h := variance_sum_pi (μ := fun _ : Fin d => gaussianReal 0 1)
    (X := fun j x => x*v j) (fun j => (memLp_id_gaussianReal (2 : NNReal)).mul_const (v j))
  have hm : Measurable (fun a : Fin d → ℝ => ∑ j,a j*v j) := by fun_prop
  simp only [Finset.sum_fn] at h
  rw [variance_eq_integral hm.aemeasurable] at h
  change (∫ a,(∑ j,a j*v j - ∫ a,∑ j,a j*v j ∂scalarRow d)^2 ∂scalarRow d)=_ at h
  rw [row_integral] at h
  simp only [sub_zero,variance_mul_const] at h
  rw [h,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  simp

noncomputable def labelDensity {p : ℕ} (r : ℝ) (y : Fin p → ℝ) : ℝ :=
  ∏ i,gaussianPDFReal 0 (NNReal.mk (r^2) (sq_nonneg r)) (y i)

lemma labelDensity_pos {p : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin p → ℝ) :
    0 < labelDensity r y := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by intro hh; have he := congrArg (fun t : NNReal => (t : ℝ)) hh; exact (pow_ne_zero 2 hr.ne') he)

lemma measurable_labelDensity {p : ℕ} (r : ℝ) : Measurable (@labelDensity p r) := by
  unfold labelDensity
  fun_prop

lemma log_labelDensity {p : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin p → ℝ) :
    Real.log (labelDensity r y) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi) -
        (∑ i,(y i)^2)/(2*r^2) := by
  unfold labelDensity
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos 0 (NNReal.mk (r^2) (sq_nonneg r)) (y i) (by intro hh; have he := congrArg (fun t : NNReal => (t : ℝ)) hh; exact (pow_ne_zero 2 hr.ne') he)).ne')]
  simp only [gaussianPDFReal,NNReal.coe_mk,sub_zero]
  have hs : Real.sqrt (2*Real.pi*r^2)=Real.sqrt (2*Real.pi)*r := by
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  simp_rw [Real.log_mul (by positivity : (Real.sqrt (2*Real.pi*r^2))⁻¹ ≠ 0) (Real.exp_pos _).ne',
    Real.log_inv,hs,Real.log_mul (by positivity : Real.sqrt (2*Real.pi) ≠ 0) hr.ne',
    Real.log_sqrt (by positivity : 0 ≤ 2*Real.pi),Real.log_exp]
  simp_rw [neg_div]
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,← Finset.sum_div,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma rows_energy {p d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (∫ X : Fin p → Fin d → ℝ, ∑ i,(∑ j,X i j*v j)^2
      ∂Measure.pi (fun _ : Fin p => scalarRow d)) = (p:ℝ)*‖v‖^2 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi (i : Fin p) : Integrable (fun X : Fin p → Fin d → ℝ => (∑ j,X i j*v j)^2)
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    ((row_memLp v).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin p) : (∫ X : Fin p → Fin d → ℝ,(∑ j,X i j*v j)^2
      ∂Measure.pi (fun _ : Fin p => scalarRow d)) = ‖v‖^2 := by
    rw [← row_energy v]
    exact integral_comp_eval (μ := fun _ : Fin p => scalarRow d) (i := i)
      (f := fun a : Fin d → ℝ => (∑ j,a j*v j)^2) ((by fun_prop : Measurable
      (fun a : Fin d → ℝ => (∑ j,a j*v j)^2)).aestronglyMeasurable)
  simp_rw [he]
  simp

lemma rows_shift_energy {p d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (e : Fin p → ℝ) :
    (∫ X : Fin p → Fin d → ℝ, ∑ i,((∑ j,X i j*v j)+e i)^2
      ∂Measure.pi (fun _ : Fin p => scalarRow d)) ≤
      2*(p:ℝ)*‖v‖^2+2*∑ i,(e i)^2 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi (i : Fin p) : MemLp (fun X : Fin p → Fin d → ℝ => ∑ j,X i j*v j) 2
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    (row_memLp v).comp_measurePreserving (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)
  have hil : Integrable (fun X : Fin p → Fin d → ℝ => ∑ i,((∑ j,X i j*v j)+e i)^2)
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    integrable_finsetSum _ (fun i _ => ((hi i).add (memLp_const (e i))).integrable_sq)
  have hir : Integrable (fun X : Fin p → Fin d → ℝ => 2*(∑ i,(∑ j,X i j*v j)^2) + 2*∑ i,(e i)^2)
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    ((integrable_finsetSum _ (fun i _ => (hi i).integrable_sq)).const_mul 2).add (integrable_const _)
  calc
    _ ≤ ∫ X : Fin p → Fin d → ℝ, 2*(∑ i,(∑ j,X i j*v j)^2) + 2*∑ i,(e i)^2
        ∂Measure.pi (fun _ : Fin p => scalarRow d) := by
      apply integral_mono hil hir
      intro X
      dsimp only
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg ((∑ j,X i j*v j)-e i)]
    _ = _ := by
      rw [integral_add ((integrable_finsetSum _ (fun i _ => (hi i).integrable_sq)).const_mul 2)
        (integrable_const _),integral_const_mul, rows_energy]
      simp
      ring

end GaussianTools

end OAI
