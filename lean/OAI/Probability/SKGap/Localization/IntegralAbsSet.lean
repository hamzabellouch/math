import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianCoordinateMemLp

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
namespace SKGap
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_abs_on_set_le {F : Ω → ℝ} (hF : MemLp F 2 μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, |F x| ∂μ) ≤ sqrt (∫ x, (F x)^2 ∂μ)*sqrt (μ.real s) := by
  have hG : MemLp (s.indicator (fun _ : Ω => (1:ℝ))) 2 μ :=
    memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top _ _))
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF) (by simpa using hG)
  have he : (fun x => ‖F x‖*‖s.indicator (fun _ : Ω => (1:ℝ)) x‖) =
      s.indicator (fun x => |F x|) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx,Real.norm_eq_abs]
  have hg : (fun x => ‖s.indicator (fun _ : Ω => (1:ℝ)) x‖^(2:ℝ)) =
      s.indicator (fun _ : Ω => (1:ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [he,hg,integral_indicator hs,integral_indicator hs] at hh
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow,
    integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

omit [IsProbabilityMeasure μ] in
lemma integral_exceptional_equal_bound {F G H : Ω → ℝ} {s : Set Ω}
    (hs : MeasurableSet s) (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (he : ∀ x ∉ s, F x=G x)
    (hb : ∀ x ∈ s, ‖F x-G x‖ ≤ H x) :
    |(∫ x, F x ∂μ)-(∫ x, G x ∂μ)| ≤ ∫ x in s, H x ∂μ := by
  rw [← integral_sub hF hG]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_indicator hs]
  apply integral_mono ((hF.sub hG).norm) (hH.indicator hs)
  intro x
  change ‖F x-G x‖ ≤ s.indicator H x
  by_cases hx : x∈s
  · simpa only [Set.indicator_of_mem hx] using hb x hx
  · simp only [Set.indicator_of_notMem hx,he x hx,sub_self,norm_zero,le_refl]

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma abs_mul_entry_bound (M K : Matrix ι ι ℝ) (C : ℝ) (hK : ∀ a b, |K a b| ≤ C) (i : ι) :
    |(M*K) i i| ≤ C*∑ b, |M i b| := by
  rw [Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hK b i) (abs_nonneg _)

omit [DecidableEq ι] in

theorem goe_diagonal_inverse_loop {r : ℝ} (hr : 0 ≤ r) (a c : ι → ℝ) (i : ι)
    {K : (MatrixCoordinates ι → ℝ) → Matrix ι ι ℝ} {C : ℝ}
    {s : Set (MatrixCoordinates ι → ℝ)} (hK : Continuous K)
    (hC : ∀ g a b, |K g a b| ≤ C) (hs : MeasurableSet s)
    (he : ∀ g ∈ s, K g i i = 1+a i*((goeMatrix r g*K g) i i-c i*K g i i)) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    |(∫ g, K g i i ∂μ)-
      (1+a i*((∫ g, (goeMatrix r g*K g) i i ∂μ)-c i*(∫ g, K g i i ∂μ)))| ≤
      (C+1+|a i*c i| *C)*μ.real sᶜ+
        (|a i| *C)*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro μ
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 i i)
  have hKi (a b : ι) : Integrable (fun g => K g a b) μ :=
    Integrable.mono' (integrable_const C) (hK.matrix_elem a b).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hC g a b))
  have hW (b : ι) : Integrable (fun g => goeMatrix r g i b) μ :=
    (goeEntry_memLp r i b).integrable (by norm_num)
  have hWK (b : ι) : Integrable (fun g => goeMatrix r g i b*K g b i) μ := by
    simpa only [mul_comm] using (hW b).bdd_mul (hK.matrix_elem b i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hC g b i))
  have hWI : Integrable (fun g => (goeMatrix r g*K g) i i) μ :=
    integrable_finsetSum _ (fun b _ => hWK b)
  let A := C+1+|a i*c i| *C
  let B := |a i| *C
  let H := fun g => A+B*∑ b, |goeMatrix r g i b|
  have hHA : Integrable (fun g => ∑ b, |goeMatrix r g i b|) μ :=
    integrable_finsetSum _ (fun b _ => (hW b).norm)
  have hHI : Integrable H μ := (integrable_const A).add (hHA.const_mul B)
  have hGI : Integrable (fun g => 1+a i*((goeMatrix r g*K g) i i-c i*K g i i)) μ :=
    (integrable_const 1).add ((hWI.sub ((hKi i i).const_mul _)).const_mul _)
  have hb (g : MatrixCoordinates ι → ℝ) :
      ‖K g i i-(1+a i*((goeMatrix r g*K g) i i-c i*K g i i))‖ ≤ H g := by
    rw [Real.norm_eq_abs]
    have hid : K g i i-(1+a i*((goeMatrix r g*K g) i i-c i*K g i i)) =
        (K g i i-1)+(a i*c i)*K g i i+(-a i)*(goeMatrix r g*K g) i i := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_add_le _ _) le_rfl).trans
    have hk1 : |K g i i-1| ≤ C+1 := (abs_sub _ _).trans (by simpa using add_le_add_right (hC g i i) 1)
    have hk2 : |(a i*c i)*K g i i| ≤ |a i*c i| *C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC g i i) (abs_nonneg _)
    have hk3 : |(-a i)*(goeMatrix r g*K g) i i| ≤ |a i| *(C*∑ b, |goeMatrix r g i b|) := by
      rw [abs_mul,abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_mul_entry_bound _ _ C (hC g) i) (abs_nonneg _)
    exact (add_le_add (add_le_add hk1 hk2) hk3).trans_eq (by dsimp [H,A,B]; ring)
  have hraw := integral_exceptional_equal_bound hs.compl (hKi i i) hGI hHI
    (fun g hg => he g (by simpa using hg)) (fun g _ => hb g)
  have hbad (b : ι) : (∫ g in sᶜ, |goeMatrix r g i b| ∂μ) ≤
      sqrt (2*r)*sqrt (μ.real sᶜ) := by
    apply (integral_abs_on_set_le (goeEntry_memLp r i b) hs.compl).trans
    exact mul_le_mul_of_nonneg_right (sqrt_le_sqrt (goeEntry_integral_sq_le hr i b)) (sqrt_nonneg _)
  have hHr : (∫ g in sᶜ, H g ∂μ) ≤ A*μ.real sᶜ+B*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
    rw [show H = fun g => A+B*∑ b, |goeMatrix r g i b| from rfl,
      integral_add (integrable_const A) ((hHA.const_mul B).mono_measure Measure.restrict_le_self),
      integral_const,integral_const_mul]
    have hWa (b : ι) : Integrable (fun g => |goeMatrix r g i b|) (μ.restrict sᶜ) := by
      simpa only [Real.norm_eq_abs] using (hW b).norm.mono_measure Measure.restrict_le_self
    rw [integral_finsetSum _ (fun b _ => hWa b)]
    simp only [measureReal_restrict_apply_univ,smul_eq_mul]
    calc
      _ ≤ μ.real sᶜ*A+B*(∑ _b : ι, sqrt (2*r)*sqrt (μ.real sᶜ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hbad b))
          (mul_nonneg (abs_nonneg _) hC0))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have heI : (∫ g, 1+a i*((goeMatrix r g*K g) i i-c i*K g i i) ∂μ) =
      1+a i*((∫ g, (goeMatrix r g*K g) i i ∂μ)-c i*(∫ g, K g i i ∂μ)) := by
    have ht := integral_add (integrable_const (1:ℝ))
      ((hWI.sub ((hKi i i).const_mul (c i))).const_mul (a i))
    change (∫ g, 1+a i*((goeMatrix r g*K g) i i-c i*K g i i) ∂μ) = _ at ht
    rw [ht,integral_const_mul]
    simp only [Pi.sub_apply]
    rw [integral_sub hWI ((hKi i i).const_mul (c i)),integral_const_mul]
    simp
  rw [heI] at hraw
  exact hraw.trans hHr

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
