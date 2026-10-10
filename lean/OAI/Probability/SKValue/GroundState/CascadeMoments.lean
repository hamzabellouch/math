import Mathlib
import OAI.Probability.SKValue.GroundState.TreeProductLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

abbrev CascadeShape := List (ℝ×ℝ)
abbrev CascadeWidths : CascadeShape → Type
  | [] => PUnit
  | _::L => ℕ×CascadeWidths L

noncomputable def cascadeLaw : (L : CascadeShape) → CascadeWidths L → Measure ℝ
  | [],_ => Measure.dirac 0
  | (c,m)::L,w => branchLaw (gaussianAddLaw c (cascadeLaw L w.2)) m w.1

instance cascadeLaw_probability (L : CascadeShape) (w : CascadeWidths L) :
    IsProbabilityMeasure (cascadeLaw L w) := by
  induction L with
  | nil => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | cons p L ih =>
    have := ih w.2
    exact inferInstanceAs (IsProbabilityMeasure (branchLaw (gaussianAddLaw p.1 (cascadeLaw L w.2)) p.2 w.1))

def CascadeScale (a : ℝ) : CascadeShape → Prop
  | [] => 0 ≤ a
  | (_,m)::L => 0 ≤ a ∧ a < m ∧ CascadeScale m L

noncomputable def cascadeMoment (a : ℝ) : CascadeShape → ℝ
  | [] => 1
  | (c,m)::L => gumbelExpMoment (a/m)*(Real.exp ((m*c)^2/2)*cascadeMoment m L)^(a/m)

lemma branchLaw_exp_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a m : ℝ} (ha : 0 ≤ a) (ham : a/m < 1)
    (he : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) (b : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (a*x)) (branchLaw μ m b) := by
  rw [branchLaw,integrable_map_measure (by fun_prop) (continuous_branchMax m b).measurable.aemeasurable]
  exact branchMax_exp_integrable ha ham he b

lemma cascadeMoment_pos {L : CascadeShape} {a : ℝ} (h : CascadeScale a L) :
    0 < cascadeMoment a L := by
  induction L generalizing a with
  | nil => exact zero_lt_one
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    exact mul_pos (gumbelExpMoment_pos ((div_lt_one hm).mpr ham))
      (Real.rpow_pos_of_pos (mul_pos (Real.exp_pos _) (ih hL)) _)

lemma cascadeLaw_integrable (L : CascadeShape) (w : CascadeWidths L) :
    Integrable (fun x : ℝ ↦ x) (cascadeLaw L w) := by
  induction L with
  | nil =>
    apply integrable_dirac
    simp
  | cons p L ih => exact branchLaw_integrable (gaussianAddLaw_integrable _ (ih w.2)) _ _

lemma cascadeLaw_exp_integrable {L : CascadeShape} {a : ℝ} (h : CascadeScale a L)
    (w : CascadeWidths L) : Integrable (fun x : ℝ ↦ Real.exp (a*x)) (cascadeLaw L w) := by
  induction L generalizing a with
  | nil =>
    apply integrable_dirac
    simp
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (ih hL w.2)
    exact branchLaw_exp_integrable ha ((div_lt_one hm).mpr ham)
      (integrable_exp_smaller ha ham.le he) w.1

theorem cascadeLaw_exp_upper {L : CascadeShape} {a : ℝ} (h : CascadeScale a L)
    (w : CascadeWidths L) : (∫ x,Real.exp (a*x) ∂cascadeLaw L w) ≤ cascadeMoment a L := by
  induction L generalizing a with
  | nil => simp [cascadeLaw,cascadeMoment]
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (cascadeLaw_exp_integrable hL w.2)
    have hb := branchLaw_exp_upper hm ha ham he w.1
    rw [gaussianAddLaw_exp] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)).le
    apply Real.rpow_le_rpow (by positivity)
    · exact mul_le_mul_of_nonneg_left (ih hL w.2) (Real.exp_pos _).le
    · exact div_nonneg ha hm.le

theorem cascadeMoment_mem_closure {L : CascadeShape} {a : ℝ} (h : CascadeScale a L) :
    cascadeMoment a L ∈ closure (range (fun w : CascadeWidths L ↦
      ∫ x,Real.exp (a*x) ∂cascadeLaw L w)) := by
  induction L generalizing a with
  | nil =>
    apply subset_closure
    exact ⟨PUnit.unit,by simp [cascadeLaw,cascadeMoment]⟩
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    let f : ℝ → ℝ := fun y ↦ gumbelExpMoment (a/p.2)*(Real.exp ((p.2*p.1)^2/2)*y)^(a/p.2)
    have hf : ContinuousAt f (cascadeMoment p.2 L) :=
      continuousAt_const.mul ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr (div_nonneg ha hm.le)))
    have hh := mem_closure_image hf (ih hL)
    apply (closure_minimal (t := closure (range (fun w : CascadeWidths (p::L) ↦
      ∫ x,Real.exp (a*x) ∂cascadeLaw (p::L) w))) ?_ isClosed_closure) hh
    rintro y ⟨z,⟨w,rfl⟩,rfl⟩
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (cascadeLaw_exp_integrable hL w)
    have ht := branchLaw_exp_tendsto hm ha ham he
    rw [gaussianAddLaw_exp] at ht
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun b ↦ ⟨(b,w),rfl⟩))

noncomputable def cascadeMean : CascadeShape → ℝ
  | [] => 0
  | (c,m)::L => gumbelMean/m+Real.log (Real.exp ((m*c)^2/2)*cascadeMoment m L)/m

theorem cascadeMean_mem_closure {L : CascadeShape} (h : CascadeScale 0 L) :
    cascadeMean L ∈ closure (range (fun w : CascadeWidths L ↦ ∫ x,x ∂cascadeLaw L w)) := by
  cases L with
  | nil =>
    apply subset_closure
    exact ⟨PUnit.unit,by simp [cascadeLaw,cascadeMean]⟩
  | cons p L =>
    obtain ⟨_,hm,hL⟩ := h
    let f : ℝ → ℝ := fun y ↦ gumbelMean/p.2+Real.log (Real.exp ((p.2*p.1)^2/2)*y)/p.2
    have hf : ContinuousAt f (cascadeMoment p.2 L) := by
      apply continuousAt_const.add
      apply ContinuousAt.div_const
      apply ContinuousAt.log (continuousAt_const.mul continuousAt_id)
      exact (mul_pos (Real.exp_pos _) (cascadeMoment_pos hL)).ne'
    have hh := mem_closure_image hf (cascadeMoment_mem_closure hL)
    apply (closure_minimal (t := closure (range (fun w : CascadeWidths (p::L) ↦
      ∫ x,x ∂cascadeLaw (p::L) w))) ?_ isClosed_closure) hh
    rintro y ⟨z,⟨w,rfl⟩,rfl⟩
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (cascadeLaw_exp_integrable hL w)
    have ht := branchLaw_mean_tendsto (gaussianAddLaw_integrable _ (cascadeLaw_integrable L w)) hm he
    rw [gaussianAddLaw_exp] at ht
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun b ↦ ⟨(b,w),rfl⟩))

end SKValueG

end

end OAI
