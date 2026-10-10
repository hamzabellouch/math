import Mathlib
import OAI.Probability.SKValue.GroundState.RandomGuerra
import OAI.Probability.SKValue.GroundState.CascadeMoments

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma branchMax_gumbelMean {branchExcess : ℕ} (x : Fin (branchExcess+1) → ℝ)
    {m : ℝ} (hm : 0 < m) :
    (∫ z,branchMax m branchExcess (x,z) ∂Measure.pi (fun _ : Fin (branchExcess+1) ↦ gumbelLaw))=
      gumbelMean/m+Real.log ((∑ i,Real.exp (m*x i))/(branchExcess+1 : ℝ))/m := by
  have hi : Integrable (fun z : Fin (branchExcess+1) → ℝ ↦ finiteMaximum (fun i ↦ x i+z i/m))
      (Measure.pi (fun _ : Fin (branchExcess+1) ↦ gumbelLaw)) := by
    apply integrable_finiteMaximum_of_integrable
    intro i
    exact (integrable_const _).add (((measurePreserving_eval (fun _ : Fin (branchExcess+1) ↦ gumbelLaw) i).integrable_comp
      (by fun_prop) |>.mpr gumbel_integrable).div_const m)
  unfold branchMax
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  have h := centered_gumbel_max x hm
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at h
  rw [add_div] at h
  linarith

theorem branchLaw_mean_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) {m : ℝ} (hm : 0 < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) (b : ℕ) :
    (∫ x,x ∂branchLaw μ m b) ≤ gumbelMean/m+Real.log (∫ x,Real.exp (m*x) ∂μ)/m := by
  let ν := Measure.pi (fun _ : Fin (b+1) ↦ μ)
  let G := Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw)
  let V := fun x : Fin (b+1) → ℝ ↦ (∑ i,Real.exp (m*x i))/(b+1 : ℝ)
  have hiv : Integrable V ν := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr he
  have hif : Integrable (fun x ↦ ∫ z,branchMax m b (x,z) ∂G) ν :=
    (branchMax_integrable hi m b).integral_prod_left
  have hil : Integrable (fun x ↦ Real.log (V x)) ν := by
    convert (hif.const_mul m).sub (integrable_const gumbelMean) using 1
    funext x
    dsimp only [G,V,Pi.sub_apply,Pi.mul_apply]
    rw [branchMax_gumbelMean x hm]
    field_simp
    ring
  have hp (x : Fin (b+1) → ℝ) : 0<V x := div_pos (exp_sum_pos _) (by positivity)
  have hv : (∫ x,V x ∂ν)=∫ x,Real.exp (m*x) ∂μ := by
    dsimp only [V]
    rw [integral_div,integral_finsetSum]
    · have hh (i : Fin (b+1)) : (∫ x : Fin (b+1) → ℝ,Real.exp (m*x i) ∂ν)=
          ∫ x,Real.exp (m*x) ∂μ :=
        (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).hasLaw.integral_comp (show AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (m*x)) μ by fun_prop)
      simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      field_simp
    · intro i _
      exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr he
  have hj := integral_log_le_log_integral hiv hil (Eventually.of_forall hp)
  rw [hv] at hj
  have hid := branchLaw_test hi m b LipschitzWith.id
  simp only [id_eq] at hid
  rw [hid]
  simp_rw [branchMax_gumbelMean _ hm]
  rw [integral_add (integrable_const _) (hil.div_const m), integral_const,integral_div]
  simp only [probReal_univ,one_smul]
  linarith [div_le_div_of_nonneg_right hj hm.le]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def gumbelTreeMoment (a : ℝ) : GaussianTree → ℝ
  | [] => 1
  | l::T => gumbelExpMoment (a/l.height)*(gumbelTreeMoment l.height T)^(a/l.height)

lemma gumbelTreeMoment_pos {T : GaussianTree} {a : ℝ} (h : TreeScale a T) :
    0 < gumbelTreeMoment a T := by
  induction T generalizing a with
  | nil => exact zero_lt_one
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0 < l.height := ha.trans_lt ham
    exact mul_pos (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)) (Real.rpow_pos_of_pos (ih hT) _)

lemma exp_prod_integrable_of_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν] {f : A×B → ℝ} {H : A → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hpos : ∀ p,0 ≤ f p)
    (hi : ∀ x,Integrable (fun y ↦ f (x,y)) ν) (hH : Integrable H μ)
    (hb : ∀ x,(∫ y,f (x,y) ∂ν) ≤ H x) : Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff hf).mpr
  refine ⟨Eventually.of_forall hi,?_⟩
  have he : (fun x ↦ ∫ y,‖f (x,y)‖ ∂ν)=(fun x ↦ ∫ y,f (x,y) ∂ν) := by
    funext x
    apply integral_congr_ae
    exact Eventually.of_forall (fun y ↦ Real.norm_of_nonneg (hpos (x,y)))
  rw [he]
  apply hH.mono' hf.integral_prod_right'
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (integral_nonneg (fun y ↦ hpos (x,y)))]
    exact hb x)

lemma fieldChildLaw_exp_bound (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ)
    {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {m K : ℝ} (hm : 0 < m)
    (hi : ∀ y,Integrable (fun w ↦ Real.exp (m*fieldTreeEval n l.endpoint T y w))
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)))
    (hb : ∀ y,(∫ w,Real.exp (m*fieldTreeEval n l.endpoint T y w)
      ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ≤ K*Real.exp (m*∑ i,ψ (y i))) :
    Integrable (fun y : ℝ ↦ Real.exp (m*y)) (fieldChildLaw n q l T x) ∧
      (∫ y,Real.exp (m*y) ∂fieldChildLaw n q l T x) ≤ K*Real.exp (m*∑ i,SKValue.coleHopf m (l.endpoint-q) ψ (x i)) := by
  let f := fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
    Real.exp (m*fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2)
  have hmeas : AEStronglyMeasurable f ((gaussianProduct (Fin n)).prod
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_fieldChild n q l T x))).aestronglyMeasurable
  have hH := (gaussian_exp_sum_profile_integrable hψ hm.le n x (Real.sqrt (l.endpoint-q))).const_mul K
  have hip : Integrable f ((gaussianProduct (Fin n)).prod
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n))) :=
    exp_prod_integrable_of_bound hmeas (fun p ↦ (Real.exp_pos _).le)
      (fun z ↦ hi (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z i)) hH
      (fun z ↦ hb (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z i))
  constructor
  · rw [fieldChildLaw,integrable_map_measure (by fun_prop) (continuous_fieldChild n q l T x).measurable.aemeasurable]
    exact hip
  · rw [fieldChildLaw,integral_map (continuous_fieldChild n q l T x).measurable.aemeasurable (by fun_prop)]
    rw [integral_prod _ hip]
    have H := integral_mono hip.integral_prod_left hH (fun z ↦ hb (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z i))
    rw [integral_const_mul,gaussian_exp_sum_coleHopf hψ hm n x (l.endpoint-q)] at H
    exact H

theorem fieldTreeEval_moment_bound (n : ℕ) {T : GaussianTree} {a : ℝ} (h : TreeScale a T)
    (q : ℝ) (x : Fin n → ℝ) :
    Integrable (fun w ↦ Real.exp (a*fieldTreeEval n q T x w))
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ∧
    (∫ w,Real.exp (a*fieldTreeEval n q T x w) ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ≤
      gumbelTreeMoment a T*Real.exp (a*∑ i,fieldProfile q T (x i)) := by
  induction T generalizing a q x with
  | nil =>
    simp only [fieldTreeEval_nil,gumbelTreeMoment,fieldProfile,one_mul]
    exact ⟨integrable_const _,by simp⟩
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0 < l.height := ha.trans_lt ham
    have hcb := fieldChildLaw_exp_bound n q l T x (fieldProfile_lipschitz hT l.endpoint) hm
      (fun y ↦ (ih hT l.endpoint y).1) (fun y ↦ (ih hT l.endpoint y).2)
    have hp := fieldTreeEval_law_step n q l T x
    constructor
    · exact hp.integrable_comp (by fun_prop) |>.mpr (branchLaw_exp_integrable ha ((div_lt_one hm).mpr ham)
        (integrable_exp_smaller ha ham.le hcb.1) _)
    · have heq := hp.hasLaw.integral_comp (show AEStronglyMeasurable (fun y : ℝ ↦ Real.exp (a*y))
          (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) by fun_prop)
      simp only [Function.comp_def] at heq
      rw [heq]
      have hub := branchLaw_exp_upper hm ha ham hcb.1 l.branchExcess
      apply hub.trans
      have kr := Real.rpow_le_rpow (integral_nonneg (fun y ↦ (Real.exp_pos _).le)) hcb.2 (div_nonneg ha hm.le)
      have hh := mul_le_mul_of_nonneg_left kr (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)).le
      rw [Real.mul_rpow (gumbelTreeMoment_pos hT).le (Real.exp_pos _).le,←Real.exp_mul] at hh
      have he : (l.height*(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)))*(a/l.height)=
          a*(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)) := by field_simp
      rw [he] at hh
      simpa only [gumbelTreeMoment,fieldProfile,mul_assoc] using hh

noncomputable def gumbelTreeMean : GaussianTree → ℝ
  | [] => 0
  | l::T => gumbelMean/l.height+Real.log (gumbelTreeMoment l.height T)/l.height

theorem fieldTreeEval_mean_upper (n : ℕ) {T : GaussianTree} (h : TreeScale 0 T)
    (q : ℝ) (x : Fin n → ℝ) :
    (∫ w,fieldTreeEval n q T x w ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ≤
      (∑ i,fieldProfile q T (x i))+gumbelTreeMean T := by
  cases T with
  | nil => simp [fieldTreeEval_nil,fieldProfile,gumbelTreeMean]
  | cons l T =>
    obtain ⟨_,hm,hT⟩ := h
    have hcb := fieldChildLaw_exp_bound n q l T x (fieldProfile_lipschitz hT l.endpoint) hm
      (fun y ↦ (fieldTreeEval_moment_bound n hT l.endpoint y).1)
      (fun y ↦ (fieldTreeEval_moment_bound n hT l.endpoint y).2)
    have hp := fieldTreeEval_law_step n q l T x
    have heq := hp.hasLaw.integral_comp (show AEStronglyMeasurable (fun y : ℝ ↦ y)
      (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) from aestronglyMeasurable_id)
    simp only [Function.comp_def] at heq
    rw [heq]
    have hu := branchLaw_mean_upper (fieldChildLaw_integrable n q l T x) hm hcb.1 l.branchExcess
    apply hu.trans
    have hpos := integral_exp_pos hcb.1
    have hh := Real.log_le_log hpos hcb.2
    rw [Real.log_mul (gumbelTreeMoment_pos hT).ne' (Real.exp_pos _).ne',Real.log_exp] at hh
    have hd := div_le_div_of_nonneg_right hh hm.le
    dsimp only [fieldProfile,gumbelTreeMean]
    have he : (Real.log (gumbelTreeMoment l.height T)+l.height*(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)))/l.height=
        Real.log (gumbelTreeMoment l.height T)/l.height+(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)) := by field_simp
    rw [he] at hd
    linarith

end SKValueG

end

end OAI
