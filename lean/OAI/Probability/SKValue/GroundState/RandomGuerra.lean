import Mathlib
import OAI.Probability.SKValue.GroundState.FieldTreeLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma scalar_pairing_law (T : GaussianTree) :
    MeasurePreserving (fun p : (TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ fun e ↦ (p.1 e,p.2 e))
      ((gaussianProduct (TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw)))
      (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)) :=
  (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (TreeEdges T)
    (fun _ ↦ standardGaussian) (fun _ ↦ gumbelLaw)).symm

lemma field_pairing_law (n : ℕ) (T : GaussianTree) :
    MeasurePreserving (fun p : (Fin n×TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ fun e ↦ ((fun i ↦ p.1 (i,e)),p.2 e))
      ((gaussianProduct (Fin n×TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw)))
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) := by
  have hs := measurePreserving_piCongrLeft (fun _ : TreeEdges T×Fin n ↦ standardGaussian)
    (Equiv.prodComm (Fin n) (TreeEdges T))
  have hc := (measurePreserving_finite_curry (I := TreeEdges T) (E := Fin n) standardGaussian).comp hs
  have hp := (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ (TreeEdges T)
    (fun _ ↦ gaussianProduct (Fin n)) (fun _ ↦ gumbelLaw)).symm
  exact hp.comp (hc.prod (MeasurePreserving.id (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))))

lemma scalarTreeEval_integrable (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Integrable (scalarTreeEval c q T) (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)) :=
  (scalarTreeEval_law c q T).integrable_comp aestronglyMeasurable_id |>.mpr (scalarTreeLaw_integrable c q T)

lemma scalarTreeValue_integrable_prod (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Integrable (fun p : (TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ scalarTreeValue c q T p.1 p.2)
      ((gaussianProduct (TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))) := by
  exact (scalar_pairing_law T).integrable_comp (continuous_scalarTreeEval c q T).aestronglyMeasurable
    |>.mpr (scalarTreeEval_integrable c q T)

lemma fieldTreeValue_integrable_prod (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ) :
    Integrable (fun p : (Fin n×TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ fieldTreeValue n q T x p.1 p.2)
      ((gaussianProduct (Fin n×TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))) := by
  have hc : Continuous (fieldTreeEval n q T x) :=
    (continuous_fieldTreeEval n q T).comp (continuous_const.prodMk continuous_id)
  exact (field_pairing_law n T).integrable_comp hc.aestronglyMeasurable
    |>.mpr (fieldTreeEval_integrable n q T x)

lemma scalarTreeValue_mean (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    (∫ g,∫ z,scalarTreeValue c q T z g ∂gaussianProduct (TreeEdges T)
      ∂Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))=∫ y,y ∂scalarTreeLaw c q T := by
  rw [←integral_prod_symm _ (scalarTreeValue_integrable_prod c q T)]
  have hcomp := (scalarTreeEval_law c q T).comp (scalar_pairing_law T)
  have he := hcomp.hasLaw.integral_comp aestronglyMeasurable_id
  exact he

lemma fieldTreeValue_mean (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ) :
    (∫ g,∫ z,fieldTreeValue n q T x z g ∂gaussianProduct (Fin n×TreeEdges T)
      ∂Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))=
      ∫ w,fieldTreeEval n q T x w ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n) := by
  rw [←integral_prod_symm _ (fieldTreeValue_integrable_prod n q T x)]
  have hc : Continuous (fieldTreeEval n q T x) :=
    (continuous_fieldTreeEval n q T).comp (continuous_const.prodMk continuous_id)
  exact (field_pairing_law n T).hasLaw.integral_comp hc.aestronglyMeasurable

theorem randomized_tree_guerra_upper {n : ℕ} (hn : 0 < n) (T : GaussianTree) (hT : ValidTreeGrid 0 T) :
    expectedMaximum n+(∫ y,y ∂scalarTreeLaw (fun q l ↦ Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)) 0 T) ≤
      ∫ w,fieldTreeEval n 0 T (fun _ ↦ 0) w ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n) := by
  let c : ℝ → TreeLevel → ℝ := fun q l ↦ Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)
  have hiA := scalarTreeValue_integrable_prod c 0 T
  have hiF := fieldTreeValue_integrable_prod n 0 T (fun _ ↦ 0)
  have hg : ∀ g : TreeEdges T → ℝ, expectedMaximum n+
      (∫ z,scalarTreeValue c 0 T z g ∂gaussianProduct (TreeEdges T)) ≤
      ∫ z,fieldTreeValue n 0 T (fun _ ↦ 0) z g ∂gaussianProduct (Fin n×TreeEdges T) := by
    intro g
    simpa only [scalarTreeValue,fieldTreeValue,zero_add,treeAuxVector,c] using
      finite_tree_guerra_upper hn T hT (treeOffset T g)
  have hu := integral_mono ((integrable_const (expectedMaximum n)).add hiA.integral_prod_right)
    hiF.integral_prod_right hg
  simp only [Pi.add_apply] at hu
  rw [integral_add (integrable_const _) hiA.integral_prod_right,integral_const,probReal_univ,one_smul,
    scalarTreeValue_mean,fieldTreeValue_mean] at hu
  exact hu

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma coleHopf_one_sided {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {m : ℝ} (hm : 0 < m)
    (h x y : ℝ) : SKValue.coleHopf m h ψ x ≤ SKValue.coleHopf m h ψ y+|x-y| := by
  have hiX := SKValue.lipschitz_exp_integrable hψ hm.le x (Real.sqrt h)
  have hiY := SKValue.lipschitz_exp_integrable hψ hm.le y (Real.sqrt h)
  have hpX := SKValue.lipschitz_exp_integral_pos hψ hm.le x (Real.sqrt h)
  have hpY := SKValue.lipschitz_exp_integral_pos hψ hm.le y (Real.sqrt h)
  have e : SKValue.standardGaussian=standardGaussian := rfl
  rw [e] at hiX hiY hpX hpY
  have hbound : (∫ z,Real.exp (m*ψ (x+Real.sqrt h*z)) ∂standardGaussian) ≤
      Real.exp (m*|x-y|)*(∫ z,Real.exp (m*ψ (y+Real.sqrt h*z)) ∂standardGaussian) := by
    rw [←integral_const_mul]
    apply integral_mono hiX (hiY.const_mul _)
    intro z
    have hl := hψ.dist_le_mul (x+Real.sqrt h*z) (y+Real.sqrt h*z)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
    rw [show x+Real.sqrt h*z-(y+Real.sqrt h*z)=x-y by ring] at hl
    dsimp only
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := le_abs_self (ψ (x+Real.sqrt h*z)-ψ (y+Real.sqrt h*z))
    nlinarith
  have hh := Real.log_le_log hpX hbound
  rw [Real.log_mul (Real.exp_pos _).ne' hpY.ne',Real.log_exp] at hh
  simp only [SKValue.coleHopf,ite_eq_right hm.ne',SKValue.heat,e]
  apply (div_le_iff₀ hm).mpr
  have he : (Real.log (∫ z,Real.exp (m*ψ (y+Real.sqrt h*z)) ∂standardGaussian)/m+|x-y|)*m=
      m*|x-y|+Real.log (∫ z,Real.exp (m*ψ (y+Real.sqrt h*z)) ∂standardGaussian) := by field_simp; ring
  rw [he]
  exact hh

lemma coleHopf_lipschitz {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {m : ℝ} (hm : 0 < m)
    (h : ℝ) : LipschitzWith 1 (SKValue.coleHopf m h ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  have hxy := coleHopf_one_sided hψ hm h x y
  have hyx := coleHopf_one_sided hψ hm h y x
  rw [abs_sub_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def fieldProfile (q : ℝ) : GaussianTree → ℝ → ℝ
  | [] => abs
  | l::T => SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T)

def TreeScale (a : ℝ) : GaussianTree → Prop
  | [] => 0 ≤ a
  | l::T => 0 ≤ a ∧ a < l.height ∧ TreeScale l.height T

lemma fieldProfile_lipschitz {T : GaussianTree} {a : ℝ} (h : TreeScale a T) (q : ℝ) :
    LipschitzWith 1 (fieldProfile q T) := by
  induction T generalizing a q with
  | nil =>
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [fieldProfile,NNReal.coe_one,one_mul,Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    exact coleHopf_lipschitz (ih hT _) (ha.trans_lt ham) _

lemma gaussian_exp_sum_profile_integrable {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {m : ℝ} (hm : 0 ≤ m) (n : ℕ) (x : Fin n → ℝ) (s : ℝ) :
    Integrable (fun z : Fin n → ℝ ↦ Real.exp (m*∑ i,ψ (x i+s*z i))) (gaussianProduct (Fin n)) := by
  have hi := Integrable.fintype_prod (fun i : Fin n ↦ SKValue.lipschitz_exp_integrable hψ hm (x i) s)
  convert hi using 1
  · funext z
    simp only [Finset.mul_sum,Real.exp_sum]
  · rfl

lemma gaussian_exp_sum_coleHopf {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {m : ℝ} (hm : 0 < m) (n : ℕ) (x : Fin n → ℝ) (h : ℝ) :
    (∫ z : Fin n → ℝ,Real.exp (m*∑ i,ψ (x i+Real.sqrt h*z i)) ∂gaussianProduct (Fin n))=
      Real.exp (m*∑ i,SKValue.coleHopf m h ψ (x i)) := by
  simp only [Finset.mul_sum,Real.exp_sum]
  rw [gaussianProduct,integral_fintype_prod_eq_prod (fun i : Fin n ↦ fun z : ℝ ↦ Real.exp (m*ψ (x i+Real.sqrt h*z)))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [SKValue.coleHopf,ite_eq_right hm.ne',SKValue.heat]
  rw [mul_div_cancel₀ _ hm.ne',Real.exp_log (SKValue.lipschitz_exp_integral_pos hψ hm.le (x i) (Real.sqrt h))]
  rfl

end SKValueG

end

end OAI
