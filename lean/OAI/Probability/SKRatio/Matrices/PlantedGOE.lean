import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianSupport
import OAI.Probability.SKRatio.Matrices.GOERegression
import OAI.Probability.SKRatio.Gaussian.Planted

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def augmented (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => β * goe g i j + β^2/(n:ℝ)

def augmentedDisorder (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Disorder n :=
  fun e => augmented β g e.1.1 e.1.2

lemma augmented_symmetric (β : ℝ) (g : (Fin n × Fin n) → ℝ) :
    (augmented β g)ᵀ = augmented β g := by
  funext i j
  simp only [Matrix.transpose_apply,augmented,goe,add_comm (g (j,i))]

lemma augmentedDisorder_gaussian (β : ℝ) :
    HasGaussianLaw (augmentedDisorder (n := n) β) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] Disorder n :=
    β • ContinuousLinearMap.pi (fun e : Edge n => (entryCLM e.1.1 e.1.2).comp (goeCLM n))
  have h := gaussian_add_constant (coordinates_gaussian.map_fun L) (fun _ : Edge n => β^2/(n:ℝ))
  apply h.congr
  exact Eventually.of_forall (fun g => by
    funext e
    simp only [L,smul_apply,
      ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,entryCLM_apply,
      goeCLM_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,augmentedDisorder,augmented])

lemma augmented_mean (β : ℝ) (i j : Fin n) :
    (∫ g, augmented β g i j ∂standardArrayLaw (Fin n × Fin n)) = β^2/(n:ℝ) := by
  unfold augmented
  rw [integral_add (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β)
    (integrable_const _),integral_const_mul,goe_entry_mean]
  simp

lemma augmented_covariance (hn : 0 < n) (β : ℝ) (i j k l : Fin n) :
    cov[fun g => augmented β g i j, fun g => augmented β g k l;
      standardArrayLaw (Fin n × Fin n)] =
      (β^2/(n:ℝ))*((if i=k ∧ j=l then 1 else 0)+(if i=l ∧ j=k then 1 else 0)) := by
  unfold augmented
  rw [covariance_add_const_left (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β),
    covariance_add_const_right (((goe_gaussian n).eval k |>.eval l).integrable.const_mul β),
    covariance_const_mul_left,covariance_const_mul_right,goe_entry_covariance hn]
  ring

lemma augmentedDisorder_covariance (hn : 0 < n) (β : ℝ) (e f : Edge n) :
    cov[fun g => augmentedDisorder β g e,fun g => augmentedDisorder β g f;
      standardArrayLaw (Fin n × Fin n)] = if e=f then β^2/(n:ℝ) else 0 := by
  unfold augmentedDisorder
  rw [augmented_covariance hn]
  have heq : e=f ↔ e.1.1=f.1.1 ∧ e.1.2=f.1.2 := by
    simp only [Subtype.ext_iff,Prod.ext_iff]
  have hcross : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    rintro ⟨h₁,h₂⟩
    have h := e.2
    rw [h₁,h₂] at h
    exact lt_asymm f.2 h
  simp only [ite_eq_right hcross,add_zero,←heq]
  split_ifs <;> simp

theorem augmentedDisorder_hasLaw (hn : 0 < n) (β : ℝ) :
    HasLaw (augmentedDisorder (n := n) β) (law β n) (standardArrayLaw (Fin n × Fin n)) := by
  have hg := augmentedDisorder_gaussian (n := n) β
  have hl (e : Edge n) : HasLaw (fun g => augmentedDisorder β g e)
      (gaussianReal (β^2/(n:ℝ)) (Real.toNNReal (β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
    refine ⟨(hg.eval e).aemeasurable,?_⟩
    rw [(hg.eval e).map_eq_gaussianReal,show (∫ g, augmentedDisorder β g e
      ∂standardArrayLaw (Fin n × Fin n)) = β^2/(n:ℝ) from augmented_mean β _ _,
      ←covariance_self (hg.eval e).aemeasurable,augmentedDisorder_covariance hn,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun e f h => by rw [augmentedDisorder_covariance hn,ite_eq_right h]))

lemma coupling_augmentedDisorder (β : ℝ) (g : (Fin n × Fin n) → ℝ) :
    Matrix.of (coupling (augmentedDisorder β g)) = augmented β g - Matrix.diagonal (fun i => augmented β g i i) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [coupling]
  · rcases lt_or_gt_of_ne h with hij | hij
    · simp [coupling,hij,h,augmentedDisorder]
    · simp [coupling,hij,not_lt_of_gt hij,h,augmentedDisorder,augmented,goe,add_comm]

def augmentedField (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, augmented β g i j

lemma augmentedField_gaussian (β : ℝ) :
    HasGaussianLaw (augmentedField (n := n) β) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    β • ContinuousLinearMap.pi (fun i : Fin n => ∑ j : Fin n,
      (entryCLM i j).comp (goeCLM n))
  have h := gaussian_add_constant (coordinates_gaussian.map_fun L)
    (fun _ : Fin n => (n:ℝ)*(β^2/(n:ℝ)))
  apply h.congr
  exact Eventually.of_forall (fun g => by
    ext i
    simp [L,augmentedField,augmented,Finset.sum_add_distrib,Finset.mul_sum])

lemma augmentedField_mean (hn : 0 < n) (β : ℝ) (i : Fin n) :
    (∫ g, augmentedField β g i ∂standardArrayLaw (Fin n × Fin n)) = β^2 := by
  have hi (j : Fin n) : Integrable (fun g => augmented β g i j)
      (standardArrayLaw (Fin n × Fin n)) :=
    (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β).add (integrable_const _)
  change (∫ g, ∑ j : Fin n, augmented β g i j ∂standardArrayLaw (Fin n × Fin n)) = _
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [augmented_mean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')

lemma augmentedField_covariance (hn : 0 < n) (β : ℝ) (i k : Fin n) :
    cov[fun g => augmentedField β g i,fun g => augmentedField β g k;
      standardArrayLaw (Fin n × Fin n)] = (if i=k then β^2 else 0)+β^2/(n:ℝ) := by
  have hLp (i j : Fin n) : MemLp (fun g => augmented β g i j) 2
      (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp i j).const_mul β).add (memLp_const _)
  unfold augmentedField
  rw [covariance_fun_sum_fun_sum (hLp i) (hLp k)]
  simp_rw [augmented_covariance hn,ite_and,mul_add,Finset.sum_add_distrib,mul_ite,
    mul_one,mul_zero,Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  split_ifs <;> simp [mul_div_cancel₀ _ hn0]

theorem augmentedField_law (hn : 0 < n) (β : ℝ) :
    (standardArrayLaw (Fin n × Fin n)).map (augmentedField β) =
      (standardArrayLaw (Option (Fin n))).map
        (sharedGaussianField (β^2) β (β/sqrt n)) := by
  apply SKRatioGaussian.GaussianRegression.law_eq_of_mean_covariance
    (augmentedField_gaussian β) (sharedGaussianField_gaussian n _ _ _)
  · intro i
    rw [augmentedField_mean hn,sharedGaussianField_mean]
  · intro i k
    rw [augmentedField_covariance hn,sharedGaussianField_covariance,div_pow,
      sq_sqrt (Nat.cast_nonneg n)]

def constantDirection (n : ℕ) : Fin n → ℝ := fun _ => (sqrt n)⁻¹

lemma constantDirection_unit (hn : 0 < n) :
    ∑ i : Fin n, constantDirection n i^2 = 1 := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [constantDirection,inv_pow,sq_sqrt (Nat.cast_nonneg n),hn0]

lemma constantColumn_unit (hn : 0 < n) :
    (queryColumn (constantDirection n))ᵀ * queryColumn (constantDirection n) = 1 :=
  queryColumn_unit _ (constantDirection_unit hn)

def fieldProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  residualProjection (queryColumn (constantDirection n))

lemma augmentedField_query (hn : 0 < n) (β : ℝ) (g : (Fin n × Fin n) → ℝ) (i : Fin n) :
    augmentedField β g i = sqrt n*β*(goe g*queryColumn (constantDirection n)) i 0+β^2 := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs0 : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  simp only [augmentedField,augmented,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Matrix.mul_apply,queryColumn,constantDirection,←Finset.sum_mul]
  field_simp

theorem field_residual_independent (hn : 0 < n) (β : ℝ) :
    IndepFun (fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
      (fieldProjection n*(β • goe g)*fieldProjection n) p.1 p.2)
      (augmentedField β) (standardArrayLaw (Fin n × Fin n)) := by
  have h := residual_answer_independent hn (queryColumn (constantDirection n)) (constantColumn_unit hn)
  have hc := h.comp
    (φ := fun x : (Fin n × Fin n) → ℝ => fun p => β*x p)
    (ψ := fun y : (Fin n × Fin 1) → ℝ => fun i => sqrt n*β*y (i,0)+β^2)
    (by fun_prop) (by fun_prop)
  convert! hc using 1
  · funext g p
    simp [fieldProjection]
  · funext g i
    exact augmentedField_query hn β g i

lemma projected_rows_formula (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (i j : Fin n) :
    M i j = (fieldProjection n*M*fieldProjection n) i j +
      ((∑ k, M i k)+(∑ k, M j k)-(∑ l, ∑ k, M l k)/(n:ℝ))/(n:ℝ) := by
  have hs0 : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hr := congrFun (congrFun
    (regression_decomposition M (queryColumn (constantDirection n)) hM) i) j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,
    queryColumn,constantDirection,Fin.sum_univ_one,←Finset.sum_mul,←Finset.mul_sum] at hr
  change M i j = _ + _ - _ + (fieldProjection n*M*fieldProjection n) i j at hr
  have hs : (sqrt (n:ℝ))⁻¹ * (sqrt n)⁻¹ = (n:ℝ)⁻¹ := by
    rw [←mul_inv_rev,←pow_two,sq_sqrt (Nat.cast_nonneg n)]
  calc
    M i j = _ := hr
    _ = _ := by
      calc
        _ = (fieldProjection n*M*fieldProjection n) i j +
            ((∑ k, M i k)+(∑ k, M j k)-(∑ l, ∑ k, M l k)*
              ((sqrt (n:ℝ))⁻¹*(sqrt n)⁻¹))*((sqrt (n:ℝ))⁻¹*(sqrt n)⁻¹) := by ring
        _ = _ := by rw [hs]; simp only [div_eq_mul_inv]

theorem augmented_decomposition (hn : 0 < n) (β : ℝ)
    (g : (Fin n × Fin n) → ℝ) (i j : Fin n) :
    augmented β g i j =
      (fieldProjection n*(β • goe g)*fieldProjection n) i j +
      (augmentedField β g i + augmentedField β g j -
        (∑ k, augmentedField β g k)/(n:ℝ))/(n:ℝ) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hM : (β • goe g)ᵀ = β • goe g := by
    simp only [Matrix.transpose_smul,goe_symmetric]
  have h := projected_rows_formula hn (β • goe g) hM i j
  have hsum (i : Fin n) : augmentedField β g i = (∑ k, (β • goe g) i k) + β^2 := by
    simp [augmentedField,augmented,Finset.sum_add_distrib,mul_div_cancel₀ _ hn0]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change β*goe g i j+β^2/(n:ℝ) = _
  rw [show β*goe g i j = (β • goe g) i j from rfl,h]
  field_simp
  ring

end SKRatio.Planted

end
end

end OAI
