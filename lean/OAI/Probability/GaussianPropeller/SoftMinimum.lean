import OAI.Probability.GaussianPropeller.SmoothedConcavity

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal

open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace GaussianPropeller.SoftMin

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

noncomputable def Z (v : ι → E) (x : E) : ℝ := ∑ i, Real.exp (-⟪v i,x⟫)
noncomputable def weight (v : ι → E) (x : E) (i : ι) : ℝ := Real.exp (-⟪v i,x⟫)/Z v x
noncomputable def value (v : ι → E) (x : E) : ℝ := -Real.log (Z v x)
noncomputable def grad (v : ι → E) (x : E) : E := ∑ i, weight v x i • v i
noncomputable def hess (v : ι → E) (x : E) : E →L[ℝ] E :=
  ∑ i, (weight v x i) • ((innerSL ℝ (grad v x-v i)).smulRight (v i))

lemma Z_pos (v : ι → E) (x : E) : 0 < Z v x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
lemma weight_pos (v : ι → E) (x : E) (i : ι) : 0 < weight v x i :=
  div_pos (Real.exp_pos _) (Z_pos v x)
lemma sum_weight (v : ι → E) (x : E) : ∑ i, weight v x i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt (Z_pos v x))
omit [Nonempty ι] in
lemma continuous_Z [Nonempty ι] (v : ι → E) : Continuous (Z v) := by unfold Z; fun_prop
lemma continuous_weight (v : ι → E) (i : ι) : Continuous (fun x => weight v x i) := by
  exact (by fun_prop : Continuous (fun x : E => Real.exp (-⟪v i,x⟫))).div
    (continuous_Z v) (fun x => ne_of_gt (Z_pos v x))
lemma continuous_grad (v : ι → E) : Continuous (grad v) := by
  unfold grad
  exact continuous_finsetSum _ (fun i _ => (continuous_weight v i).smul continuous_const)
lemma continuous_hess (v : ι → E) : Continuous (hess v) := by
  unfold hess
  apply continuous_finsetSum
  intro i _
  have h := continuous_grad v
  have hw := continuous_weight v i
  fun_prop
omit [Nonempty ι] in
lemma inner_grad [Nonempty ι] (v : ι → E) (x e : E) :
    ⟪grad v x,e⟫ = ∑ i, weight v x i*⟪v i,e⟫ := by
  simp only [grad, sum_inner, real_inner_smul_left]
lemma Z_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (Z v) (-(Z v x) • innerSL ℝ (grad v x)) x := by
  have hd (i : ι) : HasFDerivAt (fun y : E => Real.exp (-⟪v i,y⟫))
      (-Real.exp (-⟪v i,x⟫) • innerSL ℝ (v i)) x := by
    convert ((innerSL ℝ (v i)).hasFDerivAt.neg.exp) using 1 <;>
      (first | rfl | (ext y; simp))
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  convert hs using 1 <;> try rfl
  ext e
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, sum_apply,
    inner_grad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [weight]
  field_simp [ne_of_gt (Z_pos v x)]
lemma value_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (value v) (innerSL ℝ (grad v x)) x := by
  have hh := ((Z_fderiv v x).log (ne_of_gt (Z_pos v x))).neg
  convert hh using 1 <;> (first | rfl | (ext y; simp [ne_of_gt (Z_pos v x)]))
lemma weight_fderiv (v : ι → E) (x : E) (i : ι) :
    HasFDerivAt (fun y => weight v y i)
      (weight v x i • innerSL ℝ (grad v x-v i)) x := by
  have hn := ((innerSL ℝ (v i)).hasFDerivAt (x := x)).neg.exp
  have hi := (hasDerivAt_inv (ne_of_gt (Z_pos v x))).comp_hasFDerivAt x (Z_fderiv v x)
  have hh := hn.mul hi
  convert hh using 1 <;> try rfl
  ext e
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, inner_sub_left,
    Pi.neg_apply, Function.comp_def, add_apply, neg_apply]
  dsimp only [weight]
  field_simp [ne_of_gt (Z_pos v x)]
  ring
lemma grad_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (grad v) (hess v x) x := by
  have hd (i : ι) := (weight_fderiv v x i).smul_const (v i)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  convert hs using 1 <;> try rfl
  ext e
  simp [hess, smul_smul]

lemma grad_bound (v : ι → E) {L : ℝ} (hL : ∀ i, ‖v i‖ ≤ L) (x : E) : ‖grad v x‖ ≤ L := by
  calc
    ‖grad v x‖ ≤ ∑ i, ‖weight v x i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i)]
      exact mul_le_mul_of_nonneg_left (hL i) (weight_pos v x i).le
    _ = L := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma hess_bound (v : ι → E) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ i, ‖v i‖ ≤ L) (x : E) :
    ‖hess v x‖ ≤ 2*L^2 := by
  calc
    ‖hess v x‖ ≤ ∑ i, ‖weight v x i • ((innerSL ℝ (grad v x-v i)).smulRight (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*(2*L^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      apply mul_le_mul_of_nonneg_left _ (weight_pos v x i).le
      have hd : ‖grad v x-v i‖ ≤ 2*L := (norm_sub_le _ _).trans (by linarith [grad_bound v hL x, hL i])
      calc
        ‖grad v x-v i‖*‖v i‖ ≤ (2*L)*L := mul_le_mul hd (hL i) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 2*L^2 := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma hess_nonpos (v : ι → E) (x e : E) : ⟪hess v x e,e⟫ ≤ 0 := by
  have hvariance : 0 ≤ ∑ i, weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (weight_pos v x i).le (sq_nonneg _))
  have heq : (∑ i, weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2) =
      -(∑ i, weight v x i*⟪grad v x-v i,e⟫*⟪v i,e⟫) := by
    simp_rw [inner_sub_left]
    have hp (i : ι) : weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2 +
        weight v x i*(⟪grad v x,e⟫-⟪v i,e⟫)*⟪v i,e⟫ =
        weight v x i*⟪grad v x,e⟫^2 - (weight v x i*⟪v i,e⟫)*⟪grad v x,e⟫ := by ring
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_weight, one_mul, ← inner_grad] at hh
    nlinarith only [hh]
  rw [heq] at hvariance
  unfold hess
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    sum_inner, real_inner_smul_left, innerSL_apply_apply, ← mul_assoc]
  linarith only [hvariance]

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma concave_of_hessian {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x)
    (hK : ∀ x e, ⟪K x e,e⟫ ≤ 0) : ConcaveOn ℝ univ f := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let d := y-x
  have hline (s : ℝ) : HasDerivAt (fun r : ℝ => x+r•d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hdf (s : ℝ) : HasDerivAt (fun r : ℝ => f (x+r•d)) ⟪g (x+s•d),d⟫ s := by
    simpa only [Function.comp_def, innerSL_apply_apply] using (hf (x+s•d)).comp_hasDerivAt s (hline s)
  have hdg (s : ℝ) : HasDerivAt (fun r : ℝ => ⟪g (x+r•d),d⟫) ⟪K (x+s•d) d,d⟫ s := by
    simpa using ((hg (x+s•d)).comp_hasDerivAt s (hline s)).inner ℝ (hasDerivAt_const s d)
  have hant : Antitone (fun s : ℝ => ⟪g (x+s•d),d⟫) := antitone_of_hasDerivAt_nonpos hdg (fun s => hK _ _)
  have hconc : ConcaveOn ℝ univ (fun s : ℝ => f (x+s•d)) :=
    Antitone.concaveOn_univ_of_deriv (fun s => (hdf s).differentiableAt) (by
      intro s t hst
      rw [(hdf s).deriv, (hdf t).deriv]
      exact hant hst)
  have hh := hconc.2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ)) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul] at hh
  have heq : x+b•d = a•x+b•y := by
    dsimp [d]
    have haeq : a=1-b := by linarith only [hab]
    rw [haeq]
    module
  simpa only [heq, d, add_sub_cancel, smul_eq_mul] using hh

lemma value_concave {ι : Type uι} [Fintype ι] [Nonempty ι] (v : ι → E) :
    ConcaveOn ℝ univ (value v) := concave_of_hessian (value_fderiv v) (grad_fderiv v) (hess_nonpos v)

lemma value_lipschitz {ι : Type uι} [Fintype ι] [Nonempty ι] (v : ι → E)
    {L : ℝ≥0} (hL : ∀ i, ‖v i‖ ≤ L) : LipschitzWith L (value v) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (value_fderiv v x).differentiableAt)
  intro x
  rw [(value_fderiv v x).fderiv]
  exact_mod_cast (show ‖innerSL ℝ (grad v x)‖ ≤ L by rw [innerSL_apply_norm]; exact grad_bound v hL x)

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma value_le_score [Nonempty ι] (v : ι → E) (x : E) (i : ι) : value v x ≤ ⟪v i,x⟫ := by
  have hh : Real.exp (-⟪v i,x⟫) ≤ Z v x := by
    apply Finset.single_le_sum (f := fun j => Real.exp (-⟪v j,x⟫))
    · intro j _; exact (Real.exp_pos _).le
    · exact Finset.mem_univ i
  have hl := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hl
  dsimp only [value]
  linarith only [hl]

lemma value_tendsto_atBot (v : ι → E) (x : E) (i : ι) (hi : ⟪v i,x⟫ < 0) :
    Tendsto (fun n : ℕ => value (fun j => (n:ℝ) • v j) x) atTop atBot := by
  have hh : Tendsto (fun n : ℕ => (n:ℝ)*⟪v i,x⟫) atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hi
  apply tendsto_atBot_mono (fun n => ?_) hh
  simpa only [real_inner_smul_left] using value_le_score (fun j => (n:ℝ) • v j) x i

lemma value_tendsto_atTop (v : ι → E) (x : E) (hi : ∀ i, 0 < ⟪v i,x⟫) :
    Tendsto (fun n : ℕ => value (fun j => (n:ℝ) • v j) x) atTop atTop := by
  have hz : Tendsto (fun n : ℕ => Z (fun j => (n:ℝ) • v j) x) atTop (𝓝 0) := by
    have hh (i : ι) : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)*⟪v i,x⟫)) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa only [neg_mul, mul_neg] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const_of_neg (neg_neg_of_pos (hi i))
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hh i)
    simpa only [Z, real_inner_smul_left, neg_mul, Finset.sum_const_zero] using ht
  have hzn : Tendsto (fun n : ℕ => Z (fun j => (n:ℝ) • v j) x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall (fun n => Z_pos _ _)⟩
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hzn)

end GaussianPropeller.SoftMin

end OAI
