import Mathlib
import OAI.Analysis.HardSphere.FormDomain.HilbertJet

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma cfc_eigen_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) (hd : DifferentiableAt ℝ f r)
    (u : E) (hu : T u = r • u) :
    cfc (p := IsSelfAdjoint) f T u = f r • u := by
  have hg : Continuous (dslope f r) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (s := Set.univ) (Filter.univ_mem)).mpr ⟨hf.continuousOn,hd⟩
  have heq : (fun x ↦ dslope f r x * (x-r) + f r) = f := by
    funext x
    have hh := sub_smul_dslope f r x
    simp only [smul_eq_mul] at hh
    rw [mul_comm,hh,sub_add_cancel]
  have hcalc : cfc (p := IsSelfAdjoint) f T = cfc (p := IsSelfAdjoint) (dslope f r) T * (T - algebraMap ℝ (E →L[ℂ] E) r) +
      algebraMap ℝ (E →L[ℂ] E) (f r) := by
    conv_lhs => rw [← heq]
    rw [cfc_add T (fun x ↦ dslope f r x * (x-r)) (fun _ ↦ f r)
        (hg.mul (continuous_id.sub continuous_const)).continuousOn continuousOn_const,
      cfc_mul (dslope f r) (fun x ↦ x-r) T hg.continuousOn (continuous_id.sub continuous_const).continuousOn,
      cfc_sub (fun x ↦ x) (fun _ ↦ r) T continuous_id.continuousOn continuousOn_const,
      cfc_id' ℝ T hT,cfc_const r T hT,cfc_const (f r) T hT]
  rw [hcalc]
  simp only [add_apply,mul_apply_eq_comp,
    sub_apply,ContinuousLinearMap.algebraMap_apply,hu,sub_self,map_zero,zero_add]

def heatScalar (t x : ℝ) : ℝ := Real.exp t * expNegInvGlue (x/t)

lemma heatScalar_smooth (t : ℝ) : ContDiff ℝ 1 (heatScalar t) := by
  unfold heatScalar
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_id.div_const t))

lemma heatScalar_nonneg (t x : ℝ) : 0 ≤ heatScalar t x :=
  mul_nonneg (Real.exp_pos t).le (expNegInvGlue.nonneg _)

lemma heatScalar_zero (t : ℝ) : heatScalar t 0 = 0 := by simp [heatScalar]

lemma heatScalar_of_pos {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    heatScalar t x = Real.exp (t - t/x) := by
  unfold heatScalar expNegInvGlue
  rw [ite_eq_right (not_le.mpr (div_pos hx ht)),← Real.exp_add]
  congr 1
  field_simp
  ring

lemma heatScalar_resolvent {t E : ℝ} (ht : 0 < t) (hE : 0 ≤ E) :
    heatScalar t (1+E)⁻¹ = Real.exp (-t*E) := by
  rw [heatScalar_of_pos ht (inv_pos.mpr (by linarith))]
  congr 1
  rw [div_inv_eq_mul]
  ring

lemma heatScalar_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    heatScalar (s+t) x = heatScalar s x * heatScalar t x := by
  by_cases hx : 0 < x
  · rw [heatScalar_of_pos (add_pos hs ht) hx,heatScalar_of_pos hs hx,heatScalar_of_pos ht hx,← Real.exp_add]
    congr 1
    ring
  · have hx' : x ≤ 0 := le_of_not_gt hx
    simp [heatScalar,expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx' hs.le),
      expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx' (add_pos hs ht).le)]

local instance scalarOperatorRealAlgebra (N : ℕ) (L : Length) :
    Algebra ℝ (ScalarL2 N L →L[ℂ] ScalarL2 N L) := Algebra.restrictScalars ℝ ℂ _

def formHeat (N : ℕ) (L : Length) (a t : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  cfc (p := IsSelfAdjoint) (heatScalar t) (formResolvent N L a)

lemma formHeat_add (N : ℕ) (L : Length) (a : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    formHeat N L a (s+t) = formHeat N L a s * formHeat N L a t := by
  unfold formHeat
  rw [show heatScalar (s+t) = (fun x ↦ heatScalar s x * heatScalar t x) from funext (heatScalar_add hs ht)]
  exact cfc_mul _ _ _ (heatScalar_smooth s).continuous.continuousOn (heatScalar_smooth t).continuous.continuousOn

lemma formHeat_nonneg (N : ℕ) (L : Length) (a t : ℝ) : 0 ≤ formHeat N L a t := by
  unfold formHeat
  exact cfc_nonneg (fun x _ ↦ heatScalar_nonneg t x)

lemma IsGroundVector.heat_eigenvector {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {t : ℝ} (ht : 0 < t) :
    formHeat N L a t u.1 = (Real.exp (-t*energy u):ℂ) • u.1 := by
  have hE : 0 ≤ energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hh : formResolvent N L a u.1 = ((1+energy u)⁻¹:ℝ) • u.1 := by
    rw [← IsScalarTower.algebraMap_smul ℂ ((1+energy u)⁻¹:ℝ) u.1]
    change formResolvent N L a u.1 = (((1+energy u)⁻¹:ℝ):ℂ) • u.1
    simpa only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one] using hu.resolvent_eigenvector
  rw [formHeat, cfc_eigen_apply _ (formResolvent_isPositive N L a).isSelfAdjoint _
    (heatScalar_smooth t).continuous _ ((heatScalar_smooth t).differentiable (by norm_num)).differentiableAt _ hh,
    heatScalar_resolvent ht hE]
  exact (IsScalarTower.algebraMap_smul ℂ _ _).symm

lemma strong_apply_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (T₀ : E →L[ℂ] E) (C : ℝ)
    (hC : ∀ n, ‖T n‖ ≤ C) (hT : ∀ u, Tendsto (fun n ↦ T n u) atTop (𝓝 (T₀ u)))
    (v : ℕ → E) (v₀ : E) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n ↦ T n (v n)) atTop (𝓝 (T₀ v₀)) := by
  have hzero : Tendsto (fun n ↦ T n (v n-v₀)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ (T n).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)))
    simpa using (tendsto_const_nhds.mul ((hv.sub_const v₀).norm))
  have hh := hzero.add (hT v₀)
  simpa only [map_sub,sub_add_cancel,zero_add] using hh

lemma strong_pow_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (T₀ : E →L[ℂ] E)
    (hC : ∀ n, ‖T n‖ ≤ 1) (hT : ∀ u, Tendsto (fun n ↦ T n u) atTop (𝓝 (T₀ u)))
    (k : ℕ) (u : E) : Tendsto (fun n ↦ (T n ^ k) u) atTop (𝓝 ((T₀^k) u)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa only [pow_succ',mul_apply_eq_comp] using
      strong_apply_tendsto T T₀ 1 hC hT (fun n ↦ (T n^k) u) ((T₀^k) u) ih

lemma strong_polynomial_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : ℕ → E →L[ℂ] E) (T₀ : E →L[ℂ] E)
    (hC : ∀ n, ‖T n‖ ≤ 1) (hT : ∀ u, Tendsto (fun n ↦ T n u) atTop (𝓝 (T₀ u)))
    (q : Polynomial ℝ) (u : E) :
    Tendsto (fun n ↦ (Polynomial.aeval (T n) q) u) atTop (𝓝 ((Polynomial.aeval T₀ q) u)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,add_apply] using hp.add hq
  | monomial k a =>
    simpa only [Polynomial.aeval_monomial,mul_apply_eq_comp,ContinuousLinearMap.algebraMap_apply] using
      (strong_pow_tendsto T T₀ hC hT k u).const_smul a

lemma strong_cfc_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : ℕ → E →L[ℂ] E) (T₀ : E →L[ℂ] E)
    (hC : ∀ n, ‖T n‖ ≤ 1) (hC₀ : ‖T₀‖ ≤ 1)
    (hsa : ∀ n, IsSelfAdjoint (T n)) (hsa₀ : IsSelfAdjoint T₀)
    (hT : ∀ u, Tendsto (fun n ↦ T n u) atTop (𝓝 (T₀ u)))
    (f : ℝ → ℝ) (hf : Continuous f) (u : E) :
    Tendsto (fun n ↦ cfc (p := IsSelfAdjoint) f (T n) u) atTop
      (𝓝 (cfc (p := IsSelfAdjoint) f T₀ u)) := by
  nontriviality E
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (3 * (‖u‖+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨q,hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf.continuousOn δ hδ
  have herr (S : E →L[ℂ] E) (hS : ‖S‖ ≤ 1) (hsaS : IsSelfAdjoint S) :
      ‖cfc (p := IsSelfAdjoint) f S - Polynomial.aeval S q‖ ≤ δ := by
    rw [← cfc_polynomial q S hsaS,← cfc_sub f q.eval S hf.continuousOn q.continuous.continuousOn]
    apply norm_cfc_le hδ.le
    intro x hx
    have hx' : x ∈ Icc (-1:ℝ) 1 := by
      have hh := (spectrum.norm_le_norm_of_mem hx).trans hS
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hh
    simpa only [Real.norm_eq_abs,abs_sub_comm] using (hq x hx').le
  obtain ⟨n₀,hn₀⟩ := Metric.tendsto_atTop.mp (strong_polynomial_tendsto T T₀ hC hT q u)
    (ε/3) (by positivity)
  refine ⟨n₀,fun n hn ↦ ?_⟩
  have hn' := hn₀ n hn
  have he₁ : ‖cfc (p := IsSelfAdjoint) f (T n) u - (Polynomial.aeval (T n) q) u‖ ≤ δ * ‖u‖ := by
    change ‖(cfc (p := IsSelfAdjoint) f (T n) - Polynomial.aeval (T n) q) u‖ ≤ _
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (herr (T n) (hC n) (hsa n)) (norm_nonneg u))
  have he₂ : ‖(Polynomial.aeval T₀ q) u - cfc (p := IsSelfAdjoint) f T₀ u‖ ≤ δ * ‖u‖ := by
    rw [norm_sub_rev]
    change ‖(cfc (p := IsSelfAdjoint) f T₀ - Polynomial.aeval T₀ q) u‖ ≤ _
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (herr T₀ hC₀ hsa₀) (norm_nonneg u))
  have hδn : δ * ‖u‖ < ε/3 := by
    have hden : 0 < 3 * (‖u‖+1) := by positivity
    dsimp [δ]
    rw [div_mul_eq_mul_div,div_lt_div_iff₀ hden (by norm_num : (0:ℝ)<3)]
    nlinarith [norm_nonneg u]
  rw [dist_eq_norm] at hn' ⊢
  have hh := dist_triangle (cfc (p := IsSelfAdjoint) f (T n) u)
    ((Polynomial.aeval (T n) q) u) (cfc (p := IsSelfAdjoint) f T₀ u)
  have hh' := dist_triangle ((Polynomial.aeval (T n) q) u)
    ((Polynomial.aeval T₀ q) u) (cfc (p := IsSelfAdjoint) f T₀ u)
  simp only [dist_eq_norm] at hh hh'
  linarith

lemma formHeat_innerRadius_tendsto (N : ℕ) (L : Length) (a t : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun n ↦ formHeat N L (innerRadius a n) t f) atTop (𝓝 (formHeat N L a t f)) := by
  exact strong_cfc_tendsto (fun n ↦ formResolvent N L (innerRadius a n))
    (formResolvent N L a) (fun n ↦ formResolvent_norm_le_one N L _)
    (formResolvent_norm_le_one N L a) (fun n ↦ (formResolvent_isPositive N L _).isSelfAdjoint)
    (formResolvent_isPositive N L a).isSelfAdjoint (formResolvent_innerRadius_tendsto N L a)
    (heatScalar t) (heatScalar_smooth t).continuous f

end HardSphere

end

end OAI
