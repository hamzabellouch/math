import OAI.Analysis.LpDimension.ConvolutionError

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

lemma exp_abs_le_pair (x : ℝ) : Real.exp |x| ≤ Real.exp x+Real.exp (-x) := by
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.exp_pos x]

lemma mixed_exponential_tail (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J T a b : ℝ), 0 < J → T ≤ |b| →
      |a|^p ≤ C*(2*J)^p*Real.exp (-T/(2*J))*
        (Real.exp (a/J)+Real.exp (-a/J)+Real.exp (b/J)+Real.exp (-b/J)) := by
  obtain ⟨C,hC,hpow⟩ := rpow_le_constant_exp p hp
  refine ⟨C,hC,?_⟩
  intro J T a b hJ hT
  have hJ2 : 0 < 2*J := by positivity
  have hscale : |a|^p ≤ C*(2*J)^p*Real.exp (|a|/(2*J)) := by
    have hh := mul_le_mul_of_nonneg_right (hpow (|a|/(2*J)) (by positivity))
      (Real.rpow_nonneg hJ2.le p)
    rw [Real.div_rpow (abs_nonneg _) hJ2.le,div_mul_cancel₀ _ (Real.rpow_pos_of_pos hJ2 p).ne'] at hh
    nlinarith
  have hexp : Real.exp ((|a|+T)/(2*J)) ≤
      Real.exp (a/J)+Real.exp (-a/J)+Real.exp (b/J)+Real.exp (-b/J) := by
    rcases le_total |a| |b| with hab|hba
    · have hh : (|a|+T)/(2*J) ≤ |b/J| := by
        rw [abs_div,abs_of_pos hJ]
        apply (div_le_div_iff₀ hJ2 hJ).mpr
        nlinarith
      have hbexp := exp_abs_le_pair (b/J)
      rw [← neg_div] at hbexp
      exact (Real.exp_le_exp.mpr hh).trans (by linarith [Real.exp_pos (a/J),Real.exp_pos (-a/J)])
    · have hh : (|a|+T)/(2*J) ≤ |a/J| := by
        rw [abs_div,abs_of_pos hJ]
        apply (div_le_div_iff₀ hJ2 hJ).mpr
        nlinarith
      have haexp := exp_abs_le_pair (a/J)
      rw [← neg_div] at haexp
      exact (Real.exp_le_exp.mpr hh).trans (by linarith [Real.exp_pos (b/J),Real.exp_pos (-b/J)])
  calc
    _ ≤ C*(2*J)^p*Real.exp (|a|/(2*J)) := hscale
    _ = C*(2*J)^p*Real.exp (-T/(2*J))*Real.exp ((|a|+T)/(2*J)) := by
      rw [mul_assoc (C*(2*J)^p),← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

variable {E : Type uE} [Fintype E]

def globalCut (T : ℝ) (z : E → ℝ) : E → ℝ := if ∀ e, |z e| ≤ T then z else 0

lemma measurable_globalCut (T : ℝ) : Measurable (globalCut (E := E) T) := by
  classical
  unfold globalCut
  apply Measurable.ite _ measurable_id measurable_const
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => measurableSet_le (by fun_prop) measurable_const)

lemma globalCut_bound (T : ℝ) (hT : 0 ≤ T) (z : E → ℝ) (e : E) :
    |globalCut T z e| ≤ T := by
  classical
  unfold globalCut
  split_ifs with h
  · exact h e
  · simpa only [Pi.zero_apply,abs_zero] using hT

lemma globalCut_submodule (T : ℝ) (z : E → ℝ) (V : Submodule ℝ (E → ℝ)) (hz : z ∈ V) :
    globalCut T z ∈ V := by
  classical
  unfold globalCut
  split_ifs
  · exact hz
  · exact V.zero_mem

lemma globalCut_power_le (T p : ℝ) (hp : 0 < p) (z : E → ℝ) (e : E) :
    |globalCut T z e|^p ≤ |z e|^p := by
  classical
  unfold globalCut
  split_ifs
  · exact le_refl _
  · simp only [Pi.zero_apply,abs_zero,Real.zero_rpow hp.ne']
    positivity

lemma globalCut_moments (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) [Fintype E]
      (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (J T : ℝ) (_hJ : 0 < J) (_hT : 0 ≤ T)
      (_hI : ∀ e, Integrable (fun z => |z e|^p) μ)
      (_hExp : ∀ e (s : ℝ), |s|=1 → Integrable (fun z => Real.exp (s*z e/J)) μ ∧
        (∫ z, Real.exp (s*z e/J) ∂μ) ≤ Real.exp 1),
      ∀ e, |(∫ z, |globalCut T z e|^p ∂μ)-(∫ z, |z e|^p ∂μ)| ≤
        C*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
  classical
  obtain ⟨C,hC,hScalar⟩ := mixed_exponential_tail p hp.le
  refine ⟨4*Real.exp 1*C,by positivity,?_⟩
  intro E _ μ _ J T hJ hT hI hExp e
  let L := C*(2*J)^p*Real.exp (-T/(2*J))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let Q : (E → ℝ) → E → ℝ := fun z a => Real.exp (z a/J)+Real.exp (-z a/J)
  have hQI (a : E) : Integrable (fun z => Q z a) μ := by
    have h₁ := (hExp a 1 (by norm_num)).1
    have h₂ := (hExp a (-1) (by norm_num)).1
    simp only [one_mul,neg_one_mul] at h₁ h₂
    exact h₁.add h₂
  have hQb (a : E) : (∫ z, Q z a ∂μ) ≤ 2*Real.exp 1 := by
    have h₁ := hExp a 1 (by norm_num)
    have h₂ := hExp a (-1) (by norm_num)
    simp only [one_mul,neg_one_mul] at h₁ h₂
    rw [show (fun z => Q z a)=(fun z => Real.exp (z a/J)+Real.exp (-z a/J)) from rfl, integral_add h₁.1 h₂.1]
    linarith [h₁.2,h₂.2]
  have hCutI : Integrable (fun z => |globalCut T z e|^p) μ :=
    bounded_power_integrable μ (fun z => globalCut T z e) ((measurable_pi_apply e).comp (measurable_globalCut T))
      p T hp hT (fun z => globalCut_bound T hT z e)
  have hpoint (z : E → ℝ) : |z e|^p-|globalCut T z e|^p ≤ L*(∑ a, (Q z e+Q z a)) := by
    by_cases hz : ∀ a, |z a| ≤ T
    · simp only [globalCut,ite_eq_left hz,sub_self]
      exact mul_nonneg hL (Finset.sum_nonneg (fun a _ => by dsimp [Q]; positivity))
    · obtain ⟨a,ha⟩ := not_forall.mp hz
      have hh := hScalar J T (z e) (z a) hJ (le_of_not_ge ha)
      have hsum : Q z e+Q z a ≤ ∑ a, (Q z e+Q z a) :=
        Finset.single_le_sum (f := fun b => Q z e+Q z b) (fun b _ => by dsimp [Q]; positivity) (Finset.mem_univ a)
      simp only [globalCut,ite_eq_right hz,Pi.zero_apply,abs_zero,Real.zero_rpow hp.ne',sub_zero]
      apply hh.trans
      simpa only [L,Q,add_assoc] using mul_le_mul_of_nonneg_left hsum hL
  have hbound : (∫ z, |z e|^p-|globalCut T z e|^p ∂μ) ≤
      L*(4*Real.exp 1*(Fintype.card E : ℝ)) := by
    calc
      _ ≤ ∫ z, L*(∑ a, (Q z e+Q z a)) ∂μ :=
        integral_mono ((hI e).sub hCutI) ((integrable_finsetSum _ (fun a _ => (hQI e).add (hQI a))).const_mul L) hpoint
      _ = L*(∑ a, ((∫ z, Q z e ∂μ)+(∫ z, Q z a ∂μ))) := by
        rw [integral_const_mul,integral_finsetSum]
        · congr 1; apply Finset.sum_congr rfl; intro a _; exact integral_add (hQI e) (hQI a)
        · intro a _; exact (hQI e).add (hQI a)
      _ ≤ L*(∑ _a : E, 4*Real.exp 1) := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply Finset.sum_le_sum
        intro a _
        linarith [hQb e,hQb a]
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hnonneg : (∫ z, |globalCut T z e|^p ∂μ) ≤ ∫ z, |z e|^p ∂μ :=
    integral_mono hCutI (hI e) (fun z => globalCut_power_le T p hp z e)
  rw [integral_sub (hI e) hCutI] at hbound
  rw [abs_of_nonpos (sub_nonpos.mpr hnonneg)]
  dsimp [L] at hbound
  nlinarith

end SubpolynomialLp

end

end OAI
