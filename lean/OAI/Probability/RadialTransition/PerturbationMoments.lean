import OAI.Probability.RadialTransition.CellInteractions

namespace OAI

universe uX uI

noncomputable section


open MeasureTheory Set Filter

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

lemma secondMoment_of_exponential {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Measurable f) {c C : ℝ} (hc : 0 < c)
    (hi : Integrable (fun x => Real.exp (c*(f x)^2)) μ)
    (hb : ∫ x, Real.exp (c*(f x)^2) ∂μ ≤ C) :
    Integrable (fun x => (f x)^2) μ ∧ (∫ x, (f x)^2 ∂μ) ≤ C/c := by
  have hbound (x : X) : (f x)^2 ≤ c⁻¹ * Real.exp (c*(f x)^2) := by
    have hh := Real.add_one_le_exp (c*(f x)^2)
    rw [mul_comm c⁻¹, ← div_eq_mul_inv]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm, div_eq_mul_inv] using (le_of_lt (by linarith : (f x)^2*c < Real.exp (c*(f x)^2)))
  have hi' : Integrable (fun x => (f x)^2) μ :=
    (hi.const_mul c⁻¹).mono' (hf.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))] using hbound x))
  refine ⟨hi', ?_⟩
  have hh := integral_mono hi' (hi.const_mul c⁻¹) hbound
  rw [integral_const_mul] at hh
  exact hh.trans (by simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le))

lemma pairMoment_of_second {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C : ℝ} (hiF : Integrable (fun x => (f x)^2) μ) (hiG : Integrable (fun x => (g x)^2) μ)
    (hbF : ∫ x, (f x)^2 ∂μ ≤ C) (hbG : ∫ x, (g x)^2 ∂μ ≤ C) :
    Integrable (fun x => f x * g x) μ ∧ (∫ x, f x * g x ∂μ) ≤ C := by
  have hb (x : X) : |f x * g x| ≤ ((f x)^2+(g x)^2)/2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (f x-g x), sq_nonneg (f x+g x)]
  have hi : Integrable (fun x => f x*g x) μ :=
    ((hiF.add hiG).div_const 2).mono' (hf.mul hg).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hb x))
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi ((hiF.add hiG).div_const 2) (fun x => (le_abs_self _).trans (hb x))
  simp only [Pi.add_apply] at hh
  rw [integral_div, integral_add hiF hiG] at hh
  linarith

theorem log_partition_perturbation {X : Type uX} {I : Type uI} [MeasurableSpace X] [Fintype I]
    {μ : Measure X} {E F : X → ℝ} (hE : Measurable E) (hF : Measurable F)
    (hiE : Integrable (fun x => Real.exp (-E x)) μ)
    (hiF : Integrable (fun x => Real.exp (-F x)) μ)
    (hpE : 0 < boltzmannPartition μ E) (hpF : 0 < boltzmannPartition μ F)
    (n : I → X → ℝ) (hn : ∀ i, Measurable (n i))
    (K : I → I → ℝ) (hK : ∀ i j, 0 ≤ K i j) {C : ℝ}
    (hsE : ∀ i, Integrable (fun x => (n i x)^2) (boltzmannMeasure μ E))
    (hsF : ∀ i, Integrable (fun x => (n i x)^2) (boltzmannMeasure μ F))
    (hbE : ∀ i, ∫ x, (n i x)^2 ∂boltzmannMeasure μ E ≤ C)
    (hbF : ∀ i, ∫ x, (n i x)^2 ∂boltzmannMeasure μ F ≤ C)
    (hd : ∀ x, |F x-E x| ≤ ∑ i, ∑ j, K i j * n i x * n j x) :
    |Real.log (boltzmannPartition μ E) - Real.log (boltzmannPartition μ F)| ≤
      C * ∑ i, ∑ j, K i j := by
  have oneSide (E F : X → ℝ) (hE : Measurable E) (hF : Measurable F)
      (hiE : Integrable (fun x => Real.exp (-E x)) μ)
      (hiF : Integrable (fun x => Real.exp (-F x)) μ)
      (hpE : 0 < boltzmannPartition μ E) (hpF : 0 < boltzmannPartition μ F)
      (hsE : ∀ i, Integrable (fun x => (n i x)^2) (boltzmannMeasure μ E))
      (hbE : ∀ i, ∫ x, (n i x)^2 ∂boltzmannMeasure μ E ≤ C)
      (hd : ∀ x, |F x-E x| ≤ ∑ i, ∑ j, K i j * n i x * n j x) :
      Real.log (boltzmannPartition μ E) - Real.log (boltzmannPartition μ F) ≤ C*∑ i, ∑ j, K i j := by
    have hp (i j : I) := pairMoment_of_second (hn i) (hn j) (hsE i) (hsE j) (hbE i) (hbE j)
    have hiTerm (i j : I) : Integrable (fun x => K i j * n i x * n j x) (boltzmannMeasure μ E) := by
      simpa only [mul_assoc] using (hp i j).1.const_mul (K i j)
    have hiSum := integrable_finsetSum (Finset.univ : Finset I) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset I) (fun j _ => hiTerm i j))
    have hiDiff : Integrable (fun x => F x-E x) (boltzmannMeasure μ E) :=
      hiSum.mono' (hF.sub hE).aestronglyMeasurable (Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hd x))
    apply (log_boltzmann_difference_le hE hiE hiF hpE hpF hiDiff).trans
    apply (integral_mono hiDiff hiSum (fun x => (le_abs_self _).trans (hd x))).trans
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hiTerm i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hiTerm _ j)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simp_rw [mul_assoc, integral_const_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp i j).2 (hK i j)
  apply abs_le.mpr
  constructor
  · have hh := oneSide F E hF hE hiF hiE hpF hpE hsF hbF (fun x => by simpa only [abs_sub_comm] using hd x)
    linarith
  · exact oneSide E F hE hF hiE hiF hpE hpF hsE hbE hd

end RadialTransition

end

end OAI
