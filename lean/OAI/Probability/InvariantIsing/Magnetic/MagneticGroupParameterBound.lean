import OAI.Probability.InvariantIsing.Magnetic.MagneticVariational

namespace OAI

/-! The finite-group magnetic field value has a parameter modulus uniform
in all covariance partitions of bounded height. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma constrainedFieldValue_abs_le_height (h : FieldStep) {s H : ℝ}
    (hs : |s| ≤ 1) (hH : h.height (Fin.last h.depth) ≤ H) :
    |constrainedFieldValue h s| ≤ Real.log 2+H/2 := by
  have hb := constrainedFieldValue_bounds h hs
  have h0 : 0 ≤ H := (h.nonneg _).trans hH
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma magneticGroupValue_parameter_modulus {A : Type*} [Fintype A]
    (γ δ s t : A → ℝ) {r H : ℝ} (hr : r<1)
    (hs : ∀ a, |s a| ≤ r) (ht : ∀ a, |t a| ≤ r)
    (h : FieldStep) (hH : h.height (Fin.last h.depth) ≤ H) :
    |magneticGroupValue γ s h-magneticGroupValue δ t h| ≤
      (Real.log 2+H/2)*(∑ a, |γ a-δ a|)+
        ((Real.log 2+H/2)/(1-r))*(∑ a, |δ a| *|s a-t a|) := by
  unfold magneticGroupValue
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ a, |γ a*constrainedFieldValue h (s a)-δ a*constrainedFieldValue h (t a)|) ≤
      ∑ a, (|γ a-δ a| *(Real.log 2+H/2)+
        |δ a| *(((Real.log 2+H/2)/(1-r))*|s a-t a|)) := by
      apply Finset.sum_le_sum
      intro a _
      have he : γ a*constrainedFieldValue h (s a)-δ a*constrainedFieldValue h (t a) =
          (γ a-δ a)*constrainedFieldValue h (s a)+
            δ a*(constrainedFieldValue h (s a)-constrainedFieldValue h (t a)) := by ring
      rw [he]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (constrainedFieldValue_abs_le_height h ((hs a).trans hr.le) hH) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (constrainedFieldValue_magnetization_lipschitz h hr (hs a) (ht a) hH) (abs_nonneg _))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum,Finset.mul_sum]
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring

lemma magneticGroupValue_parameters_uniform {A : Type*} [Fintype A]
    (γ s : ℕ → A → ℝ) (δ t : A → ℝ)
    (hγ : Tendsto γ atTop (𝓝 δ)) (hs : Tendsto s atTop (𝓝 t))
    {r : ℝ} (hr : r<1) (hst : ∀ a, |t a| ≤ r)
    (hsk : ∀ᶠ k in atTop, ∀ a, |s k a| ≤ r) (H : ℝ) :
    ∀ ε>0, ∀ᶠ k in atTop, ∀ h : FieldStep, h.height (Fin.last h.depth) ≤ H →
      |magneticGroupValue (γ k) (s k) h-magneticGroupValue δ t h|<ε := by
  have he : Tendsto (fun k => (Real.log 2+H/2)*(∑ a, |γ k a-δ a|)+
      ((Real.log 2+H/2)/(1-r))*(∑ a, |δ a| *|s k a-t a|)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ∑ a, |γ k a-δ a|) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ
        (fun a _ => (((tendsto_pi_nhds.mp hγ) a).sub (tendsto_const_nhds (x := δ a))).abs)
    have h2 : Tendsto (fun k => ∑ a, |δ a| *|s k a-t a|) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ
        (fun a _ => ((((tendsto_pi_nhds.mp hs) a).sub (tendsto_const_nhds (x := t a))).abs).const_mul |δ a|)
    simpa using (h1.const_mul (Real.log 2+H/2)).add (h2.const_mul ((Real.log 2+H/2)/(1-r)))
  intro ε hε
  filter_upwards [hsk,he.eventually (Iio_mem_nhds hε)] with k hk he h hH
  exact (magneticGroupValue_parameter_modulus (γ k) δ (s k) t hr hk hst h hH).trans_lt he

end InvariantIsing

end

end OAI
