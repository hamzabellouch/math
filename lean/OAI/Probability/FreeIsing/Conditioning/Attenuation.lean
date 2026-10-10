import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

section Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

lemma integrable_of_measurable_unit_interval {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ w, 0 ≤ f w ∧ f w ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound w).1]
  exact (hbound w).2

lemma integral_mul_le_of_condExp_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ} {q : ℝ}
    (hf : Integrable f μ) (hg : Measurable[m] g)
    (hgBound : ∀ w, 0 ≤ g w ∧ g w ≤ 1)
    (hcond : ∀ᵐ w ∂μ, (μ[f | m]) w ≤ q) :
    (∫ w, f w * g w ∂μ) ≤ q * ∫ w, g w ∂μ := by
  have hgb : @Measurable Ω ℝ mΩ _ g := hg.mono hm le_rfl
  have hgInt := integrable_of_measurable_unit_interval (μ := μ) hgb hgBound
  have hgNorm : ∀ᵐ w ∂μ, ‖g w‖ ≤ 1 := by
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hgBound w).1]
    exact (hgBound w).2
  have hprod := hf.mul_bdd hgb.aestronglyMeasurable hgNorm
  have hpull := condExp_mul_of_stronglyMeasurable_right hg.stronglyMeasurable hprod hf
  calc
    (∫ w, f w * g w ∂μ) = ∫ w, (μ[fun v => f v * g v | m]) w ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ w, (μ[f | m]) w * g w ∂μ := integral_congr_ae hpull
    _ ≤ ∫ w, q * g w ∂μ := by
      apply integral_mono_ae
        (integrable_condExp.mul_bdd hgb.aestronglyMeasurable hgNorm)
        (hgInt.const_mul q)
      filter_upwards [hcond] with w hw
      exact mul_le_mul_of_nonneg_right hw (hgBound w).1
    _ = q * ∫ w, g w ∂μ := integral_const_mul _ _

lemma integral_prod_le_of_condExp_le {q : ℝ} (hq : 0 ≤ q)
    (A : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω) (s : Finset ℕ)
    (hMeas : ∀ i ∈ s, Measurable (A i))
    (hBound : ∀ i ∈ s, ∀ w, 0 ≤ A i w ∧ A i w ≤ 1)
    (hm : ∀ i ∈ s, m i ≤ mΩ)
    (hCE : ∀ i ∈ s, ∀ᵐ w ∂μ, (μ[A i | m i]) w ≤ q)
    (hLater : ∀ i ∈ s, ∀ j ∈ s, i < j → Measurable[m i] (A j)) :
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ q ^ s.card := by
  classical
  revert hMeas hBound hm hCE hLater
  induction s using Finset.induction_on_min with
  | empty =>
      intros
      simp
  | insert i s hmin ih =>
      intro hMeas hBound hm hCE hLater
      have his : i ∉ s := by
        intro hi
        exact (lt_irrefl i) (hmin i hi)
      have hiMem : i ∈ insert i s := Finset.mem_insert_self i s
      have hsMem : ∀ j ∈ s, j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
      have htail : (∫ w, ∏ j ∈ s, A j w ∂μ) ≤ q ^ s.card :=
        ih (fun j hj => hMeas j (hsMem j hj))
          (fun j hj => hBound j (hsMem j hj))
          (fun j hj => hm j (hsMem j hj))
          (fun j hj => hCE j (hsMem j hj))
          (fun j hj k hk => hLater j (hsMem j hj) k (hsMem k hk))
      have hprodMeas : Measurable[m i] (fun w => ∏ j ∈ s, A j w) := by
        apply Finset.measurable_fun_prod
        intro j hj
        exact hLater i hiMem j (hsMem j hj) (hmin j hj)
      have hprodBound : ∀ w, 0 ≤ (∏ j ∈ s, A j w) ∧ (∏ j ∈ s, A j w) ≤ 1 := by
        intro w
        exact ⟨Finset.prod_nonneg (fun j hj => (hBound j (hsMem j hj) w).1),
          Finset.prod_le_one₀ (fun j hj => (hBound j (hsMem j hj) w).1)
            (fun j hj => (hBound j (hsMem j hj) w).2)⟩
      calc
        (∫ w, ∏ j ∈ insert i s, A j w ∂μ) =
            ∫ w, A i w * (∏ j ∈ s, A j w) ∂μ := by simp [Finset.prod_insert, his]
        _ ≤ q * ∫ w, ∏ j ∈ s, A j w ∂μ :=
          integral_mul_le_of_condExp_le (hm i hiMem)
            (integrable_of_measurable_unit_interval (hMeas i hiMem) (hBound i hiMem))
            hprodMeas hprodBound (hCE i hiMem)
        _ ≤ q * q ^ s.card := mul_le_mul_of_nonneg_left htail hq
        _ = q ^ (insert i s).card := by rw [Finset.card_insert_of_notMem his, pow_succ']

lemma integral_prod_le_exp_of_condExp_le {delta : ℝ} (hδ : delta ≤ 1)
    (A : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω) (s : Finset ℕ)
    (hMeas : ∀ i ∈ s, Measurable (A i))
    (hBound : ∀ i ∈ s, ∀ w, 0 ≤ A i w ∧ A i w ≤ 1)
    (hm : ∀ i ∈ s, m i ≤ mΩ)
    (hCE : ∀ i ∈ s, ∀ᵐ w ∂μ, (μ[A i | m i]) w ≤ 1 - delta)
    (hLater : ∀ i ∈ s, ∀ j ∈ s, i < j → Measurable[m i] (A j)) :
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ Real.exp (-delta * (s.card : ℝ)) := by
  calc
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ (1 - delta) ^ s.card :=
      integral_prod_le_of_condExp_le (sub_nonneg.mpr hδ) A m s hMeas hBound hm hCE hLater
    _ ≤ (Real.exp (-delta)) ^ s.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr hδ)
      have h := Real.add_one_le_exp (-delta)
      linarith
    _ = Real.exp (-delta * (s.card : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end Probability

end Problem367

end

end OAI
