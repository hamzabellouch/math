import Mathlib

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere.Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integral_mul_le_sqrt (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) *
      Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

lemma memLp_sqrt {f : α → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    MemLp (fun x ↦ Real.sqrt (f x)) 2 μ := by
  refine (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1)).2 ?_
  apply hf.congr
  filter_upwards [hf0] with x hx
  exact (Real.sq_sqrt hx).symm

def affinity (μ : Measure α) (p q : α → ℝ) : ℝ :=
  ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ

lemma affinity_nonneg (p q : α → ℝ) : 0 ≤ affinity μ p q := by
  exact integral_nonneg fun x ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma affinity_integrable {p q : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) :
    Integrable (fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)) μ := by
  exact (memLp_sqrt hp hp0).integrable_mul (memLp_sqrt hq hq0)

lemma sqrt_ratio_product {p q s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hsp : p = 0 → s = 0) (hsq : q = 0 → s = 0) :
    Real.sqrt (s / Real.sqrt p * (s / Real.sqrt q)) *
      Real.sqrt (Real.sqrt p * Real.sqrt q) = s := by
  by_cases hpz : p = 0
  · simp [hpz, hsp hpz]
  by_cases hqz : q = 0
  · simp [hqz, hsq hqz]
  have hp' : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hp (Ne.symm hpz)))
  have hq' : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hqz)))
  have hprod : (s / Real.sqrt p * (s / Real.sqrt q)) *
      (Real.sqrt p * Real.sqrt q) = s ^ 2 := by
    field_simp
  rw [← Real.sqrt_mul (mul_nonneg (div_nonneg hs (Real.sqrt_nonneg p))
    (div_nonneg hs (Real.sqrt_nonneg q))), hprod, Real.sqrt_sq hs]

lemma common_density_bound {p q s : α → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) (hs0 : 0 ≤ᵐ[μ] s)
    (hsp : ∀ᵐ x ∂μ, p x = 0 → s x = 0)
    (hsq : ∀ᵐ x ∂μ, q x = 0 → s x = 0)
    (hP : MemLp (fun x ↦ s x / Real.sqrt (p x)) 2 μ)
    (hQ : MemLp (fun x ↦ s x / Real.sqrt (q x)) 2 μ) :
    (∫ x, s x ∂μ) ^ 2 ≤
      Real.sqrt (∫ x, (s x / Real.sqrt (p x)) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (s x / Real.sqrt (q x)) ^ 2 ∂μ) * affinity μ p q := by
  let a := fun x ↦ s x / Real.sqrt (p x)
  let b := fun x ↦ s x / Real.sqrt (q x)
  let c := fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)
  have ha0 : 0 ≤ᵐ[μ] a := hs0.mono fun x hx ↦ div_nonneg hx (Real.sqrt_nonneg _)
  have hb0 : 0 ≤ᵐ[μ] b := hs0.mono fun x hx ↦ div_nonneg hx (Real.sqrt_nonneg _)
  have hab : Integrable (fun x ↦ a x * b x) μ := hP.integrable_mul hQ
  have hab0 : 0 ≤ᵐ[μ] (fun x ↦ a x * b x) := by
    filter_upwards [ha0, hb0] with x hx hy using mul_nonneg hx hy
  have hc : Integrable c μ := affinity_integrable hp hq hp0 hq0
  have hc0 : 0 ≤ᵐ[μ] c := Eventually.of_forall fun x ↦ by dsimp [c]; positivity
  have hs : (fun x ↦ Real.sqrt (a x * b x) * Real.sqrt (c x)) =ᵐ[μ] s := by
    filter_upwards [hp0, hq0, hs0, hsp, hsq] with x hp' hq' hs' hsp' hsq'
    exact sqrt_ratio_product hp' hq' hs' hsp' hsq'
  have h₁ := integral_mul_le_sqrt (fun x ↦ Real.sqrt (a x * b x))
    (fun x ↦ Real.sqrt (c x)) (memLp_sqrt hab hab0) (memLp_sqrt hc hc0)
    (Eventually.of_forall fun x ↦ Real.sqrt_nonneg _) (Eventually.of_forall fun x ↦ Real.sqrt_nonneg _)
  have habsq : (∫ x, Real.sqrt (a x * b x) ^ 2 ∂μ) = ∫ x, a x * b x ∂μ := by
    apply integral_congr_ae
    exact hab0.mono fun _ h ↦ Real.sq_sqrt h
  have hcsq : (∫ x, Real.sqrt (c x) ^ 2 ∂μ) = affinity μ p q := by
    apply integral_congr_ae
    exact hc0.mono fun _ h ↦ Real.sq_sqrt h
  rw [integral_congr_ae hs, habsq, hcsq] at h₁
  have h₂ : (∫ x, s x ∂μ) ^ 2 ≤ (∫ x, a x * b x ∂μ) * affinity μ p q := by
    have h := (sq_le_sq₀ (integral_nonneg_of_ae hs0) (by positivity)).2 h₁
    simpa only [mul_pow, Real.sq_sqrt (integral_nonneg_of_ae hab0),
      Real.sq_sqrt (affinity_nonneg p q)] using h
  exact h₂.trans (mul_le_mul_of_nonneg_right
    (integral_mul_le_sqrt a b hP hQ ha0 hb0) (affinity_nonneg p q))

lemma ratio_sqrt_sq {s p : ℝ} (hp : 0 ≤ p) :
    (s / Real.sqrt p) ^ 2 = s ^ 2 / p := by
  rw [div_pow, Real.sq_sqrt hp]

lemma memLp_ratio_sqrt {s p : α → ℝ} (hs : AEStronglyMeasurable s μ)
    (hp : AEStronglyMeasurable p μ) (hp0 : 0 ≤ᵐ[μ] p)
    (h : Integrable (fun x ↦ s x ^ 2 / p x) μ) :
    MemLp (fun x ↦ s x / Real.sqrt (p x)) 2 μ := by
  refine (memLp_two_iff_integrable_sq
    ((hs.aemeasurable.div (Real.continuous_sqrt.measurable.comp_aemeasurable hp.aemeasurable)).aestronglyMeasurable)).2 ?_
  apply h.congr
  exact hp0.mono fun x hx ↦ (ratio_sqrt_sq hx).symm

theorem common_density_affinity {p q s : α → ℝ} {C_P C_Q : ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ) (hs : Integrable s μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) (hs0 : 0 ≤ᵐ[μ] s)
    (hsp : ∀ᵐ x ∂μ, p x = 0 → s x = 0)
    (hsq : ∀ᵐ x ∂μ, q x = 0 → s x = 0)
    (hPi : Integrable (fun x ↦ s x ^ 2 / p x) μ)
    (hQi : Integrable (fun x ↦ s x ^ 2 / q x) μ)
    (hP : (∫ x, s x ^ 2 / p x ∂μ) ≤ C_P)
    (hQ : (∫ x, s x ^ 2 / q x ∂μ) ≤ C_Q)
    (hm : 0 < ∫ x, s x ∂μ) :
    (∫ x, s x ∂μ) ^ 2 / Real.sqrt (C_P * C_Q) ≤ affinity μ p q := by
  have hP' := memLp_ratio_sqrt hs.1 hp.1 hp0 hPi
  have hQ' := memLp_ratio_sqrt hs.1 hq.1 hq0 hQi
  have hPeq : (∫ x, (s x / Real.sqrt (p x)) ^ 2 ∂μ) =
      ∫ x, s x ^ 2 / p x ∂μ :=
    integral_congr_ae (hp0.mono fun x hx ↦ ratio_sqrt_sq hx)
  have hQeq : (∫ x, (s x / Real.sqrt (q x)) ^ 2 ∂μ) =
      ∫ x, s x ^ 2 / q x ∂μ :=
    integral_congr_ae (hq0.mono fun x hx ↦ ratio_sqrt_sq hx)
  have hP0 : 0 ≤ ∫ x, s x ^ 2 / p x ∂μ := by
    rw [← hPeq]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hQ0 : 0 ≤ ∫ x, s x ^ 2 / q x ∂μ := by
    rw [← hQeq]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hCP0 := hP0.trans hP
  have hCQ0 := hQ0.trans hQ
  have h := common_density_bound hp hq hp0 hq0 hs0 hsp hsq hP' hQ'
  rw [hPeq, hQeq] at h
  have h' : (∫ x, s x ∂μ) ^ 2 ≤ Real.sqrt (C_P * C_Q) * affinity μ p q := by
    rw [Real.sqrt_mul hCP0]
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (Real.sqrt_le_sqrt hP) (Real.sqrt_le_sqrt hQ)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (affinity_nonneg p q))
  have hden : 0 < Real.sqrt (C_P * C_Q) := by
    by_contra hn
    have hz : Real.sqrt (C_P * C_Q) = 0 :=
      le_antisymm (le_of_not_gt hn) (Real.sqrt_nonneg _)
    rw [hz, zero_mul] at h'
    nlinarith
  exact (div_le_iff₀ hden).2 (by simpa only [mul_comm] using h')

def measureAffinity (P Q : Measure α) : ℝ :=
  affinity (P + Q) (fun x ↦ (P.rnDeriv (P + Q) x).toReal)
    (fun x ↦ (Q.rnDeriv (P + Q) x).toReal)

lemma real_rnDeriv_chain {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ] (hνP : ν ≪ P) :
    (fun x ↦ (ν.rnDeriv P x).toReal * (P.rnDeriv ξ x).toReal) =ᵐ[ξ]
      (fun x ↦ (ν.rnDeriv ξ x).toReal) := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := ξ) hνP] with x hx
  exact ENNReal.toReal_mul.symm.trans (congrArg ENNReal.toReal hx)

lemma sq_mul_div (a b : ℝ) : (a * b) ^ 2 / b = b * a ^ 2 := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp

lemma rnDeriv_density_moment {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ]
    (hνP : ν ≪ P) (hPξ : P ≪ ξ) :
    (∫ x, (ν.rnDeriv ξ x).toReal ^ 2 / (P.rnDeriv ξ x).toReal ∂ξ) =
      ∫ x, (ν.rnDeriv P x).toReal ^ 2 ∂P := by
  calc
    (∫ x, (ν.rnDeriv ξ x).toReal ^ 2 / (P.rnDeriv ξ x).toReal ∂ξ) =
        ∫ x, (P.rnDeriv ξ x).toReal * (ν.rnDeriv P x).toReal ^ 2 ∂ξ := by
      apply integral_congr_ae
      filter_upwards [real_rnDeriv_chain (ξ := ξ) hνP] with x hx
      rw [← hx, sq_mul_div]
    _ = _ := integral_toReal_rnDeriv_mul hPξ

lemma integrable_rnDeriv_density_moment {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ]
    (hνP : ν ≪ P) (hPξ : P ≪ ξ)
    (h : Integrable (fun x ↦ (ν.rnDeriv P x).toReal ^ 2) P) :
    Integrable (fun x ↦ (ν.rnDeriv ξ x).toReal ^ 2 / (P.rnDeriv ξ x).toReal) ξ := by
  apply ((integrable_toReal_rnDeriv_mul_iff hPξ).2 h).congr
  filter_upwards [real_rnDeriv_chain (ξ := ξ) hνP] with x hx
  rw [← hx, sq_mul_div]

theorem common_measure_affinity {ν P Q : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {C_P C_Q : ℝ} (hνP : ν ≪ P) (hνQ : ν ≪ Q)
    (hm : 0 < ν.real univ)
    (hPi : Integrable (fun x ↦ (ν.rnDeriv P x).toReal ^ 2) P)
    (hQi : Integrable (fun x ↦ (ν.rnDeriv Q x).toReal ^ 2) Q)
    (hP : (∫ x, (ν.rnDeriv P x).toReal ^ 2 ∂P) ≤ C_P)
    (hQ : (∫ x, (ν.rnDeriv Q x).toReal ^ 2 ∂Q) ≤ C_Q) :
    (ν.real univ) ^ 2 / Real.sqrt (C_P * C_Q) ≤ measureAffinity P Q := by
  have hPξ : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQξ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hνξ := hνP.trans hPξ
  have chainP := real_rnDeriv_chain (ξ := P + Q) hνP
  have chainQ := real_rnDeriv_chain (ξ := P + Q) hνQ
  have hsp : ∀ᵐ x ∂(P + Q), (P.rnDeriv (P + Q) x).toReal = 0 →
      (ν.rnDeriv (P + Q) x).toReal = 0 := by
    filter_upwards [chainP] with x hx hz
    rw [← hx, hz, mul_zero]
  have hsq : ∀ᵐ x ∂(P + Q), (Q.rnDeriv (P + Q) x).toReal = 0 →
      (ν.rnDeriv (P + Q) x).toReal = 0 := by
    filter_upwards [chainQ] with x hx hz
    rw [← hx, hz, mul_zero]
  have h := common_density_affinity (C_P := C_P) (C_Q := C_Q)
    (μ := P + Q) (p := fun x ↦ (P.rnDeriv (P + Q) x).toReal)
    (q := fun x ↦ (Q.rnDeriv (P + Q) x).toReal)
    (s := fun x ↦ (ν.rnDeriv (P + Q) x).toReal)
    Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
    Measure.integrable_toReal_rnDeriv
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    hsp hsq
    (integrable_rnDeriv_density_moment hνP hPξ hPi)
    (integrable_rnDeriv_density_moment hνQ hQξ hQi)
    (by rwa [rnDeriv_density_moment hνP hPξ])
    (by rwa [rnDeriv_density_moment hνQ hQξ])
    (by rwa [Measure.integral_toReal_rnDeriv hνξ])
  simpa only [Measure.integral_toReal_rnDeriv hνξ, measureAffinity] using h

end HardSphere.Comparison

end
end

end

end OAI
