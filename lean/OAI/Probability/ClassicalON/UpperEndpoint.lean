import OAI.Probability.ClassicalON.CylindricalConfiguration

namespace OAI

universe uI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

instance sphereProbability_isOpenPos (n : ℕ) [NeZero n] :
    (sphereProbability n).IsOpenPosMeasure := by
  unfold sphereProbability
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

instance sphericalAmplitudeLaw_isOpenPos : sphericalAmplitudeLaw.IsOpenPosMeasure :=
  continuous_firstAmplitude.isOpenPosMeasure_map (fun r =>
    ⟨cylindricalSpin r true 0,firstAmplitude_cylindricalSpin r true 0⟩)

variable {I : Type uI} [Fintype I]

def upperTent (δ : ℝ) (r : I → Amplitude) : ℝ := ∏ i,max 0 ((r i:ℝ)-(1-δ))

theorem continuous_upperTent (δ : ℝ) : Continuous (upperTent (I := I) δ) := by
  unfold upperTent
  fun_prop

theorem upperTent_nonneg (δ : ℝ) (r : I → Amplitude) : 0≤upperTent δ r :=
  Finset.prod_nonneg (fun _ _ => le_max_left _ _)

theorem upperTent_monotone (δ : ℝ) : Monotone (upperTent (I := I) δ) := by
  intro r s hrs
  apply Finset.prod_le_prod₀ (fun _ _ => le_max_left _ _)
  intro i _
  exact max_le_max le_rfl (sub_le_sub_right (show (r i:ℝ)≤(s i:ℝ) from hrs i) _)

theorem upperTent_top_pos {δ : ℝ} (hδ : 0<δ) : 0<upperTent (I := I) δ ⊤ := by
  apply Finset.prod_pos
  intro i _
  simpa using (lt_max_of_lt_right hδ : (0:ℝ) < max 0 δ)

theorem upperTent_support_ball {δ : ℝ} (hδ : 0<δ) {r : I → Amplitude}
    (hr : upperTent δ r≠0) : dist r ⊤<δ := by
  apply (dist_pi_lt_iff hδ).2
  intro i
  have hi : max 0 ((r i:ℝ)-(1-δ))≠0 := by
    intro he
    exact hr (Finset.prod_eq_zero (Finset.mem_univ i) he)
  have hip : 0<(r i:ℝ)-(1-δ) := by
    by_contra! hn
    exact hi (max_eq_left hn)
  change dist (r i:ℝ) 1<δ
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (r i).property.2)]
  linarith

theorem upperEndpoint_nonneg (μ : Measure (I → Amplitude)) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {F : (I → Amplitude) → ℝ} (hF : Continuous F)
    (ht : ∀ h : (I → Amplitude) → ℝ,Continuous h → (∀ r,0≤h r) → Monotone h →
      0≤∫ r,h r*F r ∂μ) : 0≤F ⊤ := by
  by_contra! hneg
  obtain ⟨δ,hδ,hd⟩ := (Metric.continuousAt_iff.mp hF.continuousAt) (-F ⊤/2) (by linarith)
  let h := upperTent (I := I) δ
  have hc : Continuous (fun r => -(h r*F r)) := ((continuous_upperTent δ).mul hF).neg
  have hp : ∀ r,0≤ -(h r*F r) := by
    intro r
    by_cases hr : h r=0
    · simp [hr]
    · have hx := hd (upperTent_support_ball hδ hr)
      rw [Real.dist_eq,abs_lt] at hx
      have hfn : F r<0 := by linarith
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (upperTent_nonneg δ r) hfn.le)
  have hs : (Function.support (fun r => -(h r*F r))).Nonempty := by
    refine ⟨⊤,?_⟩
    exact neg_ne_zero.mpr (mul_ne_zero (upperTent_top_pos hδ).ne' hneg.ne)
  have hi : 0<∫ r,-(h r*F r) ∂μ :=
    (integral_pos_iff_support_of_nonneg hp (compact_integrable hc)).2
      (hc.isOpen_support.measure_pos μ hs)
  rw [integral_neg] at hi
  have hn := ht h (continuous_upperTent δ) (upperTent_nonneg δ) (upperTent_monotone δ)
  linarith

end ClassicalON

end

end OAI
