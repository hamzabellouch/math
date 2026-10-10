import OAI.Probability.ContinuumTransition.GibbsIntegrability

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem idealFamily_finite (d : ℝ) {D : Set Space} (hD : volume D ≠ ⊤) :
    GrandFinite (idealFamily d) D :=
  GrandFinite.of_bound _ hD (fun _ _ => measurable_const)
    (idealFamily_nonneg d) (fun _ _ _ => le_refl _)

theorem grandIntegral_ideal (d : ℝ) (D : Set Space) :
    grandIntegral (idealFamily d) D = Real.exp (volume.real D*Real.exp d) := by
  have he (n : ℕ) : familyTerm (idealFamily d) D n =
      (volume.real D*Real.exp d)^n/(n.factorial : ℝ) := by
    simp only [familyTerm, familyIntegral, idealFamily, Fintype.card_fin,
      setIntegral_const, smul_eq_mul, Measure.real, volume_generalConfigurations,
      ENNReal.toReal_pow, mul_pow, mul_comm d, Real.exp_nat_mul]
  simp_rw [grandIntegral, he]
  simpa only [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (volume.real D*Real.exp d)).tsum_eq

theorem core_gibbs_finite (t d : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {D : Set Space} (hD : volume D ≠ ⊤) :
    GrandFinite (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) D := by
  apply GrandFinite.of_bound _ hD
    (fun ι _ => measurable_gibbsFamily (V := fun x y : Space => coreProfile t ‖x-y‖) ((measurable_coreProfile t).comp
      ((measurable_fst.sub measurable_snd).norm)) β d ι)
    (gibbsFamily_nonneg _ β d)
  intro ι _ x
  unfold gibbsFamily
  split_ifs
  · apply Real.exp_le_exp.mpr
    have he : 0 ≤ gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x := by
      unfold gibbsEnergy
      apply div_nonneg _ (by norm_num)
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · rfl
      · exact coreProfile_nonneg _ _
    exact sub_le_self _ (mul_nonneg hβ he)
  · exact (Real.exp_pos _).le

theorem core_grand_bad_bound (t d L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    grandIntegral (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube L) ≤
      Real.exp (volume.real (cube L)*Real.exp (d-β*t^2/2))*
        grandIntegral (freeFamily t d) (cube L) := by
  rw [← grandIntegral_ideal]
  exact grandIntegral_label_convolution _ _ _ (idealFamily_relabel _) (freeFamily_relabel t d)
    (measurableSet_cube L) (core_gibbs_finite t d hβ (isCompact_cube L).measure_lt_top.ne)
    (idealFamily_finite _ (isCompact_cube L).measure_lt_top.ne)
    (GrandFinite.of_bound _ (isCompact_cube L).measure_lt_top.ne
      (freeFamily_measurable t d) (freeFamily_nonneg t d) (freeFamily_le_exp t d))
    (fun _ x _ => core_gibbs_bad_endpoints t d hβ x)

lemma truncated_exp_poly_bound {V θ : ℝ} (hV : 0 ≤ V) (hθ : 0 ≤ θ) (M : ℕ) :
    (∑ k ∈ Finset.range (M+1), (V*θ)^k/(k.factorial : ℝ)) ≤
      (M+1)*Real.exp V*(max 1 θ)^M := by
  have hs : HasSum (fun k : ℕ => V^k/(k.factorial : ℝ)) (Real.exp V) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp V
  calc
    _ ≤ ∑ _k ∈ Finset.range (M+1), Real.exp V*(max 1 θ)^M := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ M := by have := Finset.mem_range.mp hk; omega
      have hp : V^k/(k.factorial : ℝ) ≤ Real.exp V :=
        hs.summable.le_tsum k (fun j _ => by positivity) |>.trans_eq hs.tsum_eq
      rw [mul_pow, mul_div_right_comm]
      exact mul_le_mul hp
        ((pow_le_pow_left₀ hθ (le_max_right 1 θ) k).trans
          (pow_le_pow_right₀ (le_max_left 1 θ) hkn))
        (pow_nonneg hθ k) (Real.exp_pos V).le
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

noncomputable def clusterActivity (t d : ℝ) : ℝ :=
  Real.exp d*(max 1 (volume.real (Metric.closedBall (0 : Space)
    ((1+shellDelta)*Real.exp (-t)))*Real.exp d))^3

theorem core_grand_upper {t : ℝ} (ht : 2*(1+shellDelta)*Real.exp (-t) < 1)
    (d L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    grandIntegral (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube L) ≤
      Real.exp (volume.real (cube L)*(1+Real.exp (d-β*t^2/2))+(packingNumber L : ℝ))*
        ((packingNumber L : ℝ)+1)*(max 1 (clusterActivity t d))^(packingNumber L) := by
  have h1 := core_grand_bad_bound t d L hβ
  have h2 := free_grand_upper ht d L
  have h3 := truncated_exp_poly_bound (V := volume.real (cube L)) ENNReal.toReal_nonneg
    (θ := clusterActivity t d) (by unfold clusterActivity; positivity) (packingNumber L)
  have he : volume.real (cube L)*Real.exp d*
      (max 1 (volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t)))*Real.exp d))^3 =
      volume.real (cube L)*clusterActivity t d := by unfold clusterActivity; ring
  rw [he] at h2
  apply h1.trans
  apply (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
    (Real.exp_pos _).le).trans_eq
  rw [show volume.real (cube L)*(1+Real.exp (d-β*t^2/2))+(packingNumber L : ℝ) =
    volume.real (cube L)*Real.exp (d-β*t^2/2)+volume.real (cube L)+(packingNumber L : ℝ) by ring,
    Real.exp_add, Real.exp_add]
  ring

end ContinuumTemperature
end

end OAI
