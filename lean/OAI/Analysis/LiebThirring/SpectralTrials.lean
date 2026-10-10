import OAI.Analysis.LiebThirring.FlagApproximation

namespace OAI

universe u179


noncomputable section
namespace SharpLiebThirring.SpectralProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set ContinuationGap ActionProof
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma triangular_action_upper {σ l r : ℝ} (hσ : 0 < σ) (hlr : l ≤ r)
    (k : Fin N → ℝ) (a v : ℝ → Fin N → ℝ)
    (ha : ContinuousOn a (Icc l r)) (hv : ContinuousOn v (Icc l r))
    {W : ℝ → ℝ} (hW : IntervalIntegrable W volume l r)
    (hWn : ∀ᵐ x ∂volume, 0 ≤ W x)
    (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (he : (∫ t in l..r, (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) ≤
      ∫ t in l..r, W t*(∑ i, a t i^2)) :
    (∫ t in l..r, actionDensity σ k (a t) (v t)) ≤
      actionYoungConstant σ * ∫ t, W t^(1+σ) := by
  let m := fun t ↦ ∑ i, a t i^2
  have hm : ContinuousOn m (Icc l r) := continuousOn_finsetSum Finset.univ (fun i _ ↦ (continuousOn_pi.mp ha i).pow 2)
  have hm0 (t : ℝ) : 0 ≤ m t := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmr : ContinuousOn (fun t ↦ m t^(1+1/σ)) (Icc l r) :=
    hm.rpow_const (fun _ _ ↦ Or.inr (by positivity))
  have hE : ContinuousOn (fun t ↦ (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) (Icc l r) :=
    (continuousOn_finsetSum Finset.univ (fun i _ ↦ (continuousOn_pi.mp hv i).pow 2)).add
      (continuousOn_finsetSum Finset.univ (fun i _ ↦ ((continuousOn_pi.mp ha i).pow 2).const_mul _))
  have hEi : IntervalIntegrable (fun t ↦ (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) volume l r := hE.intervalIntegrable_of_Icc hlr
  have hmri : IntervalIntegrable (fun t ↦ m t^(1+1/σ)) volume l r := hmr.intervalIntegrable_of_Icc hlr
  have hWmi : IntervalIntegrable (fun t ↦ W t*m t) volume l r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlr] at hW ⊢
    exact hW.mul_continuousOn hm isCompact_Icc
  have hAi : IntervalIntegrable (fun t ↦ actionYoungConstant σ * W t^(1+σ)) volume l r := hWp.intervalIntegrable.const_mul (actionYoungConstant σ)
  calc
    (∫ t in l..r, actionDensity σ k (a t) (v t)) =
        (∫ t in l..r, (∑ i, v t i^2)+(∑ i, k i^2*a t i^2)) -
          ∫ t in l..r, m t^(1+1/σ) := intervalIntegral.integral_sub hEi hmri
    _ ≤ (∫ t in l..r, W t*m t) - ∫ t in l..r, m t^(1+1/σ) := sub_le_sub_right he _
    _ = ∫ t in l..r, W t*m t-m t^(1+1/σ) :=
      (intervalIntegral.integral_sub hWmi hmri).symm
    _ ≤ ∫ t in l..r, actionYoungConstant σ * W t^(1+σ) := by
      apply intervalIntegral.integral_mono_ae_restrict hlr (hWmi.sub hmri) hAi
      filter_upwards [ae_restrict_of_ae hWn] with t ht
      exact young_action_bound hσ ht (hm0 t)
    _ = actionYoungConstant σ * ∫ t in l..r, W t^(1+σ) := intervalIntegral.integral_const_mul _ _
    _ ≤ actionYoungConstant σ * ∫ t, W t^(1+σ) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold actionYoungConstant; positivity)
      rw [intervalIntegral.integral_of_le hlr]
      exact integral_mono_measure Measure.restrict_le_self
        (hWn.mono fun x hx ↦ Real.rpow_nonneg hx _) hWp

lemma finite_spectral_trial {σ l r : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    {W : ℝ → ℝ} (hW : IntervalIntegrable W volume l r)
    (hWn : ∀ᵐ x ∂volume, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (he : ∀ C : LowerSpace N,
      (∫ t in l..r, (∑ i, (C.val *ᵥ v t) i^2)+(∑ i, k i^2*(C.val *ᵥ u t) i^2)) ≤
        ∫ t in l..r, W t*(∑ i, (C.val *ᵥ u t) i^2)) :
    (∑ i, ∫ s in -(k i)..k i, (k i^2-s^2)^σ) ≤
      actionYoungConstant σ * ∫ t, W t^(1+σ) := by
  apply finite_action_upper_test hσ₀ hσ₁ hlr k hk u v hu hv hud hul hur ho
  intro C
  exact triangular_action_upper hσ₀ hlr k _ _
    ((show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hu)
    ((show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hv)
    hW hWn hWp (he C)

end SharpLiebThirring.SpectralProof

end


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Filter Matrix MatrixProof ContinuationGap
open scoped Topology Matrix.Norms.L2Operator

lemma compact_family_radius {ι : Type u179} [Fintype ι] (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) :
    ∃ R : ℝ, 0 < R ∧ ∀ i x, R ≤ |x| → (u i).val x = 0 ∧ (u i).grad x = 0 := by
  have hc : IsCompact (⋃ i, tsupport (u i).val) := isCompact_iUnion hu
  obtain ⟨R,hR,hs⟩ := hc.isBounded.subset_ball_lt 0 0
  refine ⟨R,hR,fun i x hx ↦ ?_⟩
  have hn : x ∉ tsupport (u i).val := by
    intro hm
    have hxb := hs (mem_iUnion.2 ⟨i,hm⟩)
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] at hxb
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hn,?_⟩
  rw [← deriv_val]
  apply Function.notMem_support.mp
  exact fun hd ↦ hn (support_deriv_subset hd)

lemma integral_eq_interval_of_vanish {R : ℝ} (_hR : 0 ≤ R) {f : ℝ → ℝ}
    (hf : ∀ x, R ≤ |x| → f x = 0) : (∫ x, f x) = ∫ x in -R..R, f x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hn : |x| < R := lt_of_not_ge (fun h ↦ hx (hf x h))
  exact ⟨by rw [abs_lt] at hn; linarith [hn.1],by rw [abs_lt] at hn; linarith [hn.2]⟩

lemma row_mem_prefix {N : ℕ} (q : Fin N → C1L2) (C : LowerSpace N) (i : Fin N) :
    (∑ j, C.val i j • q j) ∈ Submodule.span ℝ (q '' Iic i) := by
  classical
  apply Submodule.sum_mem
  intro j _
  by_cases hj : j ≤ i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_image_of_mem q (mem_Iic.mpr hj)))
  · rw [C.property i j (lt_of_not_ge hj),zero_smul]
    exact Submodule.zero_mem _

lemma compact_trial_energy {N : ℕ} {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (κ : Fin N → ℝ) (p : Fin N → C1L2) (hp : ∀ i, HasCompactSupport (p i).val)
    (he : ∀ i, energy W (p i) (p i)+κ i^2*inner ℝ (p i) (p i) ≤ 0) :
    (∫ x, (∑ i, (p i).grad x^2)+(∑ i, κ i^2*(p i).val x^2)) ≤
      ∫ x, W x*(∑ i, (p i).val x^2) := by
  have hgi (i : Fin N) : Integrable (fun x ↦ (p i).grad x^2) := by
    simpa only [pow_two] using (p i).integrable_grad_mul (p i)
  have hvi (i : Fin N) : Integrable (fun x ↦ κ i^2*(p i).val x^2) := by
    simpa only [pow_two] using ((p i).integrable_val_mul (p i)).const_mul (κ i*κ i)
  have hwi (i : Fin N) : Integrable (fun x ↦ W x*(p i).val x^2) := by
    simpa only [pow_two,mul_assoc] using integrable_potential hW (p i) (p i) (hp i)
  rw [integral_add (integrable_finsetSum _ (fun i _ ↦ hgi i))
    (integrable_finsetSum _ (fun i _ ↦ hvi i)),integral_finsetSum _ (fun i _ ↦ hgi i),
    integral_finsetSum _ (fun i _ ↦ hvi i)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hwi i),← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hh := he i
  simp only [energy,inner_eq_integral,mul_assoc,← pow_two] at hh
  rw [integral_const_mul]
  linarith

lemma compact_trial_bound {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (hWn : ∀ᵐ x, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (κ : Fin N → ℝ) (hκ : ∀ i, 0 < κ i)
    (q : Fin N → C1L2) (ho : Orthonormal ℝ q)
    (hc : ∀ i, HasCompactSupport (q i).val)
    (he : ∀ i (v : C1L2), v ∈ Submodule.span ℝ (q '' Iic i) →
      energy W v v+κ i^2*inner ℝ v v ≤ 0) :
    (∑ i, ∫ s in -(κ i)..κ i, (κ i^2-s^2)^σ) ≤
      actionYoungConstant σ * ∫ x, W x^(1+σ) := by
  classical
  obtain ⟨R,hR,hvan⟩ := compact_family_radius q hc
  apply finite_spectral_trial hσ₀ hσ₁ (l := -R) (r := R) (by linarith) κ hκ
    (fun x i ↦ (q i).val x) (fun x i ↦ (q i).grad x)
    ((continuous_pi (fun i ↦ (q i).continuous)).continuousOn)
    ((continuous_pi (fun i ↦ (q i).grad_continuous)).continuousOn)
    (fun x _ i ↦ (q i).hasDerivAt x)
  · ext i; exact (hvan i (-R) (by simp [abs_of_pos hR])).1
  · ext i; exact (hvan i R (by simp [abs_of_pos hR])).1
  · intro i j
    rw [← integral_eq_interval_of_vanish hR.le (fun x hx ↦ by rw [(hvan i x hx).1,zero_mul]),
      ← inner_eq_integral]
    exact orthonormal_iff_ite.mp ho i j
  · exact locallyIntegrable_intervalIntegrable hW _ _
  · exact hWn
  · exact hWp
  · intro C
    let p := fun i ↦ ∑ j, C.val i j • q j
    have hp (i : Fin N) : HasCompactSupport (p i).val :=
      compact_sum _ _ (fun j _ ↦ compact_smul _ (hc j))
    have hpv (i : Fin N) (x : ℝ) : (p i).val x = (C.val *ᵥ (fun j ↦ (q j).val x)) i := by
      simp only [p,val_sum,val_smul,mulVec,dotProduct]
    have hpg (i : Fin N) (x : ℝ) : (p i).grad x = (C.val *ᵥ (fun j ↦ (q j).grad x)) i := by
      simp only [p,grad_sum,grad_smul,mulVec,dotProduct]
    have he' := compact_trial_energy hW κ p hp (fun i ↦ he i (p i) (row_mem_prefix q C i))
    have hz (i : Fin N) (x : ℝ) (hx : R ≤ |x|) : (p i).val x = 0 ∧ (p i).grad x = 0 := by
      constructor <;> simp only [p,val_sum,grad_sum,val_smul,grad_smul] <;>
        apply Finset.sum_eq_zero <;> intro j _ <;> simp [(hvan j x hx).1,(hvan j x hx).2]
    rw [integral_eq_interval_of_vanish hR.le (fun x hx ↦ by simp [(fun i ↦ (hz i x hx).1),(fun i ↦ (hz i x hx).2)]),
      integral_eq_interval_of_vanish hR.le (fun x hx ↦ by simp [(fun i ↦ (hz i x hx).1)])] at he'
    simpa only [hpv,hpg] using he'

end SharpLiebThirring.SpectralProof

end

end OAI
