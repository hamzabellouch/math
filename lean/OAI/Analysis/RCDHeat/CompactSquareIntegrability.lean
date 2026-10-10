import Mathlib
import OAI.Analysis.RCDHeat.GeodesicCauchy
import OAI.Analysis.RCDHeat.SqrtPairSlope

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CompactSquareIntegrability, CompactDensityDescent, CompactRecovery, CompactConvergence, ProbabilityRecovery. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
 theorem compactSquare_integrable {f : X → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun x => f x^2) μ := by
  simpa only [pow_two,Pi.mul_def] using (hf.mul hf).integrable_of_hasCompactSupport hs.mul_right
 theorem compactSquare_entropy_integrable {f : X → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun x => f x^2*Real.log (f x^2)) μ := by
  have h0 : (fun a : ℝ => a*Real.log a) 0 = 0 := by simp
  have hsq : HasCompactSupport (fun x => f x^2) := by simpa only [pow_two,Pi.mul_def] using hs.mul_right (f' := f)
  exact (Real.continuous_mul_log.comp (hf.pow 2)).integrable_of_hasCompactSupport (hsq.comp_left h0)
 theorem compactSquare_weight_integrable {f v : X → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hv : Continuous v) : Integrable v (μ.withDensity (fun x => ENNReal.ofReal (f x^2))) := by
  apply (squareDensity_integrable_iff μ hf.measurable).mpr
  have hsq : HasCompactSupport (fun x => f x^2) := by simpa only [pow_two,Pi.mul_def] using hs.mul_right (f' := f)
  exact ((hf.pow 2).mul hv).integrable_of_hasCompactSupport hsq.mul_right
variable [ProperSpace X]
omit [MeasurableSpace X] [BorelSpace X] in
 theorem compactSupport_of_dist_bound (p : X) {R : ℝ} {f : X → ℝ}
    (hf : ∀ x, f x ≠ 0 → dist p x ≤ R) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall p R)
  intro x hx
  exact Metric.mem_closedBall.mpr (by rw [dist_comm]; exact hf x hx)
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
 

 theorem FullCD.compact_sqrt_density_descent (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [NeZero μ] [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : X → ℝ) {C M : ℝ≥0} {R : ℝ}
    (hf : LipschitzWith C f) (hfB : ∀ x, |f x| ≤ M)
    (hfS : ∀ x, f x ≠ 0 → dist p x ≤ R)
    (hfI : Integrable (fun x => f x^2) μ) (hfM : ∫x, f x^2 ∂μ = 1)
    (hfE : Integrable (fun x => f x^2*Real.log (f x^2)) μ)
    (hfExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x))
      (μ.withDensity (fun x => ENNReal.ofReal (f x^2))))
    (hfDist : Integrable (fun x => dist p x^2) (μ.withDensity (fun x => ENNReal.ofReal (f x^2))))
    (G : Lp ℝ 2 μ) (hG : IsSlopeMajorant μ f G)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x)) ν)
    (hνDist : Integrable (fun x => dist p x^2) ν)
    (π : Measure (X×X))
    (hπ₀ : π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (f x^2)))
    (hπ₁ : π.map Prod.snd = ν) :
    ENNReal.ofReal ((∫x, f x^2*Real.log (f x^2) ∂μ)-boltzmannEntropy μ ν) ≤
      ENNReal.ofReal (2*‖G‖)*(transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  obtain ⟨c,H,hc,hH,hgI,hgM,hgE,hgExp,hgDist⟩ :=
    exists_normalized_exponential_sqrt μ p hA hB hvol
  let g := fun x => c*Real.exp (-(2*(B+1))*dist p x)
  let σ := μ.withDensity (fun x => ENNReal.ofReal (g x^2))
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (f x^2))
  let : IsProbabilityMeasure σ := squareDensity_probability μ hgI hgM
  let : IsProbabilityMeasure ρ := squareDensity_probability μ hfI hfM
  have hgL := lipschitzWith_const_mul_real (exp_neg_dist_lipschitz p (by positivity : 0 ≤ 2*(B+1))) c
  have hgpos (x : X) : 0 < g x := mul_pos hc (Real.exp_pos _)
  have hprod := product_coupling σ ν
  have hπfin := coupling_transportCost_ne_top hπ₀ hπ₁ p hfDist hνDist
  have hκfin := coupling_transportCost_ne_top hprod.1 hprod.2 p hgDist hνDist
  let t : ℕ → ℝ := fun i => (1/2:ℝ)^(i+1)
  have ht (i : ℕ) : 0 < t i := pow_pos (by norm_num) _
  have ht1 (i : ℕ) : t i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htlim : Tendsto t atTop (𝓝 0) := by
    simpa [t,pow_succ] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const (1/2:ℝ)
  have hden (i : ℕ) : μ.withDensity (fun x => ENNReal.ofReal (sqrtMixture (t i) f g x^2)) =
      measureMixture (t i) ρ σ := by
    simp_rw [sqrtMixture_sq (ht i).le (ht1 i)]
    exact withDensity_mixture μ (hf.continuous.measurable.pow_const 2)
      (hgL.continuous.measurable.pow_const 2) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) (ht i).le (ht1 i)
  have hineq (i : ℕ) :
      ENNReal.ofReal ((∫x, sqrtMixture (t i) f g x^2*Real.log (sqrtMixture (t i) f g x^2) ∂μ)-
        boltzmannEntropy μ ν) ≤
        ENNReal.ofReal (2*‖Real.sqrt (1-t i) • G+Real.sqrt (t i) • H‖)*
          (transportCost (measureMixture (t i) π (σ.prod ν)))^(1/(2:ℝ))+
        ENNReal.ofReal (|K|/2)*transportCost (measureMixture (t i) π (σ.prod ν)) := by
    have hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (sqrtMixture (t i) f g x^2))) := by
      rw [hden i]
      exact measureMixture_probability (ht i).le (ht1 i)
    have hdist : Integrable (fun x => dist p x^2)
        (μ.withDensity (fun x => ENNReal.ofReal (sqrtMixture (t i) f g x^2))) := by
      rw [hden i]
      exact measureMixture_integrable hfDist hgDist _
    have hexp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x))
        (μ.withDensity (fun x => ENNReal.ofReal (sqrtMixture (t i) f g x^2))) := by
      rw [hden i]
      exact measureMixture_integrable hfExp hgExp _
    have he : Integrable (fun x => sqrtMixture (t i) f g x^2*Real.log (sqrtMixture (t i) f g x^2)) μ := by
      simp_rw [sqrtMixture_sq (ht i).le (ht1 i)]
      exact entropy_mixture_integrable μ hfI hgI (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun _ => sq_nonneg _) hfE hgE (ht i).le (ht1 i)
    have hcouple := mixture_coupling hπ₀ hπ₁ hprod.1 hprod.2 (ht i).le (ht1 i)
    rw [← hden i] at hcouple
    exact FullCD.sqrt_density_descent μ K n hcd _
      (sqrtMixture_lipschitz (ht i).le (ht1 i) hf hgL) (sqrtMixture_pos (ht i) (ht1 i) f g hgpos)
      (sqrtMixture_exp_log_lipschitz p (by positivity) hc (ht i) (ht1 i) hf hfB hfS) _
      (hG.sqrtMixture μ hH (ht i).le (ht1 i)) ν hν hprob
      (finiteSecondMoment_of_integrable_dist _ p hdist) (finiteSecondMoment_of_integrable_dist _ p hνDist)
      he hνE p (by positivity)
      (integrable_exp_neg_dist_of_volume μ p hA hB (by linarith : B < B+1) hvol)
      hexp hνExp hdist hνDist _ hcouple.1 hcouple.2
  have hEnt : Tendsto
      (fun i => ∫x, sqrtMixture (t i) f g x^2*Real.log (sqrtMixture (t i) f g x^2) ∂μ)
      atTop (𝓝 (∫x, f x^2*Real.log (f x^2) ∂μ)) := by
    simp_rw [sqrtMixture_sq (ht _).le (ht1 _)]
    exact entropy_mixture_tendsto μ hfI hgI (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ => sq_nonneg _) hfE hgE (fun i => (ht i).le) ht1 htlim
  have hLeft := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hEnt.sub_const (boltzmannEntropy μ ν))
  have hMaj := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((sqrtMixture_majorant_tendsto μ G H htlim).norm.const_mul 2)
  have hCost := transportCost_mixture_tendsto π (σ.prod ν) hπfin hκfin htlim
  have hSqrt := (ENNReal.continuous_rpow_const (y := (1/(2:ℝ)))).continuousAt.tendsto.comp hCost
  have hRight := (ENNReal.Tendsto.mul hMaj
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ 1/(2:ℝ)) hπfin)) hSqrt (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (|K|/2)) hCost (Or.inr ENNReal.ofReal_ne_top))
  exact le_of_tendsto_of_tendsto hLeft hRight (Eventually.of_forall hineq)
 

 theorem FullCD.compact_density_HWI (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [NeZero μ] [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : X → ℝ) {C M : ℝ≥0} {R : ℝ}
    (hf : LipschitzWith C f) (hfB : ∀ x, |f x| ≤ M)
    (hfS : ∀ x, f x ≠ 0 → dist p x ≤ R) (hfM : ∫x, f x^2 ∂μ = 1)
    (G : Lp ℝ 2 μ) (hG : IsSlopeMajorant μ f G)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x)) ν)
    (hνDist : Integrable (fun x => dist p x^2) ν)
    (π : Measure (X×X))
    (hπ₀ : π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (f x^2)))
    (hπ₁ : π.map Prod.snd = ν) :
    ENNReal.ofReal ((∫x, f x^2*Real.log (f x^2) ∂μ)-boltzmannEntropy μ ν) ≤
      ENNReal.ofReal (2*‖G‖)*(transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  have hs := compactSupport_of_dist_bound p hfS
  exact hcd.compact_sqrt_density_descent μ K n p hA hB hvol f hf hfB hfS
    (compactSquare_integrable μ hf.continuous hs) hfM
    (compactSquare_entropy_integrable μ hf.continuous hs)
    (compactSquare_weight_integrable μ hf.continuous hs (by fun_prop))
    (compactSquare_weight_integrable μ hf.continuous hs (by fun_prop))
    G hG ν hν hνE hνExp hνDist π hπ₀ hπ₁
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable def clipPositive (M : ℝ≥0) (a : ℝ) : ℝ := min (max a 0) M
 theorem clipPositive_lipschitz (M : ℝ≥0) : LipschitzWith 1 (clipPositive M) :=
  (LipschitzWith.id.max_const 0).min_const M
 theorem clipPositive_zero (M : ℝ≥0) : clipPositive M 0 = 0 := by simp [clipPositive]
 theorem clipPositive_bounds (M : ℝ≥0) (a : ℝ) : 0 ≤ clipPositive M a ∧ clipPositive M a ≤ M :=
  ⟨le_min (le_max_right _ _) M.coe_nonneg,min_le_right _ _⟩
 theorem clipPositive_eq_self (M : ℝ≥0) {a : ℝ} (ha : 0 ≤ a ∧ a ≤ M) : clipPositive M a = a := by
  rw [clipPositive,max_eq_left ha.1,min_eq_left ha.2]
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)
 theorem IsSlopeMajorant.comp_contraction {g : X → ℝ} {G : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ g G) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) :
    IsSlopeMajorant μ (φ ∘ g) G := by
  filter_upwards [hG] with x hx
  exact ⟨hx.1,(localSlope_comp_le hφ g x).trans hx.2⟩
 theorem IsRelaxedSlope.bounded_recovery {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ M) :
    ∃ (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ),
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
      (∀ i, ⇑(us i) =ᵐ[μ] gs i) ∧ (∀ i, IsSlopeMajorant μ (gs i) (Gs i)) ∧
      Tendsto us atTop (𝓝 f) ∧ Tendsto Gs atTop (𝓝 G) ∧
      (∀ i x, 0 ≤ gs i x ∧ gs i x ≤ M) := by
  obtain ⟨us,gs,Gs,hl,ha,hm,hu,hlim⟩ := hG
  have hcf : (clipPositive_lipschitz M).compLp (clipPositive_zero M) f = f := by
    apply Lp.ext
    filter_upwards [(clipPositive_lipschitz M).coeFn_compLp (clipPositive_zero M) f,hf] with x hx hf
    exact hx.trans (clipPositive_eq_self M hf)
  refine ⟨fun i => (clipPositive_lipschitz M).compLp (clipPositive_zero M) (us i),
    fun i => clipPositive M ∘ gs i,Gs,?_,?_,?_,?_,hlim,fun i x => clipPositive_bounds M _⟩
  · intro i
    obtain ⟨C,hC⟩ := hl i
    exact ⟨1*C,(clipPositive_lipschitz M).comp hC⟩
  · intro i
    exact ((clipPositive_lipschitz M).coeFn_compLp (clipPositive_zero M) _).trans
      ((ha i).mono fun x hx => congrArg (clipPositive M) hx)
  · intro i
    exact (hm i).comp_contraction μ (clipPositive_lipschitz M)
  · rw [← hcf]
    exact (clipPositive_lipschitz M).continuous_compLp (clipPositive_zero M) |>.continuousAt.tendsto.comp hu

omit [MeasurableSpace X] μ in
 theorem radialCutoff_slope_zero (p : X) {R : ℝ} (hR : 0 < R) {x : X} (hx : dist p x < R) :
    localSlope (radialCutoff p R) x = 0 := by
  have he : radialCutoff p R =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [(continuous_const.dist continuous_id).continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact radialCutoff_eq_one p hR hy.le
  rw [localSlope_congr_nhds he,localSlope_const]

variable [BorelSpace X] [ProperSpace X]
 

 theorem IsRelaxedSlope.compact_bounded_recovery {f G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ f G)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ M)
    (p : X) {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) :
    ∃ (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ) (H : Lp ℝ 2 μ) (R : ℝ),
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
      (∀ i, ⇑(us i) =ᵐ[μ] gs i) ∧ (∀ i, IsSlopeMajorant μ (gs i) (Gs i)) ∧
      Tendsto us atTop (𝓝 f) ∧ Tendsto Gs atTop (𝓝 H) ∧ ‖H‖ ≤ ‖G‖ ∧
      (∀ i x, 0 ≤ gs i x ∧ gs i x ≤ M) ∧ (∀ i x, gs i x ≠ 0 → dist p x ≤ R) := by
  obtain ⟨us,gs,Gs,hl,ha,hm,hu,hlim,hb⟩ := hG.bounded_recovery μ M hf
  let R := max r 0+1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right r 0]
  have hrR : r < R := by dsimp [R]; linarith [le_max_left r 0]
  let θ := radialCutoff p R
  let C : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
  have hθ : LipschitzWith C θ := radialCutoff_lipschitz p hR
  have hθb (x : X) : 0 ≤ θ x ∧ θ x ≤ 1 := radialCutoff_bounds p R x
  let Θ := boundedMultiplier μ θ hθ.continuous.measurable 1 (fun x => by rw [abs_of_nonneg (hθb x).1]; exact (hθb x).2)
  have hΘ : ⇑Θ =ᵐ[μ] θ := boundedMultiplier_coe μ _ _ _ _
  have hfix : lpMultiplier μ Θ f = f := by
    apply Lp.ext
    filter_upwards [lpMultiplier_coe μ Θ f,hΘ,hfS] with x hx hθx hs
    rw [hx,hθx]
    by_cases hx0 : f x = 0
    · simp [hx0]
    · rw [show θ x = 1 from radialCutoff_eq_one p hR ((hs hx0).trans hrR.le),one_mul]
  let ws := fun i => lpMultiplier μ Θ (us i)
  let ks := fun i x => θ x*gs i x
  let Ws := fun i => lpMultiplier μ Θ (Gs i)+(C:ℝ) • lpAbs μ (us i-f)
  have hla (i : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (ks i) := by
    obtain ⟨D,hD⟩ := hl i
    exact lipschitz_mul_compact_cutoff hθ hD (radialCutoff_hasCompactSupport p hR)
      (fun x => by rw [abs_of_nonneg (hθb x).1]; exact (hθb x).2)
  have hae (i : ℕ) : ⇑(ws i) =ᵐ[μ] ks i := by
    filter_upwards [lpMultiplier_coe μ Θ (us i),hΘ,ha i] with x hx hθx hu'
    exact hx.trans (by rw [hθx,hu'])
  have hmaj (i : ℕ) : IsSlopeMajorant μ (ks i) (Ws i) := by
    obtain ⟨D,hD⟩ := hl i
    filter_upwards [Lp.coeFn_add (lpMultiplier μ Θ (Gs i)) ((C:ℝ) • lpAbs μ (us i-f)),
      lpMultiplier_coe μ Θ (Gs i),Lp.coeFn_smul (C:ℝ) (lpAbs μ (us i-f)),
      lpAbs_coe μ (us i-f),Lp.coeFn_sub (us i) f,hΘ,ha i,hm i,hfS]
      with x hadd hmul hsm habs hsub hθx hu' hGx hfSx
    have he : Ws i x = θ x*Gs i x+(C:ℝ)*|gs i x-f x| := by
      dsimp only [Ws]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at hadd hsm hsub
      rw [hadd,hmul,hsm,habs,hsub,hθx,hu']
    rw [he]
    refine ⟨add_nonneg (mul_nonneg (hθb x).1 hGx.1) (mul_nonneg C.coe_nonneg (abs_nonneg _)),?_⟩
    have hp := localSlope_mul_le hθ.continuous.continuousAt
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hD x))
    change localSlope (fun y => θ y*gs i y) x ≤ _ at hp ⊢
    apply hp.trans
    rw [abs_of_nonneg (hθb x).1,ENNReal.ofReal_add
      (mul_nonneg (hθb x).1 hGx.1) (mul_nonneg C.coe_nonneg (abs_nonneg _)),
      ENNReal.ofReal_mul (hθb x).1,ENNReal.ofReal_mul C.coe_nonneg]
    apply add_le_add (mul_le_mul' le_rfl hGx.2)
    by_cases hxR : dist p x < R
    · rw [radialCutoff_slope_zero p hR hxR,mul_zero]
      exact bot_le
    · have hfx : f x = 0 := by
        by_contra hf0
        exact hxR ((hfSx hf0).trans_lt hrR)
      rw [hfx,sub_zero,mul_comm (ENNReal.ofReal (C:ℝ))]
      apply mul_le_mul' le_rfl
      simpa only [ENNReal.ofReal_coe_nnreal] using localSlope_le_of_lipschitz hθ x
  refine ⟨ws,ks,Ws,lpMultiplier μ Θ G,2*R,hla,hae,hmaj,?_,?_,?_,?_,?_⟩
  · simpa only [ws,Function.comp_def,hfix] using (lpMultiplier μ Θ).continuous.continuousAt.tendsto.comp hu
  · have hz := ((lpAbs_continuous μ).continuousAt.tendsto.comp (hu.sub_const f)).const_smul (C:ℝ)
    simpa only [Ws,Function.comp_def,sub_self,lpAbs_zero,smul_zero,add_zero] using
      ((lpMultiplier μ Θ).continuous.continuousAt.tendsto.comp hlim).add hz
  · have hbound := boundedMultiplier_norm_le μ θ hθ.continuous.measurable 1
      (fun x => by rw [abs_of_nonneg (hθb x).1]; exact (hθb x).2)
    exact (Lp.norm_smul_le Θ G).trans (by simpa using mul_le_mul_of_nonneg_right hbound (norm_nonneg G))
  · intro i x
    exact ⟨mul_nonneg (hθb x).1 (hb i x).1,
      (mul_le_mul_of_nonneg_right (hθb x).2 (hb i x).1).trans (by simpa using (hb i x).2)⟩
  · intro i x hx
    by_contra h
    apply hx
    dsimp only [ks]
    rw [show θ x = 0 from radialCutoff_eq_zero p hR (le_of_not_ge h),zero_mul]
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
 

 theorem compact_bounded_integral_tendsto {fs : ℕ → X → ℝ} {f : X → ℝ}
    (p : X) (R M : ℝ) (hm : ∀ i, Measurable (fs i))
    (hb : ∀ i x, 0 ≤ fs i x ∧ fs i x ≤ M)
    (hs : ∀ i x, fs i x ≠ 0 → dist p x ≤ R)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => fs i x) atTop (𝓝 (f x)))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) :
    Tendsto (fun i => ∫x, ψ (fs i x) ∂μ) atTop (𝓝 (∫x, ψ (f x) ∂μ)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) M)).exists_bound_of_continuousOn hψ.continuousOn
  let S := Metric.closedBall p R
  apply tendsto_integral_of_dominated_convergence (S.indicator (fun _ => |C|))
  · exact fun i => (hψ.measurable.comp (hm i)).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_closedBall p R).measure_lt_top.ne).integrable_indicator
      (isCompact_closedBall p R).measurableSet
  · intro i
    filter_upwards with x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact (hC (fs i x) (hb i x)).trans (le_abs_self C)
    · rw [indicator_of_notMem hx]
      have hz : fs i x = 0 := by
        by_contra h0
        exact hx (by simpa only [S,Metric.mem_closedBall,dist_comm] using hs i x h0)
      rw [hz,hψ0,norm_zero]
  · filter_upwards [hlim] with x hx
    exact hψ.continuousAt.tendsto.comp hx
end

 
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
 

 theorem IsRelaxedSlope.compact_probability_recovery {f G : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hfM : ‖f‖ = 1)
    (M : ℝ≥0) (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ M)
    (p : X) {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) :
    ∃ (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ) (H : Lp ℝ 2 μ) (R : ℝ),
      (∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i)) ∧
      (∀ i, IsSlopeMajorant μ (gs i) (Gs i)) ∧
      Tendsto Gs atTop (𝓝 H) ∧ ‖H‖ ≤ ‖G‖ ∧
      (∀ i x, 0 ≤ gs i x ∧ gs i x ≤ 2*M) ∧
      (∀ i x, gs i x ≠ 0 → dist p x ≤ R) ∧
      (∀ i, ∫x, gs i x^2 ∂μ = 1) ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => gs i x) atTop (𝓝 (f x))) ∧
      Tendsto (fun i => ∫x, gs i x^2*Real.log (gs i x^2) ∂μ) atTop
        (𝓝 (∫x, f x^2*Real.log (f x^2) ∂μ)) := by
  obtain ⟨us,gs,Gs,H,R,hl,ha,hm,hu,hlim,hH,hb,hs⟩ := hG.compact_bounded_recovery μ M hf p hfS
  have hn : Tendsto (fun i => ‖us i‖) atTop (𝓝 (1:ℝ)) := by simpa [hfM] using hu.norm
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hn.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
  let a : ℕ → ℝ := fun i => ‖us (i+N)‖⁻¹
  have hnu (i : ℕ) : (1:ℝ)/2 < ‖us (i+N)‖ := hN _ (Nat.le_add_left N i)
  have hnpos (i : ℕ) : 0 < ‖us (i+N)‖ := by linarith [hnu i]
  have haP (i : ℕ) : 0 < a i := inv_pos.mpr (hnpos i)
  have haB (i : ℕ) : a i ≤ 2 := by
    dsimp [a]
    calc
      _ ≤ ((1:ℝ)/2)⁻¹ := (inv_le_inv₀ (hnpos i) (by norm_num)).mpr (hnu i).le
      _ = 2 := by norm_num
  have haL : Tendsto a atTop (𝓝 (1:ℝ)) := by
    simpa only [a,Function.comp_def,inv_one] using (hn.comp (tendsto_add_atTop_nat N)).inv₀ one_ne_zero
  let vs := fun i => a i • us (i+N)
  let ks := fun i x => a i*gs (i+N) x
  let Ws := fun i => a i • Gs (i+N)
  have hv : Tendsto vs atTop (𝓝 f) := by
    simpa only [vs,Function.comp_def,one_smul] using haL.smul (hu.comp (tendsto_add_atTop_nat N))
  have hW : Tendsto Ws atTop (𝓝 H) := by
    simpa only [Ws,Function.comp_def,one_smul] using haL.smul (hlim.comp (tendsto_add_atTop_nat N))
  have hva (i : ℕ) : ⇑(vs i) =ᵐ[μ] ks i := by
    filter_upwards [Lp.coeFn_smul (a i) (us (i+N)),ha (i+N)] with x hx hx'
    simpa only [Pi.smul_apply,smul_eq_mul,hx'] using hx
  have hkb (i : ℕ) (x : X) : 0 ≤ ks i x ∧ ks i x ≤ 2*M := by
    exact ⟨mul_nonneg (haP i).le (hb (i+N) x).1,
      mul_le_mul (haB i) (hb (i+N) x).2 (hb (i+N) x).1 (by norm_num)⟩
  have hks (i : ℕ) (x : X) (hx : ks i x ≠ 0) : dist p x ≤ R := by
    apply hs (i+N) x
    exact (mul_ne_zero_iff.mp hx).2
  have hkm (i : ℕ) : ∫x, ks i x^2 ∂μ = 1 := by
    rw [show (∫x, ks i x^2 ∂μ) = ∫x, vs i x^2 ∂μ from
      integral_congr_ae ((hva i).symm.mono fun x hx => congrArg (fun a : ℝ => a^2) hx),integral_sq_Lp]
    have hnorm : ‖vs i‖ = 1 := by
      change ‖a i • us (i+N)‖ = 1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (haP i)]
      exact inv_mul_cancel₀ (ne_of_gt (hnpos i))
    rw [hnorm,one_pow]
  have hkl (i : ℕ) : ∃ C : ℝ≥0, LipschitzWith C (ks i) := by
    obtain ⟨C,hC⟩ := hl (i+N)
    exact ⟨‖a i‖₊*C,lipschitzWith_const_mul_real hC (a i)⟩
  have hkg (i : ℕ) : IsSlopeMajorant μ (ks i) (Ws i) := by
    exact (hm (i+N)).const_mul μ (haP i).le
  obtain ⟨s,hsm,hsa⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hka : ∀ᵐ x ∂μ, Tendsto (fun i => ks (s i) x) atTop (𝓝 (f x)) := by
    filter_upwards [hsa,ae_all_iff.mpr (fun i => hva (s i))] with x hx heq
    simpa only [heq] using hx
  refine ⟨fun i => ks (s i),fun i => Ws (s i),H,R,fun i => hkl (s i),
    fun i => hkg (s i),hW.comp hsm.tendsto_atTop,hH,fun i x => hkb (s i) x,
    fun i x => hks (s i) x,fun i => hkm (s i),hka,?_⟩
  exact compact_bounded_integral_tendsto μ p R (2*M) (fun i => (hkl (s i)).choose_spec.continuous.measurable)
    (fun i x => hkb (s i) x) (fun i x => hks (s i) x) hka
    (Real.continuous_mul_log.comp (continuous_id.pow 2)) (by simp)

end RegularPointCoordinates

end OAI
