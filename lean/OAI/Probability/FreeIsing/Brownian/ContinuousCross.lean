import OAI.Probability.FreeIsing.Brownian.ArrayFiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.IntegralHorizon
import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianCross

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianContinuousCross

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_eLpNorm_mul_sub {N : Type*} {l : Filter N}
    {f g : N → Ω → ℝ} {u v : Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 2 P) (hg : ∀ n, MemLp (g n) 2 P)
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hfu : Tendsto (fun n => eLpNorm (f n - u) 2 P) l (𝓝 0))
    (hgv : Tendsto (fun n => eLpNorm (g n - v) 2 P) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n * g n - u * v) 1 P) l (𝓝 0) := by
  let M : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P →L[ℝ] Lp ℝ 1 P :=
    ContinuousLinearMap.holderL P 2 2 1 (ContinuousLinearMap.mul ℝ ℝ)
  have hmul {a b : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
      M (ha.toLp a) (hb.toLp b) = (memLp_one_iff_integrable.mpr (ha.integrable_mul hb)).toLp (a * b) := by
    apply Lp.ext
    have hm := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1)
      (ha.toLp a) (hb.toLp b)
    filter_upwards [hm, ha.coeFn_toLp, hb.coeFn_toLp,
      (memLp_one_iff_integrable.mpr (ha.integrable_mul hb)).coeFn_toLp] with ω hm hωa hωb hab
    change M (ha.toLp a) (hb.toLp b) ω = (ha.toLp a) ω * (hb.toLp b) ω at hm
    rw [hωa, hωb] at hm
    exact hm.trans hab.symm
  have hfLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hfu
  have hgLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg v hv).mpr hgv
  have h := (M.continuous₂.tendsto (hu.toLp u, hv.toLp v)).comp
    (hfLp.prodMk_nhds hgLp)
  change Tendsto (fun n => M ((hf n).toLp (f n)) ((hg n).toLp (g n))) l
    (𝓝 (M (hu.toLp u) (hv.toLp v))) at h
  simp only [hmul] at h
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => f n * g n)
    (fun n => (memLp_one_iff_integrable.mpr ((hf n).integrable_mul (hg n)))) (u * v)
    (memLp_one_iff_integrable.mpr (hu.integrable_mul hv))).mp h

theorem condExp_ae_eq_of_L1_limits
    {ι N : Type*} [LinearOrder ι] [IsFiniteMeasure P]
    {F : Filtration ι mΩ} {l : Filter N} [l.NeBot]
    {X : N → ι → Ω → ℝ} (hX : ∀ n, Martingale (X n) F P)
    {s t : ι} (hst : s ≤ t) {u v : Ω → ℝ}
    (hu : StronglyMeasurable[F s] u) (hui : Integrable u P) (hvi : Integrable v P)
    (hs : Tendsto (fun n => eLpNorm (X n s - u) 1 P) l (𝓝 0))
    (ht : Tendsto (fun n => eLpNorm (X n t - v) 1 P) l (𝓝 0)) :
    P[v | F s] =ᵐ[P] u := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) hvi
    (fun A hA _ => hui.integrableOn) ?_ hu.aestronglyMeasurable).symm
  intro A hA hAfin
  have hs' := tendsto_setIntegral_of_L1' u
    (Eventually.of_forall (fun n => (hX n).integrable s)) hs A
  have ht' := tendsto_setIntegral_of_L1' v
    (Eventually.of_forall (fun n => (hX n).integrable t)) ht A
  have heq : (fun n => ∫ ω in A, X n s ω ∂P) =
      (fun n => ∫ ω in A, X n t ω ∂P) :=
    funext fun n => (hX n).setIntegral_eq hst hA
  rw [heq] at hs'
  exact tendsto_nhds_unique hs' ht'

theorem global_uniform_limits_product_martingale
    {B C H G I J : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    (hpair : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t →
      IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P)
    (hH : StronglyAdapted F H) (hG : StronglyAdapted F G)
    {K L : ℝ} (hboundH : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ K)
    (hboundG : ∀ᵐ ω ∂P, ∀ t, ‖G t ω‖ ≤ L)
    (hI : StronglyAdapted F I) (hJ : StronglyAdapted F J)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hlimI : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (hlimJ : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum C G N n t ω - J t ω) ^ 2 ∂P)
        atTop (𝓝 0)) :
    Martingale (fun t ω => I t ω * J t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hB2 (t : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hC2 (t : ℝ≥0) := (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hBH (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖H t ω‖ ≤ K := hboundH.mono fun ω hω => hω t
  have hCG (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖G t ω‖ ≤ L := hboundG.mono fun ω hω => hω t
  refine ⟨fun t => (hI t).mul (hJ t), ?_⟩
  intro s t hst
  obtain ⟨N, hN⟩ := exists_nat_ge t
  have htN : t ≤ ((N + 1 : ℕ) : ℝ≥0) :=
    hN.trans (by exact_mod_cast Nat.le_succ N)
  let X := fun n => BrownianIntegralProcess.stoppedUniformSum B H ((N + 1 : ℕ) : ℝ≥0) n
  let Y := fun n => BrownianIntegralProcess.stoppedUniformSum C G ((N + 1 : ℕ) : ℝ≥0) n
  have hX2 (n : ℕ) (r : ℝ≥0) : MemLp (X n r) 2 P := by
    apply memLp_finsetSum (Finset.range n)
    intro i hi
    exact StoppedBrownianCross.intervalSum_memLp_two_of_bounded hB2
      (hH _) (hBH _) r
  have hY2 (n : ℕ) (r : ℝ≥0) : MemLp (Y n r) 2 P := by
    apply memLp_finsetSum (Finset.range n)
    intro i hi
    exact StoppedBrownianCross.intervalSum_memLp_two_of_bounded hC2
      (hG _) (hCG _) r
  have hM (n : ℕ) : Martingale (fun r ω => X n r ω * Y n r ω) F P :=
    StoppedBrownianCross.stopped_brownian_sum_product_martingale hB hC hAdB hAdC
      hpair hind (BrownianGrid.uniformGrid ((N + 1 : ℕ) : ℝ≥0) n) (BrownianGrid.uniformGrid_mono _ _)
      (fun i => H (BrownianGrid.uniformGrid ((N + 1 : ℕ) : ℝ≥0) n i))
      (fun i => G (BrownianGrid.uniformGrid ((N + 1 : ℕ) : ℝ≥0) n i))
      (fun i => hH _) (fun i => hG _) (fun _ => K) (fun _ => L)
      (fun i => hBH _) (fun i => hCG _) n
  have hprod (r : ℝ≥0) (hr : r ≤ ((N + 1 : ℕ) : ℝ≥0)) :
      Tendsto (fun n => eLpNorm (X n r * Y n r - I r * J r) 1 P) atTop (𝓝 0) :=
    tendsto_eLpNorm_mul_sub (fun n => hX2 n r) (fun n => hY2 n r) (hI2 r) (hJ2 r)
      (CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
        (fun n => hX2 n r) (hI2 r) (hlimI (N + 1) (Nat.succ_pos N) r hr))
      (CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
        (fun n => hY2 n r) (hJ2 r) (hlimJ (N + 1) (Nat.succ_pos N) r hr))
  exact condExp_ae_eq_of_L1_limits hM hst ((hI s).mul (hJ s))
    ((hI2 s).integrable_mul (hJ2 s)) ((hI2 t).integrable_mul (hJ2 t))
    (hprod s (hst.trans htN)) (hprod t htN)

end Problem367.BrownianContinuousCross

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B H I : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem global_uniform_limits_pairwise_product_martingale
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hH : ∀ a, StronglyAdapted F (H a))
    {K : ι → ℝ} (hbound : ∀ a, ∀ᵐ ω ∂P, ∀ t, ‖H a t ω‖ ≤ K a)
    (hI : ∀ a, StronglyAdapted F (I a))
    (hI2 : ∀ a t, MemLp (I a t) 2 P)
    (hlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
        atTop (𝓝 0)) :
    Pairwise fun a b => Martingale (fun t ω => I a t ω * I b t ω) F P := by
  intro a b hab
  apply BrownianContinuousCross.global_uniform_limits_product_martingale
    (hB a) (hB b) (hAd a) (hAd b) ?_ (fun s t hst => hind s t hst hab)
    (hH a) (hH b) (hbound a) (hbound b) (hI a) (hI b) (hI2 a) (hI2 b)
    (hlim a) (hlim b)
  intro s t hst
  apply indep_of_indep_of_le_left (hpast s t hst)
  have hm : Measurable[MeasurableSpace.comap
      (fun ω c => B c t ω - B c s ω) inferInstance]
      (fun ω c => B c t ω - B c s ω) := measurable_iff_comap_le.mpr le_rfl
  exact (((measurable_pi_apply a).comp hm).prodMk
    ((measurable_pi_apply b).comp hm)).comap_le

theorem exists_global_continuous_channel_integrals
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, StronglyAdapted F (H a))
    (hHc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {K : ι → ℝ} (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ K a) :
    ∃ I : ι → ℝ≥0 → Ω → ℝ,
      (∀ a, IsStronglyPredictable F (I a)) ∧
      (∀ a, Martingale (I a) F P) ∧
      (∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω)) ∧
      (∀ a t, MemLp (I a t) 2 P) ∧
      (∀ a, I a 0 =ᵐ[P] 0) ∧
      (∀ a t, (∫ ω, I a t ω ∂P) = 0) ∧
      (∀ a t, (∫ ω, (I a t ω) ^ 2 ∂P) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H a s.toNNReal ω) ^ 2 ∂P) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (Pairwise fun a b => Martingale (fun t ω => I a t ω * I b t ω) F P) := by
  have hex (a : ι) := BrownianIntegralProcess.exists_global_continuous_uniform_integral
    (hB a) (hAd a)
    (fun s t hst => coordinate_increment_indep_past (hpast s t hst) a)
    (hBc a) (hH a) (hHc a) (hK a) (hbound a)
  choose I hIp hIM hIc hI2 hIz hImean hIiso hIlim using hex
  refine ⟨I, hIp, hIM, hIc, hI2, hIz, hImean, hIiso, hIlim, ?_⟩
  exact global_uniform_limits_pairwise_product_martingale hB hAd hpast hind hH
    (by simpa only [Real.norm_eq_abs] using hbound)
    (fun a => (hIM a).stronglyAdapted) hI2 hIlim

end Problem367.BrownianArrayFiltration

end

end OAI
