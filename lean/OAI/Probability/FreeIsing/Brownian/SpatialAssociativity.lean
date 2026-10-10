import OAI.Probability.FreeIsing.Brownian.ArrayFiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.ContinuousAssociativity
import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Martingales.SpatialLimit
import OAI.Probability.FreeIsing.Posterior.FilteringRepresentationClosure
import OAI.Probability.FreeIsing.Stochastic.IntegralAssociativityLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianSpatialAssociativity

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

private theorem tendsto_zero_of_uniform_approximation
    {A N : Type*} {l : Filter N} {k : Filter A} [k.NeBot]
    {f : N → ℝ} {g : A → N → ℝ} {r : A → ℝ}
    (h0 : ∀ n, 0 ≤ f n) (hr : Tendsto r k (𝓝 0))
    (hg : ∀ a, Tendsto (g a) l (𝓝 0))
    (hb : ∀ a n, f n ≤ r a + g a n) : Tendsto f l (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (h0 n))
  · intro b hb0
    obtain ⟨a, ha⟩ := (hr.eventually (gt_mem_nhds (half_pos hb0))).exists
    filter_upwards [(hg a).eventually (gt_mem_nhds (half_pos hb0))] with n hn
    linarith [hb a n]

omit mΩ in
theorem uniformSum_finiteSum (I : ι → ℝ≥0 → Ω → ℝ)
    (K : ℝ≥0 → Ω → ℝ) (q : Finset ι) (T : ℝ≥0) (n : ℕ) :
    BrownianGrid.uniformSum (MartingaleSpatialLimit.finiteSum I q) K T n =
      fun ω => ∑ a ∈ q, BrownianGrid.uniformSum (I a) K T n ω := by
  funext ω
  simp only [BrownianGrid.uniformSum, BrownianGrid.integralSum,
    MartingaleSpatialLimit.finiteSum]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem uniformSum_memLp {M K : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hK : ∀ t, AEStronglyMeasurable (K t) P)
    {C : ℝ} (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (BrownianGrid.uniformSum M K T n) 2 P := by
  exact SimpleIntegral.coarseTransform_memLp
    (fun i => K (BrownianGrid.uniformGrid T n i))
    (fun i => hK _) (fun _ => C) (fun i => hb _)
    (fun i => hM2 (BrownianGrid.uniformGrid T n i)) n

theorem uniformSum_spatial_tail_le [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {I : ι → ℝ≥0 → Ω → ℝ}
    {Y K : ℝ≥0 → Ω → ℝ}
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hK : StronglyAdapted F K) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (q : Finset ι) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (BrownianGrid.uniformSum Y K T n ω -
      BrownianGrid.uniformSum (MartingaleSpatialLimit.finiteSum I q) K T n ω) ^ 2 ∂P) ≤
      C ^ 2 * ∫ ω, (Y T ω - ∑ a ∈ q, I a T ω) ^ 2 ∂P := by
  by_cases hn : n = 0
  · subst n
    simp only [BrownianGrid.uniformSum, BrownianGrid.integralSum,
      Finset.range_zero, Finset.sum_empty, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact mul_nonneg (sq_nonneg C) (integral_nonneg (fun ω => sq_nonneg _))
  have h := MartingaleTransformL2.integral_sq_grid_transform_le_terminal
    (hY.sub (MartingaleSpatialLimit.finiteSum_martingale hI q))
    (fun t => (hY2 t).sub (MartingaleSpatialLimit.finiteSum_memLp hI2 q t))
    (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
    (fun i => K (BrownianGrid.uniformGrid T n i)) (fun i => hK _) hC (fun i => hb _) n
  rw [BrownianGrid.uniformGrid_end T (Nat.pos_of_ne_zero hn)] at h
  simpa only [BrownianGrid.uniformSum, BrownianGrid.integralSum,
    MartingaleSpatialLimit.finiteSum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    sub_sub_sub_comm] using h

theorem uniformSum_spatial_limit_of_channel_limits [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {I : ι → ℝ≥0 → Ω → ℝ}
    {Y K : ℝ≥0 → Ω → ℝ} {J : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hJ2 : ∀ a, MemLp (J a) 2 P) (hZ2 : MemLp Z 2 P)
    (hK : StronglyAdapted F K) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (hsumJ : HasSum (fun a => (hJ2 a).toLp (J a)) (hZ2.toLp Z))
    (hlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (I a) K T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum Y K T n ω - Z ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  have hKm (t : ℝ≥0) : AEStronglyMeasurable (K t) P :=
    ((hK t).mono (F.le t)).aestronglyMeasurable
  let S := MartingaleSpatialLimit.finiteSum I
  let R (q : Finset ι) (ω : Ω) := ∑ a ∈ q, J a ω
  have hS2 (q : Finset ι) (t : ℝ≥0) : MemLp (S q t) 2 P :=
    MartingaleSpatialLimit.finiteSum_memLp hI2 q t
  have hR2 (q : Finset ι) : MemLp (R q) 2 P :=
    memLp_finsetSum q (fun a _ => hJ2 a)
  have hX2 (n : ℕ) : MemLp (BrownianGrid.uniformSum Y K T n) 2 P :=
    uniformSum_memLp hY2 hKm hb T n
  have hXS2 (q : Finset ι) (n : ℕ) :
      MemLp (BrownianGrid.uniformSum (S q) K T n) 2 P :=
    uniformSum_memLp (hS2 q) hKm hb T n
  have hYtail := PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun a => I a T) (fun a => hI2 a T) (hY2 T) hsumI
  have hZtail := PredictableL2.tendsto_integral_sq_error_of_hasSum J hJ2 hZ2 hsumJ
  have hfinite (q : Finset ι) : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (S q) K T n ω - R q ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hl := FilteringRepresentationClosure.tendsto_integral_sq_fintype_sum_error
      (fun a : q => hJ2 a) (fun a n => uniformSum_memLp (hI2 a) hKm hb T n)
      (fun a => hlim a)
    apply hl.congr
    intro n
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    simp only [S, R, uniformSum_finiteSum]
    rw [Finset.sum_coe_sort q (fun a => BrownianGrid.uniformSum (I a) K T n ω),
      Finset.sum_coe_sort q (fun a => J a ω)]
  apply tendsto_zero_of_uniform_approximation (k := (atTop : Filter (Finset ι)))
    (fun n => integral_nonneg (fun ω => sq_nonneg _))
    (r := fun q : Finset ι =>
      2 * C ^ 2 * (∫ ω, (Y T ω - S q T ω) ^ 2 ∂P) +
        4 * ∫ ω, (Z ω - R q ω) ^ 2 ∂P)
    (g := fun q n => 4 * ∫ ω,
      (BrownianGrid.uniformSum (S q) K T n ω - R q ω) ^ 2 ∂P)
  · simpa only [S, R, MartingaleSpatialLimit.finiteSum, sub_sq_comm,
      mul_zero, add_zero] using
      (hYtail.const_mul (2 * C ^ 2)).add (hZtail.const_mul 4)
  · intro q
    simpa only [mul_zero] using (hfinite q).const_mul 4
  · intro q n
    have h1 := BrownianGrid.integral_sq_sub_le_two (hX2 n) hZ2 (hXS2 q n)
    have h2 := BrownianGrid.integral_sq_sub_le_two hZ2 (hXS2 q n) (hR2 q)
    have h3 := uniformSum_spatial_tail_le hI hY hI2 hY2 hK hC hb q T n
    change (∫ ω, (BrownianGrid.uniformSum Y K T n ω -
      BrownianGrid.uniformSum (S q) K T n ω) ^ 2 ∂P) ≤
      C ^ 2 * (∫ ω, (Y T ω - S q T ω) ^ 2 ∂P) at h3
    linarith

theorem summable_integrated_mul_energy [IsFiniteMeasure P]
    {H : ι → ℝ≥0 → Ω → ℝ} {K : ℝ≥0 → Ω → ℝ}
    (hH : ∀ a t, AEStronglyMeasurable (H a t) P)
    (hK : ∀ t, AEStronglyMeasurable (K t) P)
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C : ι → ℝ} {D : ℝ} (hC : ∀ a, 0 ≤ C a) (hD : 0 ≤ D)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D) (T : ℝ≥0)
    (henergy : Summable (fun a => ∫ r in (0 : ℝ)..(T : ℝ),
      ∫ ω, H a r.toNNReal ω ^ 2 ∂P)) :
    Summable (fun a => ∫ r in (0 : ℝ)..(T : ℝ),
      ∫ ω, (K r.toNNReal ω * H a r.toNNReal ω) ^ 2 ∂P) := by
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P :=
    MemLp.of_bound (hH a t) (C a) ((hbH a).mono (fun ω hω => hω t))
  have hKH2 (a : ι) (t : ℝ≥0) : MemLp (fun ω => K t ω * H a t ω) 2 P :=
    SimpleIntegral.bounded_mul_memLp (hK t) (hbK.mono (fun ω hω => hω t)) (hH2 a t)
  have hcontH (a : ι) : Continuous (fun r : ℝ => ∫ ω, H a r.toNNReal ω ^ 2 ∂P) :=
    (EnergyRiemann.continuous_energy (hH a) (hcH a) (hC a) (hbH a)).comp (by fun_prop)
  have hcontKH (a : ι) :
      Continuous (fun r : ℝ => ∫ ω, (K r.toNNReal ω * H a r.toNNReal ω) ^ 2 ∂P) := by
    apply (EnergyRiemann.continuous_energy (fun t => (hK t).mul (hH a t))
      (hcK.and (hcH a) |>.mono (fun ω hω => hω.1.mul hω.2))
      (mul_nonneg hD (hC a)) ?_).comp (by fun_prop)
    filter_upwards [hbK, hbH a] with ω hKω hHω
    intro t
    exact (abs_mul _ _).trans_le (mul_le_mul (hKω t) (hHω t) (abs_nonneg _) hD)
  apply Summable.of_nonneg_of_le
    (fun a => intervalIntegral.integral_nonneg T.coe_nonneg
      (fun r _ => integral_nonneg (fun ω => sq_nonneg _))) ?_
    (henergy.mul_left (D ^ 2))
  intro a
  calc
    _ ≤ ∫ r in (0 : ℝ)..(T : ℝ), D ^ 2 * ∫ ω, H a r.toNNReal ω ^ 2 ∂P := by
      apply intervalIntegral.integral_mono_ae_restrict T.coe_nonneg
        ((hcontKH a).intervalIntegrable _ _) (((hcontH a).intervalIntegrable _ _).const_mul _)
      apply Eventually.of_forall
      intro r
      dsimp only
      rw [← integral_const_mul]
      apply integral_mono_ae (hKH2 a r.toNNReal).integrable_sq
        ((hH2 a r.toNNReal).integrable_sq.const_mul _)
      filter_upwards [hbK] with ω hω
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (hω r.toNNReal))
        (sq_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem exists_terminal_spatial_associative_integral [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I : ι → ℝ≥0 → Ω → ℝ}
    {Y K : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P) (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : StronglyAdapted F K)
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C : ι → ℝ} {D : ℝ} (hC : ∀ a, 0 ≤ C a) (hD : 0 ≤ D)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (hIlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a T ω) ^ 2 ∂P) atTop (𝓝 0))
    (henergy : Summable (fun a => ∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H a r.toNNReal ω ^ 2 ∂P)) :
    ∃ (J : ι → Ω → ℝ) (Z : Ω → ℝ) (hJ2 : ∀ a, MemLp (J a) 2 P) (hZ2 : MemLp Z 2 P),
      Measurable Z ∧ AEStronglyMeasurable[F T] Z P ∧ (∫ ω, Z ω ∂P) = 0 ∧
      (∫ ω, Z ω ^ 2 ∂P) = ∑' a, ∫ r in (0 : ℝ)..(T : ℝ),
        ∫ ω, (K r.toNNReal ω * H a r.toNNReal ω) ^ 2 ∂P ∧
      HasSum (fun a => (hJ2 a).toLp (J a)) (hZ2.toLp Z) ∧
      (∀ a, Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum (B a) (fun t ω => K t ω * H a t ω) T n ω - J a ω) ^ 2 ∂P)
        atTop (𝓝 0)) ∧
      Tendsto (fun n => ∫ ω, (BrownianGrid.uniformSum Y K T n ω - Z ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
  have hKH (a : ι) : StronglyAdapted F (fun t ω => K t ω * H a t ω) :=
    fun t => (hK t).mul (hH a t)
  have hcKH (a : ι) : ∀ᵐ ω ∂P, Continuous (fun t => K t ω * H a t ω) :=
    (hcK.and (hcH a)).mono (fun ω hω => hω.1.mul hω.2)
  have hbKH (a : ι) : ∀ᵐ ω ∂P, ∀ t, |K t ω * H a t ω| ≤ D * C a := by
    filter_upwards [hbK, hbH a] with ω hKω hHω
    intro t
    exact (abs_mul _ _).trans_le (mul_le_mul (hKω t) (hHω t) (abs_nonneg _) hD)
  have henergyKH := summable_integrated_mul_energy
    (fun a t => ((hH a t).mono (F.le t)).aestronglyMeasurable)
    (fun t => ((hK t).mono (F.le t)).aestronglyMeasurable)
    hcH hcK hC hD hbH hbK T henergy
  obtain ⟨J, Z, hJ2, hJlim, hmZ, hZterm, hZ2, hZ0, hZiso, hZlim⟩ :=
    BrownianArrayFiltration.exists_infinite_integral hB hAd hpast hcross
      (fun a t ω => K t ω * H a t ω) hKH hcKH (fun a => D * C a)
      (fun a => mul_nonneg hD (hC a)) hbKH T henergyKH
  have hsumJ : HasSum (fun a => (hJ2 a).toLp (J a)) (hZ2.toLp Z) := by
    have hl := (SimpleIntegral.tendsto_toLp_iff_meanSquare
      (fun q : Finset ι => memLp_finsetSum q (fun a _ => hJ2 a)) hZ2).mpr hZlim
    change Tendsto (fun q : Finset ι => ∑ a ∈ q, (hJ2 a).toLp (J a)) atTop (𝓝 (hZ2.toLp Z))
    exact hl.congr (fun q => PredictableL2.toLp_finsetSum J hJ2 q)
  refine ⟨J, Z, hJ2, hZ2, hmZ, hZterm, hZ0, hZiso, hsumJ, hJlim, ?_⟩
  apply uniformSum_spatial_limit_of_channel_limits hI hY hI2 hY2 hJ2 hZ2 hK hD
    (fun t => hbK.mono (fun ω hω => hω t)) T hsumI hsumJ
  intro a
  exact BrownianContinuousAssociativity.uniformSum_associativity (hB a) (hAd a)
    (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past (hpast s t hst) a)
    (hH a) hK hcK (hC a) hD (hbH a) hbK (hI a) (hI2 a) T (hIlim a) (hJ2 a) (hJlim a)

end Problem367.BrownianSpatialAssociativity

end

end OAI
