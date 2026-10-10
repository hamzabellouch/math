import OAI.Probability.FKMaps.Offspring

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def bridgePath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(unitInterval, ℝ) :=
  brownianPath B ω - B 1 ω • ⟨fun t => (t:ℝ), continuous_subtype_val⟩

lemma bridgePath_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    AEMeasurable (bridgePath B) μ :=
  (brownianPath_aemeasurable hB).sub ((hB.aemeasurable 1).smul aemeasurable_const)

lemma bridgePath_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : unitInterval,
      bridgePath B ω t = B ⟨(t:ℝ),t.property.1⟩ ω - (t:ℝ)*B 1 ω := by
  filter_upwards [brownianPath_ae_eq hB] with ω hω
  intro t
  simp only [bridgePath, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul, hω, mul_comm]

lemma bridge_joint_gaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    IsGaussianProcess (Sum.elim
      (fun (t : unitInterval) ω => B ⟨(t:ℝ),t.property.1⟩ ω-(t:ℝ)*B 1 ω)
      (fun (_ : Unit) ω => B 1 ω)) μ := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro s
  cases s with
  | inl t =>
    let u : ℝ≥0 := ⟨(t:ℝ),t.property.1⟩
    refine ⟨{u,1},
      { toFun x := x ⟨u, by simp⟩ - (t:ℝ) * x ⟨1, by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
    intro ω
    rfl
  | inr t =>
    refine ⟨{1},
      { toFun x := x ⟨1, by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rfl

lemma bridge_covariance_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (t : unitInterval) :
    cov[fun ω => B ⟨(t:ℝ),t.property.1⟩ ω-(t:ℝ)*B 1 ω, B 1; μ] = 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let u : ℝ≥0 := ⟨(t:ℝ), unitInterval.nonneg t⟩
  change cov[fun ω => B u ω - (t:ℝ) * B 1 ω, B 1; μ] = 0
  rw [covariance_fun_sub_left (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _)
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval]
  simp only [min_self, NNReal.coe_one, mul_one]
  change min (t:ℝ) (1:ℝ) - (t:ℝ) = 0
  rw [min_eq_left t.property.2, sub_self]

lemma bridge_process_indep_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    IndepFun (fun ω (t : unitInterval) =>
      B ⟨(t:ℝ),t.property.1⟩ ω-(t:ℝ)*B 1 ω) (B 1) μ := by
  have h := (bridge_joint_gaussian hB).indepFun_of_covariance_eq_zero
    (fun t => (hB.aemeasurable _).sub ((hB.aemeasurable 1).const_mul _))
    (fun _ => hB.aemeasurable 1) (fun t _ => bridge_covariance_endpoint hB t)
  exact h.comp measurable_id (measurable_pi_apply ())

lemma indepFun_of_measurableEmbedding_left {Ω E F G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    {μ : Measure Ω} {X : Ω → E} {Y : Ω → F} {f : E → G}
    (hf : MeasurableEmbedding f) (h : IndepFun (f ∘ X) Y μ) : IndepFun X Y μ := by
  simp only [IndepFun, Kernel.IndepFun] at h ⊢
  rw [← MeasurableSpace.comap_comp, hf.comap_eq] at h
  exact h

lemma bridgePath_indep_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    IndepFun (bridgePath B) (B 1) μ := by
  let D := TopologicalSpace.denseSeq unitInterval
  let f : C(unitInterval,ℝ) → (ℕ → ℝ) := fun g n => g (D n)
  have hf : MeasurableEmbedding f := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro a b hab
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        a.continuous b.continuous hab)
  apply indepFun_of_measurableEmbedding_left hf
  have h := (bridge_process_indep_endpoint hB.toIsPreBrownianReal).comp
    (φ := fun a : unitInterval → ℝ => fun n : ℕ => a (D n))
    (by fun_prop) measurable_id
  apply h.congr ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [bridgePath_ae_eq hB] with ω hω
  funext n
  exact (hω (D n)).symm

lemma gaussian_softCutoff_pos {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ x, softCutoff ε x ∂gaussianReal 0 1 := by
  rw [integral_pos_iff_support_of_nonneg (softCutoff_nonneg ε)
    (softCutoff_integrable aemeasurable_id hε), softCutoff_support hε, pos_iff_ne_zero]
  intro h
  have hv := gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hv
  linarith

lemma brownian_softCutoff_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ ω, softCutoff ε (B 1 ω) ∂μ := by
  change 0 < ∫ ω, (softCutoff ε ∘ B 1) ω ∂μ
  rw [(hB.hasLaw_eval 1).integral_comp (softCutoff_continuous ε).aestronglyMeasurable]
  exact gaussian_softCutoff_pos hε

lemma brownian_dist_bridge_le {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    dist (brownianPath B ω) (bridgePath B ω) ≤ |B 1 ω| := by
  rw [dist_eq_norm]
  change ‖brownianPath B ω -
    (brownianPath B ω - B 1 ω • (⟨fun t : unitInterval => (t:ℝ),continuous_subtype_val⟩ : C(unitInterval,ℝ)))‖ ≤ _
  rw [sub_sub_cancel, norm_smul,Real.norm_eq_abs]
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro t
  simp only [ContinuousMap.coe_mk, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  exact t.property.2

theorem brownian_soft_bridge_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {F : C(unitInterval,ℝ) → ℝ} {M : ℝ} {L : ℝ≥0}
    (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) {ε : ℝ} (hε : 0 < ε) :
    |(∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) /
        (∫ ω, softCutoff ε (B 1 ω) ∂μ) -
      ∫ ω, F (bridgePath B ω) ∂μ| ≤ (L:ℝ)*ε := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  have hX := brownianPath_aemeasurable hB
  have hY := bridgePath_aemeasurable hB
  have hg := softCutoff_integrable (hB.aemeasurable 1) hε
  have hFg (Z : Ω → C(unitInterval,ℝ)) (hZ : AEMeasurable Z μ) :
      Integrable (fun ω => F (Z ω)*softCutoff ε (B 1 ω)) μ := by
    apply (hg.norm.const_mul M).mono'
      ((hF.continuous.aestronglyMeasurable.comp_aemeasurable hZ).mul hg.aestronglyMeasurable)
    filter_upwards [] with ω
    change ‖F (Z ω)*softCutoff ε (B 1 ω)‖ ≤ M*‖softCutoff ε (B 1 ω)‖
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (hFM _) (abs_nonneg _)
  have hdiff : Integrable (fun ω =>
      (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)) μ := by
    have h := (hFg _ hX).sub (hFg _ hY)
    apply h.congr
    filter_upwards [] with ω
    change F (brownianPath B ω)*softCutoff ε (B 1 ω) -
      F (bridgePath B ω)*softCutoff ε (B 1 ω) = _
    ring
  have heq := (bridgePath_indep_endpoint hB).integral_fun_comp_mul_comp
    hY (hB.aemeasurable 1) hF.continuous.aestronglyMeasurable
    (softCutoff_continuous ε).aestronglyMeasurable
  have hb : |∫ ω, (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω) ∂μ| ≤
      (L:ℝ)*ε * ∫ ω, softCutoff ε (B 1 ω) ∂μ := by
    calc
      _ ≤ ∫ ω, |(F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω))
      _ ≤ ∫ ω, ((L:ℝ)*ε)*softCutoff ε (B 1 ω) ∂μ := by
        apply integral_mono_ae hdiff.norm (hg.const_mul _)
        filter_upwards [] with ω
        change |(F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)| ≤ _
        rw [abs_mul,abs_of_nonneg (softCutoff_nonneg _ _)]
        by_cases hgω : softCutoff ε (B 1 ω) = 0
        · simp only [hgω,mul_zero,le_refl]
        apply mul_le_mul_of_nonneg_right _ (softCutoff_nonneg _ _)
        have heω : |B 1 ω| < ε := (softCutoff_pos_iff hε).mp
          (lt_of_le_of_ne (softCutoff_nonneg _ _) (Ne.symm hgω))
        calc
          _ ≤ (L:ℝ)*dist (brownianPath B ω) (bridgePath B ω) := by
            simpa only [Real.dist_eq] using hF.dist_le_mul (brownianPath B ω) (bridgePath B ω)
          _ ≤ (L:ℝ)*ε := mul_le_mul_of_nonneg_left
            ((brownian_dist_bridge_le B ω).trans heω.le) L.coe_nonneg
      _ = _ := integral_const_mul _ _
  rw [show (∫ ω, (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω) ∂μ) =
      (∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) -
      (∫ ω, F (bridgePath B ω) ∂μ)*(∫ ω, softCutoff ε (B 1 ω) ∂μ) by
        rw [show (fun ω => (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)) =
          (fun ω => F (brownianPath B ω)*softCutoff ε (B 1 ω) -
            F (bridgePath B ω)*softCutoff ε (B 1 ω)) by funext ω; ring,
          integral_sub (hFg _ hX) (hFg _ hY),heq]] at hb
  have hpos := brownian_softCutoff_pos hB.toIsPreBrownianReal hε
  have hform :
      (∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) /
          (∫ ω, softCutoff ε (B 1 ω) ∂μ) - (∫ ω, F (bridgePath B ω) ∂μ) =
      ((∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) -
        (∫ ω, F (bridgePath B ω) ∂μ)*(∫ ω, softCutoff ε (B 1 ω) ∂μ)) /
          (∫ ω, softCutoff ε (B 1 ω) ∂μ) := by
    rw [sub_div,mul_div_cancel_right₀ _ hpos.ne']
  rw [hform,abs_div,abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr hb

lemma integral_tendsto_of_tendstoInDistribution
    {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ∀ i, Measure (Ω i)} {ν : Measure Ω'} [∀ i, IsProbabilityMeasure (μ i)]
    [IsProbabilityMeasure ν] {l : Filter ι} {X : ∀ i, Ω i → E} {Y : Ω' → E}
    (h : TendstoInDistribution X l Y μ ν) {F : E → ℝ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    Tendsto (fun i => ∫ ω, F (X i ω) ∂μ i) l (𝓝 (∫ ω, F (Y ω) ∂ν)) := by
  let f : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF M hM
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto f
  change Tendsto (fun i => ∫ x, f x ∂(μ i).map (X i)) l
    (𝓝 (∫ x, f x ∂ν.map Y)) at hh
  simp_rw [integral_map (h.forall_aemeasurable _) f.continuous.aestronglyMeasurable,
    integral_map h.aemeasurable_limit f.continuous.aestronglyMeasurable] at hh
  exact hh

theorem soft_weighted_tendsto
    {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ∀ i, Measure (Ω i)} {ν : Measure Ω'} [∀ i, IsProbabilityMeasure (μ i)]
    [IsProbabilityMeasure ν] {l : Filter ι} {X : ∀ i, Ω i → E} {Y : Ω' → E}
    (h : TendstoInDistribution X l Y μ ν) {F g : E → ℝ}
    (hF : Continuous F) (hg : Continuous g) {M ε : ℝ}
    (hM : ∀ x, |F x| ≤ M) (hε : 0 < ε)
    (hD : 0 < ∫ ω, softCutoff ε (g (Y ω)) ∂ν) :
    Tendsto (fun i => (∫ ω, F (X i ω)*softCutoff ε (g (X i ω)) ∂μ i) /
      (∫ ω, softCutoff ε (g (X i ω)) ∂μ i)) l
      (𝓝 ((∫ ω, F (Y ω)*softCutoff ε (g (Y ω)) ∂ν) /
        (∫ ω, softCutoff ε (g (Y ω)) ∂ν))) := by
  apply Tendsto.div _ _ hD.ne'
  · apply integral_tendsto_of_tendstoInDistribution h (hF.mul ((softCutoff_continuous ε).comp hg)) (M := M)
    intro x
    change |F x * softCutoff ε (g x)| ≤ M
    rw [abs_mul,abs_of_nonneg (softCutoff_nonneg ε _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (softCutoff_le_one hε _)).trans (hM x)
  · exact integral_tendsto_of_tendstoInDistribution h ((softCutoff_continuous ε).comp hg) (M := 1)
      (fun x => by change |softCutoff ε (g x)| ≤ 1; rw [abs_of_nonneg (softCutoff_nonneg ε _)]; exact softCutoff_le_one hε _)

lemma tendsto_of_soft_windows {A : ℕ → ℝ} {S : ℝ → ℕ → ℝ} {b : ℝ} {T : ℝ → ℝ}
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hd : ∀ ε > 0, ∀ δ > 0, ∀ᶠ n in atTop, |A n-S ε n| ≤ C*ε+δ)
    (hs : ∀ ε > 0, Tendsto (S ε) atTop (𝓝 (T ε)))
    (ht : ∀ ε > 0, |T ε-b| ≤ D*ε) : Tendsto A atTop (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  let ε := η/(4*(C+D+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbound : (C+D)*ε ≤ η/4 := by
    dsimp [ε]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 4*(C+D+1))]
    nlinarith
  have hmid := (Metric.tendsto_nhds.mp (hs ε hε)) (η/4) (by positivity)
  filter_upwards [hd ε hε (η/4) (by positivity),hmid] with n hn hm
  rw [Real.dist_eq] at hm ⊢
  have h₁ := abs_sub_le (A n) (S ε n) b
  have h₂ := abs_sub_le (S ε n) (T ε) b
  have h₃ := ht ε hε
  nlinarith

lemma CriticalEvenOffspring.iid_endpoint_positive (p : CriticalEvenOffspring) (n : ℕ) :
    0 < (p.iidLaw (2*n+1)).real {d | totalStep d = -1} := by
  have hlen : 2*n+1 = n+(n+1) := by omega
  rw [hlen]
  let d : Fin (n+(n+1)) → ℕ := (iidSplit n (n+1)).symm (fun _ => 2,fun _ => 0)
  have hd : iidSplit n (n+1) d = (fun _ => 2,fun _ => 0) :=
    (iidSplit n (n+1)).apply_symm_apply _
  have htotal : totalStep d = -1 := by
    rw [totalStep_split,hd]
    simp [totalStep]
  have hval (i : Fin (n+(n+1))) : d i=2 ∨ d i=0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl (congrFun (congrArg Prod.fst hd) j)
    · exact Or.inr (congrFun (congrArg Prod.snd hd) j)
  have hsing : 0 < (p.iidLaw (n+(n+1))) {d} := by
    rw [iidLaw,Measure.pi_singleton]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply ne_of_gt
    rw [p.law_singleton,ENNReal.ofReal_pos]
    rcases hval i with h|h
    · simpa only [h] using p.two_pos
    · simpa only [h] using p.zero_pos
  have hpos : 0 < (p.iidLaw (n+(n+1))) {d | totalStep d = -1} := by
    apply hsing.trans_le
    exact measure_mono (Set.singleton_subset_iff.mpr htotal)
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

def CriticalEvenOffspring.iidBridgeLaw (p : CriticalEvenOffspring) (n : ℕ) :
    Measure (Fin (2*n+1) → ℕ) := cond (p.iidLaw (2*n+1)) {d | totalStep d = -1}

instance (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.iidBridgeLaw n) := by
  apply cond_isProbabilityMeasure
  exact fun h => (p.iid_endpoint_positive n).ne' (by simp [measureReal_def,h])

def CriticalEvenOffspring.bridgeConstant (p : CriticalEvenOffspring) : ℝ :=
  Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)

lemma CriticalEvenOffspring.bridgeConstant_pos (p : CriticalEvenOffspring) :
    0 < p.bridgeConstant := div_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
      (mul_pos p.sigma_pos Real.pi_pos)

lemma CriticalEvenOffspring.iid_endpoint_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => Real.sqrt ((2*n+1:ℕ):ℝ) *
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1}) atTop (𝓝 p.bridgeConstant) := by
  obtain ⟨E,hE,hEt,hb⟩ := p.uniform_local_limit
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h2 : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hden : Tendsto (fun n : ℕ => p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)).const_mul_atTop p.sigma_pos
  have hx : Tendsto (fun n : ℕ => (-1:ℝ)/(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have harg : Tendsto (fun n : ℕ => -((-1:ℝ)/(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)))^2/2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),neg_zero,zero_div] using (hx.pow 2).neg.div_const 2
  have hp := ((Real.continuous_exp.tendsto 0).comp harg).const_mul p.bridgeConstant
  rw [Real.exp_zero,mul_one] at hp
  let A : ℕ → ℝ := fun n => Real.sqrt ((2*n+1:ℕ):ℝ) *
    (p.iidLaw (2*n+1)).real {d | totalStep d = -1}
  let G : ℕ → ℝ := fun n => p.bridgeConstant *
    Real.exp (-((-1:ℝ)/(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)))^2/2)
  have herr : ∀ n, |A n-G n| ≤ E (2*n) := by
    intro n
    have hpar : Even (((2*n+1:ℕ):ℤ)+(-1)) := by
      refine ⟨(n:ℤ),?_⟩
      push_cast
      ring
    have hh := hb (2*n) (-1) hpar
    simpa only [A,G,bridgeConstant,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      Int.cast_neg,Int.cast_one] using hh
  have he : Tendsto (fun n => A n-G n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero (fun _ => abs_nonneg _) herr (hEt.comp h2)
  have hadd := he.add (show Tendsto G atTop (𝓝 p.bridgeConstant) from hp)
  simpa only [sub_add_cancel,zero_add] using hadd

lemma bridge_soft_numeric {M E B σ S T P K ε : ℝ}
    (hM : 0 ≤ M) (hE : 0 ≤ E) (hB : 0 < B) (hσ : 0 < σ)
    (hS : 0 < S) (hT : 0 < T) (hK : 0 < K) (hε : 0 ≤ ε)
    (hden : B/2 ≤ S*P) (hratio : S ≤ K*T) :
    2*M*((2*E+B*(1+ε*(σ*S))/(σ*T))/T)/P ≤
      (4*M*K/B)*(2*E+(B/σ)/T)+4*M*K^2*ε := by
  have hP : 0 < P := (mul_pos_iff_of_pos_left hS).mp ((half_pos hB).trans_le hden)
  have hTP : 0 < T*P := mul_pos hT hP
  have hi : 1/(T*P) ≤ 2*K/B := by
    rw [div_le_div_iff₀ hTP hB]
    have hh := mul_le_mul_of_nonneg_right hratio hP.le
    nlinarith
  have hn : 2*E+B*(1+ε*(σ*S))/(σ*T) ≤ 2*E+(B/σ)/T+B*ε*K := by
    have hh : S/T ≤ K := (div_le_iff₀ hT).mpr hratio
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hB.le hε)
    have he : B*(1+ε*(σ*S))/(σ*T) = (B/σ)/T+B*ε*(S/T) := by
      field_simp
    rw [he]
    linarith
  have hn0 : 0 ≤ 2*E+B*(1+ε*(σ*S))/(σ*T) := by positivity
  calc
    _ = (2*M)*(2*E+B*(1+ε*(σ*S))/(σ*T))*(1/(T*P)) := by ring
    _ ≤ (2*M)*(2*E+B*(1+ε*(σ*S))/(σ*T))*(2*K/B) :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg (by positivity) hn0)
    _ ≤ (2*M)*(2*E+(B/σ)/T+B*ε*K)*(2*K/B) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) (by positivity)
    _ = _ := by field_simp [hB.ne']; ring

lemma exists_bridge_cutoff (t : unitInterval) (ht : (t:ℝ) < 1) :
    ∃ k : ℕ, 2 ≤ k ∧ (k:ℝ)*(t:ℝ) ≤ (k:ℝ)-1 := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
  let k := n+2
  have hk : 2 ≤ k := by omega
  have hnk : 1/(k:ℝ) ≤ 1/((n:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [k]
    push_cast
    linarith
  have hh : 1/(k:ℝ) < 1-(t:ℝ) := hnk.trans_lt hn
  have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hx := (div_lt_iff₀ hkr).mp hh
  refine ⟨k,hk,?_⟩
  nlinarith

lemma bridge_split_parameters {t : unitInterval} {k N : ℕ}
    (hk : 2 ≤ k) (ht : (k:ℝ)*(t:ℝ) ≤ (k:ℝ)-1) (hN : k ≤ N) :
    (N-N/k)+(N/k-1+1)=N ∧
      (N:ℝ)*(t:ℝ) ≤ (N-N/k:ℕ) ∧
      Real.sqrt (N:ℝ) ≤ (k:ℝ)*Real.sqrt ((N/k-1+1:ℕ):ℝ) := by
  have hk0 : 0 < k := by omega
  have hkr : 0 < (k:ℝ) := by positivity
  have hq : 1 ≤ N/k := (Nat.le_div_iff_mul_le hk0).mpr (by simpa using hN)
  have hqN : N/k ≤ N := Nat.div_le_self N k
  have hqr : N/k-1+1=N/k := by omega
  refine ⟨by omega,?_,?_⟩
  · have hmul : (k:ℝ)*((N/k:ℕ):ℝ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N k
    have htN := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N (α := ℝ))
    have hm : ((N-N/k:ℕ):ℝ) = (N:ℝ)-((N/k:ℕ):ℝ) := Nat.cast_sub hqN
    rw [hm]
    nlinarith
  · rw [hqr]
    have hlt : N < k*(N/k+1) := by
      have hh := Nat.mod_lt N hk0
      have he := Nat.mod_add_div N k
      nlinarith
    have hh : N ≤ 2*k*(N/k) := by nlinarith
    have hNR : (N:ℝ) ≤ 2*(k:ℝ)*((N/k:ℕ):ℝ) := by exact_mod_cast hh
    have hkr2 : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hq0 : (0:ℝ) ≤ ((N/k:ℕ):ℝ) := by positivity
    have hsq := Real.sq_sqrt (Nat.cast_nonneg N (α := ℝ))
    have hsq' := Real.sq_sqrt hq0
    have hKsq : (2*(k:ℝ)) ≤ (k:ℝ)^2 := by nlinarith
    have hNN := hNR.trans (mul_le_mul_of_nonneg_right hKsq hq0)
    have hpos : 0 ≤ (k:ℝ)*Real.sqrt ((N/k:ℕ):ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg (N:ℝ)]

lemma bridge_suffix_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => (2*n+1)/k-1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (k*(b+2))] with n hn
  have hq : b+2 ≤ (2*n+1)/k := (Nat.le_div_iff_mul_le hk).mpr (by nlinarith)
  omega

theorem CriticalEvenOffspring.stopped_soft_error (p : CriticalEvenOffspring)
    (t : unitInterval) (ht : (t:ℝ)<1) {F : C(unitInterval,ℝ) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ f, |F f| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε > 0, ∀ δ > 0, ∀ᶠ n in atTop,
      |(∫ d, F (stopPath t (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n) -
        (∫ d, F (stopPath t (p.iidWalk (2*n+1) d))*
          softCutoff ε (p.iidWalk (2*n+1) d 1) ∂p.iidLaw (2*n+1)) /
        (∫ d, softCutoff ε (p.iidWalk (2*n+1) d 1) ∂p.iidLaw (2*n+1))| ≤ C*ε+δ := by
  obtain ⟨k,hk,hkt⟩ := exists_bridge_cutoff t ht
  obtain ⟨E,hE,hEt,hb⟩ := p.prefix_soft_bound
  let r : ℕ → ℕ := fun n => (2*n+1)/k-1
  have hr : Tendsto r atTop atTop := bridge_suffix_tendsto (by omega)
  have hT : Tendsto (fun n => Real.sqrt ((r n+1:ℕ):ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1 |>.comp hr))
  have hres : Tendsto (fun n => (4*M*(k:ℝ)/p.bridgeConstant)*
      (2*E (r n)+(p.bridgeConstant/p.sigma)/Real.sqrt ((r n+1:ℕ):ℝ))) atTop (𝓝 0) := by
    have hh := ((hEt.comp hr).const_mul 2).add
      (hT.const_div_atTop (p.bridgeConstant/p.sigma))
    simpa only [mul_zero,add_zero,Function.comp_apply] using hh.const_mul (4*M*(k:ℝ)/p.bridgeConstant)
  refine ⟨4*M*(k:ℝ)^2,by positivity,?_⟩
  intro ε hε δ hδ
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp;omega) tendsto_id
  have hscale : Tendsto (fun n : ℕ => ε*(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ))) atTop atTop :=
    ((Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)).const_mul_atTop
      p.sigma_pos).const_mul_atTop hε
  have hden := p.iid_endpoint_limit.eventually (eventually_ge_nhds
    (show p.bridgeConstant/2 < p.bridgeConstant by linarith [p.bridgeConstant_pos]))
  have hsmall := hres.eventually (eventually_lt_nhds hδ)
  filter_upwards [hN.eventually (eventually_ge_atTop k),hscale.eventually (eventually_gt_atTop 1),
    hden,hsmall] with n hn hw hp he
  let m := (2*n+1)-(2*n+1)/k
  obtain ⟨hlen,htm,hratio⟩ := bridge_split_parameters hk hkt hn
  change m+(r n+1)=2*n+1 at hlen
  change ((2*n+1:ℕ):ℝ)*(t:ℝ) ≤ m at htm
  change Real.sqrt ((2*n+1:ℕ):ℝ) ≤ (k:ℝ)*Real.sqrt ((r n+1:ℕ):ℝ) at hratio
  have htm' : ((m+(r n+1):ℕ):ℝ)*(t:ℝ) ≤ m := by simpa only [hlen] using htm
  have hpar : Even (((m+(r n+1):ℕ):ℤ)-1) := by
    rw [hlen]
    refine ⟨(n:ℤ),?_⟩
    push_cast
    ring
  have hw' : 1 < ε*(p.sigma*Real.sqrt (m+(r n+1))) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (show 1 < ε*(p.sigma*Real.sqrt ((m+(r n+1):ℕ):ℝ)) from hlen ▸ hw)
  have hp' : 0 < (p.iidLaw (m+(r n+1))).real {d | totalStep d = -1} := by
    rw [hlen]
    exact p.iid_endpoint_positive n
  have hh := hb m (r n) ε hε hpar hw' hp'
    (fun a => F (p.prefixWalk m (r n+1) t a)) M hM (fun a => hF _)
  simp_rw [p.prefixWalk_eq m (r n+1) htm'] at hh
  have hcast : (m:ℝ)+((r n:ℝ)+1)=((2*n+1:ℕ):ℝ) := by exact_mod_cast hlen
  rw [hcast] at hh
  rw [hlen] at hh
  simp_rw [← p.iidWalk_endpoint (by omega : 0 < 2*n+1)] at hh
  have hcast' : (r n:ℝ)+1=((r n+1:ℕ):ℝ) := by norm_cast
  rw [hcast'] at hh
  change |_ - _| ≤ 2*M*((2*E (r n)+p.bridgeConstant*
    (1+ε*(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)))/
      (p.sigma*Real.sqrt ((r n+1:ℕ):ℝ)))/Real.sqrt ((r n+1:ℕ):ℝ)) /
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1} at hh
  apply hh.trans
  have hnumb := bridge_soft_numeric hM (hE (r n)) p.bridgeConstant_pos p.sigma_pos
    (Real.sqrt_pos.mpr (by positivity : 0 < ((2*n+1:ℕ):ℝ)))
    (Real.sqrt_pos.mpr (by positivity : 0 < ((r n+1:ℕ):ℝ)))
    (by exact_mod_cast (show 0 < k by omega)) hε.le hp hratio
  exact hnumb.trans (by linarith)

theorem CriticalEvenOffspring.stopped_bridge_integral_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν)
    (t : unitInterval) (ht : (t:ℝ)<1) {F : C(unitInterval,ℝ) → ℝ}
    {M : ℝ} {L : ℝ≥0} (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d, F (stopPath t (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n)
      atTop (𝓝 (∫ ω, F (stopPath t (bridgePath B ω)) ∂ν)) := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  obtain ⟨C,hC,he⟩ := p.stopped_soft_error t ht hM hFM
  let G : C(unitInterval,ℝ) → ℝ := F ∘ stopPath t
  have hG : LipschitzWith L G := by
    simpa only [mul_one] using hF.comp (stopPath_lipschitz t)
  have hGM : ∀ f, |G f| ≤ M := fun f => hFM _
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp;omega) tendsto_id
  have hclt := p.iidWalk_CLT hB
  have hodd : TendstoInDistribution (fun n => p.iidWalk (2*n+1)) atTop
      (brownianPath B) (fun n => p.iidLaw (2*n+1)) ν :=
    ⟨fun n => hclt.forall_aemeasurable (2*n+1),hclt.aemeasurable_limit,hclt.tendsto.comp hN⟩
  have hep : (fun ω => brownianPath B ω 1) =ᵐ[ν] (fun ω => B 1 ω) := by
    filter_upwards [brownianPath_ae_eq hB] with ω hω
    exact hω 1
  have hden (ε : ℝ) : (∫ ω, softCutoff ε (brownianPath B ω 1) ∂ν) =
      ∫ ω, softCutoff ε (B 1 ω) ∂ν :=
    integral_congr_ae (hep.fun_comp (softCutoff ε))
  have hnum (ε : ℝ) : (∫ ω, G (brownianPath B ω)*softCutoff ε (brownianPath B ω 1) ∂ν) =
      ∫ ω, G (brownianPath B ω)*softCutoff ε (B 1 ω) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hep] with ω hω
    rw [hω]
  apply tendsto_of_soft_windows hC L.coe_nonneg he
    (T := fun ε => (∫ ω, G (brownianPath B ω)*softCutoff ε (B 1 ω) ∂ν) /
      (∫ ω, softCutoff ε (B 1 ω) ∂ν))
  · intro ε hε
    have hh := soft_weighted_tendsto hodd hG.continuous
      (show Continuous (fun f : C(unitInterval,ℝ) => f 1) from by fun_prop) hGM hε
      (show 0 < ∫ ω, softCutoff ε (brownianPath B ω 1) ∂ν from by
        rw [hden]; exact brownian_softCutoff_pos hB.toIsPreBrownianReal hε)
    rw [hnum,hden] at hh
    exact hh
  · intro ε hε
    exact brownian_soft_bridge_bound hB hGM hG hε

theorem CriticalEvenOffspring.stopped_bridge_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν)
    (t : unitInterval) (ht : (t:ℝ)<1) :
    TendstoInDistribution (fun n d => stopPath t (p.iidWalk (2*n+1) d)) atTop
      (fun ω => stopPath t (bridgePath B ω)) p.iidBridgeLaw ν := by
  have hX (n : ℕ) : AEMeasurable (fun d => stopPath t (p.iidWalk (2*n+1) d)) (p.iidBridgeLaw n) :=
    ((continuous_stopPath t).measurable.comp (p.iidWalk_measurable _)).aemeasurable
  have hY : AEMeasurable (fun ω => stopPath t (bridgePath B ω)) ν :=
    (continuous_stopPath t).measurable.comp_aemeasurable (bridgePath_aemeasurable hB)
  refine ⟨hX,hY,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ f, F f ∂(p.iidBridgeLaw n).map (fun d => stopPath t (p.iidWalk (2*n+1) d)))
    atTop (𝓝 (∫ f, F f ∂ν.map (fun ω => stopPath t (bridgePath B ω))))
  simp_rw [integral_map (hX _) hL.continuous.aestronglyMeasurable,
    integral_map hY hL.continuous.aestronglyMeasurable]
  apply p.stopped_bridge_integral_limit hB t ht (M := |F 0|+M) (L := L) _ hL
  intro f
  have hh := hM f 0
  rw [Real.dist_eq] at hh
  linarith [abs_sub_abs_le_abs_sub (F f) (F 0)]

lemma hat_reverse (N : ℕ) (i : Fin (N+1)) (t : unitInterval) :
    hat N i.rev.val (unitInterval.symm t) = hat N i.val t := by
  change max 0 (1-|(N:ℝ)*(1-(t:ℝ))-(i.rev.val:ℝ)|) = _
  have hi : i.rev.val=N-i.val := by simp [Fin.val_rev]
  have hile : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  rw [hi,Nat.cast_sub hile]
  have he : (N:ℝ)*(1-(t:ℝ))-((N:ℝ)-i.val) = -((N:ℝ)*(t:ℝ)-i.val) := by ring
  rw [he,abs_neg]
  rfl

lemma interpolation_reverse (N : ℕ) (a : Fin (N+1) → ℝ) (c : ℝ)
    (t : unitInterval) :
    interpolation N (fun i => c-a i.rev) t = c-interpolation N a (unitInterval.symm t) := by
  rw [interpolation_apply,interpolation_apply]
  have hs : (∑ i : Fin (N+1), a i*hat N i.val (unitInterval.symm t)) =
      ∑ i : Fin (N+1), a i.rev*hat N i.val t := by
    rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin (N+1) => a i*hat N i.val (unitInterval.symm t))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.revPerm_apply,hat_reverse]
  rw [hs]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hat_sum,mul_one]

lemma reverse_partial_sum (N : ℕ) (x : Fin N → ℝ) (i : Fin (N+1)) :
    (∑ j : Fin N, if j.val < i.val then x j.rev else 0) =
    (∑ j : Fin N, x j)-(∑ j : Fin N, if j.val < i.rev.val then x j else 0) := by
  rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin N => if j.val < i.val then x j.rev else 0),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply,Fin.rev_rev]
  have hi : i.rev.val=N-i.val := by simp [Fin.val_rev]
  have hj : j.rev.val=N-1-j.val := by simp [Fin.val_rev];omega
  have hb : j.rev.val < i.val ↔ ¬ j.val < i.rev.val := by rw [hi,hj];omega
  by_cases h : j.val < i.rev.val <;> simp only [hb,h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,sub_self,sub_zero]

lemma interpolation_increments_reverse (N : ℕ) (x : Fin N → ℝ) (a : ℝ)
    (t : unitInterval) :
    interpolation N (fun i => (∑ j : Fin N, if j.val < i.val then x j.rev else 0)/a) t =
    (∑ j : Fin N, x j)/a -
      interpolation N (fun i => (∑ j : Fin N, if j.val < i.val then x j else 0)/a)
        (unitInterval.symm t) := by
  simp_rw [reverse_partial_sum,sub_div]
  exact interpolation_reverse N (fun i : Fin (N+1) => (∑ j : Fin N, if j.val < i.val then x j else 0)/a) ((∑ j : Fin N, x j)/a) t

lemma measurePreserving_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {e : Ω → Ω} (he : MeasurePreserving e μ μ) {s : Set Ω}
    (hs : MeasurableSet s) (hes : e ⁻¹' s=s) :
    MeasurePreserving e (cond μ s) (cond μ s) := by
  refine ⟨he.measurable,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply he.measurable hA,cond_apply hs,cond_apply hs]
  congr 1
  calc
    μ (s ∩ e ⁻¹' A) = μ (e ⁻¹' (s ∩ A)) := by rw [Set.preimage_inter,hes]
    _ = μ (s ∩ A) := he.measure_preimage (hs.inter hA).nullMeasurableSet

def reverseArray (N : ℕ) : (Fin N → ℕ) ≃ᵐ (Fin N → ℕ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℕ) Fin.revPerm

lemma reverseArray_apply (N : ℕ) (d : Fin N → ℕ) (i : Fin N) :
    reverseArray N d i = d i.rev := by
  simpa only [Fin.revPerm_apply,Fin.rev_rev,reverseArray] using
    MeasurableEquiv.piCongrLeft_apply_apply Fin.revPerm (β := fun _ : Fin N => ℕ) d i.rev

lemma reverseArray_preserving (μ : Measure ℕ) [SigmaFinite μ] (N : ℕ) :
    MeasurePreserving (reverseArray N) (Measure.pi (fun _ : Fin N => μ))
      (Measure.pi (fun _ : Fin N => μ)) :=
  measurePreserving_piCongrLeft (fun _ : Fin N => μ) Fin.revPerm

lemma reverseArray_sum (N : ℕ) (d : Fin N → ℕ) (f : ℕ → ℤ) :
    (∑ i : Fin N, f (reverseArray N d i)) = ∑ i : Fin N, f (d i) := by
  simpa only [reverseArray_apply,Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm (fun i : Fin N => f (d i))

lemma reverseArray_cond_preserving (μ : Measure ℕ) [SigmaFinite μ] (N : ℕ)
    (f : ℕ → ℤ) (j : ℤ) :
    MeasurePreserving (reverseArray N)
      (cond (Measure.pi (fun _ : Fin N => μ)) {d | (∑ i : Fin N, f (d i))=j})
      (cond (Measure.pi (fun _ : Fin N => μ)) {d | (∑ i : Fin N, f (d i))=j}) := by
  apply measurePreserving_cond (reverseArray_preserving μ N) (by measurability)
  ext d
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,reverseArray_sum]

lemma stopPath_one (f : C(unitInterval,ℝ)) : stopPath 1 f=f := by
  ext s
  rw [stopPath_apply,min_eq_left (show s ≤ (1:unitInterval) from s.property.2)]

lemma stopPath_zero (f : C(unitInterval,ℝ)) : stopPath 0 f=ContinuousMap.const _ (f 0) := by
  ext s
  simp [stopPath_apply]

lemma continuous_stopPath_time (f : C(unitInterval,ℝ)) : Continuous (fun t => stopPath t f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.min continuous_fst)

lemma dist_stop_reverse_le (f g : C(unitInterval,ℝ)) (c : ℝ)
    (hfg : ∀ u, g u=c-f (unitInterval.symm u)) (t : unitInterval) :
    dist f (stopPath t f) ≤ 2*‖stopPath (unitInterval.symm t) g‖ := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro u
  have hval (v : unitInterval) (hv : v ≤ unitInterval.symm t) :
      |g v| ≤ ‖stopPath (unitInterval.symm t) g‖ := by
    have hh := ContinuousMap.norm_coe_le_norm (stopPath (unitInterval.symm t) g) v
    simpa only [stopPath_apply,min_eq_left hv,Real.norm_eq_abs] using hh
  rw [stopPath_apply,Real.dist_eq]
  by_cases hu : u ≤ t
  · simp only [min_eq_left hu,sub_self,abs_zero]
    positivity
  · have htu : t ≤ u := le_of_not_ge hu
    rw [min_eq_right htu]
    have hv := hval (unitInterval.symm u) ((unitInterval.symm_le_symm).mpr htu)
    have ht' := hval (unitInterval.symm t) le_rfl
    have hdiff : f u-f t = g (unitInterval.symm t)-g (unitInterval.symm u) := by
      rw [hfg,hfg,unitInterval.symm_symm,unitInterval.symm_symm]
      ring
    rw [hdiff]
    exact (abs_sub _ _).trans (by linarith)

def earlyTime (j : ℕ) : unitInterval :=
  ⟨1/((j:ℝ)+2),by constructor <;> (try positivity); apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg j (α := ℝ)]⟩

lemma earlyTime_pos (j : ℕ) : (0:ℝ)<earlyTime j := by dsimp [earlyTime];positivity

lemma earlyTime_lt_one (j : ℕ) : (earlyTime j:ℝ)<1 := by
  dsimp [earlyTime]
  apply (div_lt_one (by positivity)).mpr
  linarith [Nat.cast_nonneg j (α := ℝ)]

lemma earlyTime_tendsto : Tendsto earlyTime atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0)
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_div_atTop 1

lemma lateTime_tendsto : Tendsto (fun j => unitInterval.symm (earlyTime j)) atTop (𝓝 1) := by
  simpa only [unitInterval.symm_zero,Function.comp_def] using unitInterval.continuous_symm.tendsto 0 |>.comp earlyTime_tendsto

lemma norm_stop_early_tendsto (f : C(unitInterval,ℝ)) (hf : f 0=0) :
    Tendsto (fun j => ‖stopPath (earlyTime j) f‖) atTop (𝓝 0) := by
  have h := ((continuous_stopPath_time f).tendsto 0 |>.comp earlyTime_tendsto).norm
  simpa only [stopPath_zero,hf,ContinuousMap.const_zero,norm_zero,Function.comp_def] using h

lemma stop_late_tendsto (f : C(unitInterval,ℝ)) :
    Tendsto (fun j => stopPath (unitInterval.symm (earlyTime j)) f) atTop (𝓝 f) := by
  simpa only [stopPath_one,Function.comp_def] using (continuous_stopPath_time f).tendsto 1 |>.comp lateTime_tendsto

def freezeGauge (M : ℝ) (L : ℝ≥0) (f : C(unitInterval,ℝ)) : ℝ :=
  min (2*M) (2*(L:ℝ)*‖f‖)

lemma freezeGauge_continuous (M : ℝ) (L : ℝ≥0) : Continuous (freezeGauge M L) := by
  unfold freezeGauge
  fun_prop

lemma freezeGauge_nonneg {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) (f : C(unitInterval,ℝ)) :
    0 ≤ freezeGauge M L f := by unfold freezeGauge;positivity

lemma freezeGauge_abs_le {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) (f : C(unitInterval,ℝ)) :
    |freezeGauge M L f| ≤ 2*M := by
  rw [abs_of_nonneg (freezeGauge_nonneg hM L f)]
  exact min_le_left _ _

lemma integral_reverse_freeze_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {e : Ω ≃ᵐ Ω}
    (he : MeasurePreserving e μ μ) {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) (c : Ω → ℝ)
    (hrev : ∀ ω u, X (e ω) u=c ω-X ω (unitInterval.symm u))
    {F : C(unitInterval,ℝ) → ℝ} {M : ℝ} {L : ℝ≥0}
    (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) (t : unitInterval) :
    |(∫ ω, F (X ω) ∂μ)-(∫ ω, F (stopPath t (X ω)) ∂μ)| ≤
      ∫ ω, freezeGauge M L (stopPath (unitInterval.symm t) (X ω)) ∂μ := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  have hi (Z : Ω → C(unitInterval,ℝ)) (hZ : AEMeasurable Z μ) : Integrable (fun ω => F (Z ω)) μ :=
    Integrable.of_bound (hF.continuous.measurable.comp_aemeasurable hZ).aestronglyMeasurable M
      (ae_of_all μ (fun ω => hFM _))
  have hstop : AEMeasurable (fun ω => stopPath t (X ω)) μ :=
    (continuous_stopPath t).measurable.comp_aemeasurable hX
  have hg : Integrable (fun ω => freezeGauge M L (stopPath (unitInterval.symm t) (X (e ω)))) μ := by
    apply Integrable.of_bound _ (2*M) (ae_of_all μ (fun ω => freezeGauge_abs_le hM L _))
    exact ((freezeGauge_continuous M L).measurable.comp_aemeasurable
      ((continuous_stopPath _).measurable.comp_aemeasurable
        (hX.comp_quasiMeasurePreserving he.quasiMeasurePreserving))).aestronglyMeasurable
  rw [← integral_sub (hi _ hX) (hi _ hstop)]
  apply (show |∫ ω, F (X ω)-F (stopPath t (X ω)) ∂μ| ≤
    ∫ ω, |F (X ω)-F (stopPath t (X ω))| ∂μ by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => F (X ω)-F (stopPath t (X ω)))).trans
  calc
    _ ≤ ∫ ω, freezeGauge M L (stopPath (unitInterval.symm t) (X (e ω))) ∂μ := by
      apply integral_mono ((hi _ hX).sub (hi _ hstop)).norm hg
      intro ω
      change |F (X ω)-F (stopPath t (X ω))| ≤
        min (2*M) (2*(L:ℝ)*‖stopPath (unitInterval.symm t) (X (e ω))‖)
      apply le_min
      · linarith [abs_sub (F (X ω)) (F (stopPath t (X ω))),hFM (X ω),hFM (stopPath t (X ω))]
      · have hb := dist_stop_reverse_le (X ω) (X (e ω)) (c ω) (hrev ω) t
        have hl := hF.dist_le_mul (X ω) (stopPath t (X ω))
        rw [Real.dist_eq] at hl
        calc
          _ ≤ (L:ℝ)*dist (X ω) (stopPath t (X ω)) := hl
          _ ≤ (L:ℝ)*(2*‖stopPath (unitInterval.symm t) (X (e ω))‖) :=
            mul_le_mul_of_nonneg_left hb L.coe_nonneg
          _ = _ := by ring
    _ = _ := he.integral_comp' (fun ω => freezeGauge M L (stopPath (unitInterval.symm t) (X ω)))

lemma early_gauge_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) (hz : ∀ᵐ ω ∂μ, X ω 0=0) {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) :
    Tendsto (fun j => ∫ ω, freezeGauge M L (stopPath (earlyTime j) (X ω)) ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω => 2*M)
    (F := fun j ω => freezeGauge M L (stopPath (earlyTime j) (X ω))) (f := fun _ => 0)
    (fun j => ((freezeGauge_continuous M L).measurable.comp_aemeasurable
      ((continuous_stopPath _).measurable.comp_aemeasurable hX)).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all μ (fun ω => freezeGauge_abs_le hM L _)) (by
      filter_upwards [hz] with ω hω
      have h := tendsto_const_nhds.min ((norm_stop_early_tendsto (X ω) hω).const_mul (2*(L:ℝ))) (f := fun _ : ℕ => 2*M)
      simpa only [freezeGauge,mul_zero,min_eq_right (by positivity : 0 ≤ 2*M)] using h)
  simpa only [integral_zero] using hh

lemma late_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) {F : C(unitInterval,ℝ) → ℝ} (hF : Continuous F)
    {M : ℝ} (hFM : ∀ f, |F f| ≤ M) :
    Tendsto (fun j => ∫ ω, F (stopPath (unitInterval.symm (earlyTime j)) (X ω)) ∂μ) atTop
      (𝓝 (∫ ω, F (X ω) ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
    (fun j => (hF.measurable.comp_aemeasurable
      ((continuous_stopPath _).measurable.comp_aemeasurable hX)).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all μ (fun ω => hFM _))
    (ae_of_all μ (fun ω => (hF.tendsto (X ω)).comp (stop_late_tendsto (X ω))))

lemma CriticalEvenOffspring.iidWalk_reverse (p : CriticalEvenOffspring) (N : ℕ)
    (d : Fin N → ℕ) (t : unitInterval) :
    p.iidWalk N (reverseArray N d) t =
      (∑ j : Fin N, p.standardStep (d j))/Real.sqrt N-
        p.iidWalk N d (unitInterval.symm t) := by
  unfold iidWalk
  simp_rw [reverseArray_apply]
  exact interpolation_increments_reverse N (fun j => p.standardStep (d j)) (Real.sqrt N) t

lemma CriticalEvenOffspring.bridge_reverse_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseArray (2*n+1)) (p.iidBridgeLaw n) (p.iidBridgeLaw n) :=
  reverseArray_cond_preserving p.law.toMeasure (2*n+1) (fun k => (k:ℤ)-1) (-1)

lemma bridgePath_zero_ae {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    ∀ᵐ ω ∂ν, bridgePath B ω 0=0 := by
  filter_upwards [bridgePath_ae_eq hB,hB.eval_zero_ae_eq_zero] with ω hω hz
  rw [hω]
  change B 0 ω-(0:ℝ)*B 1 ω=0
  simp [hz]

theorem CriticalEvenOffspring.bridge_integral_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν)
    {F : C(unitInterval,ℝ) → ℝ} {M : ℝ} {L : ℝ≥0}
    (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d, F (p.iidWalk (2*n+1) d) ∂p.iidBridgeLaw n) atTop
      (𝓝 (∫ ω, F (bridgePath B ω) ∂ν)) := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  let A : ℕ → ℝ := fun n => ∫ d, F (p.iidWalk (2*n+1) d) ∂p.iidBridgeLaw n
  let S : ℕ → ℕ → ℝ := fun j n => ∫ d,
    F (stopPath (unitInterval.symm (earlyTime j)) (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n
  let b : ℝ := ∫ ω, F (bridgePath B ω) ∂ν
  let a : ℕ → ℝ := fun j => ∫ ω,
    F (stopPath (unitInterval.symm (earlyTime j)) (bridgePath B ω)) ∂ν
  let R : ℕ → ℕ → ℝ := fun j n => ∫ d,
    freezeGauge M L (stopPath (earlyTime j) (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n
  let r : ℕ → ℝ := fun j => ∫ ω,
    freezeGauge M L (stopPath (earlyTime j) (bridgePath B ω)) ∂ν
  have hlate (j : ℕ) : ((unitInterval.symm (earlyTime j):unitInterval):ℝ)<1 := by
    rw [unitInterval.coe_symm_eq]
    linarith [earlyTime_pos j]
  have hS (j : ℕ) : Tendsto (S j) atTop (𝓝 (a j)) :=
    p.stopped_bridge_integral_limit hB _ (hlate j) hFM hF
  have hR (j : ℕ) : Tendsto (R j) atTop (𝓝 (r j)) := by
    exact integral_tendsto_of_tendstoInDistribution (p.stopped_bridge_CLT hB _ (earlyTime_lt_one j))
      (freezeGauge_continuous M L) (freezeGauge_abs_le hM L)
  have hr : Tendsto r atTop (𝓝 0) :=
    early_gauge_integral_tendsto (bridgePath_aemeasurable hB) (bridgePath_zero_ae hB) hM L
  have ha : Tendsto a atTop (𝓝 b) :=
    late_integral_tendsto (bridgePath_aemeasurable hB) hF.continuous hFM
  have he (j n : ℕ) : |A n-S j n| ≤ R j n := by
    have hh := integral_reverse_freeze_bound (p.bridge_reverse_preserving n)
      (p.iidWalk_measurable (2*n+1)).aemeasurable
      (fun d => (∑ i : Fin (2*n+1), p.standardStep (d i))/Real.sqrt ((2*n+1:ℕ):ℝ))
      (p.iidWalk_reverse (2*n+1)) hFM hF (unitInterval.symm (earlyTime j))
    simpa only [unitInterval.symm_symm] using hh
  change Tendsto A atTop (𝓝 b)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j,hj,hja⟩ := ((Metric.tendsto_nhds.mp hr (ε/4) (by positivity)).and
    (Metric.tendsto_nhds.mp ha (ε/4) (by positivity))).exists
  rw [Real.dist_eq,sub_zero] at hj
  rw [Real.dist_eq] at hja
  have hSn := Metric.tendsto_nhds.mp (hS j) (ε/4) (by positivity)
  have hRn := (hR j).eventually (eventually_lt_nhds (show r j < r j+ε/4 by linarith))
  filter_upwards [hSn,hRn] with n hn hnr
  rw [Real.dist_eq] at hn ⊢
  have h₁ := abs_sub_le (A n) (S j n) b
  have h₂ := abs_sub_le (S j n) (a j) b
  have h₃ := he j n
  linarith [le_abs_self (r j)]

theorem CriticalEvenOffspring.iidBridge_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution (fun n => p.iidWalk (2*n+1)) atTop
      (bridgePath B) p.iidBridgeLaw ν := by
  have hX (n : ℕ) : AEMeasurable (p.iidWalk (2*n+1)) (p.iidBridgeLaw n) :=
    (p.iidWalk_measurable _).aemeasurable
  have hY := bridgePath_aemeasurable hB
  refine ⟨hX,hY,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ f, F f ∂(p.iidBridgeLaw n).map (p.iidWalk (2*n+1))) atTop
    (𝓝 (∫ f, F f ∂ν.map (bridgePath B)))
  simp_rw [integral_map (hX _) hL.continuous.aestronglyMeasurable,
    integral_map hY hL.continuous.aestronglyMeasurable]
  apply p.bridge_integral_limit hB (M := |F 0|+M) (L := L) _ hL
  intro f
  have hh := hM f 0
  rw [Real.dist_eq] at hh
  linarith [abs_sub_abs_le_abs_sub (F f) (F 0)]

end FKCRT.TreeCoding
end

end OAI
