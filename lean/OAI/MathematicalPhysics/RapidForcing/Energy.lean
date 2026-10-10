import OAI.MathematicalPhysics.RapidForcing.Flow

namespace OAI

open scoped BigOperators ENNReal Topology NNReal
open Set MeasureTheory
namespace RapidForcing

instance compactSpace_K : CompactSpace K := isCompact_iff_compactSpace.mp K_compact

section CompactLp
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def boxExtension (g : C(K, E)) : Space → E :=
  Function.extend Subtype.val g (fun _ => 0)

omit [NormedSpace ℝ E] in
lemma boxExtension_mem (g : C(K, E)) {x : Space} (hx : x ∈ K) :
    boxExtension g x = g ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply _ _ ⟨x, hx⟩

omit [NormedSpace ℝ E] in
lemma boxExtension_notMem (g : C(K, E)) {x : Space} (hx : x ∉ K) :
    boxExtension g x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

omit [NormedSpace ℝ E] in
lemma boxExtension_measurable (g : C(K, E)) : StronglyMeasurable (boxExtension g) :=
  (MeasurableEmbedding.subtype_coe K_compact.isClosed.measurableSet).stronglyMeasurable_extend
    g.continuous.stronglyMeasurable stronglyMeasurable_const

omit [NormedSpace ℝ E] in
lemma boxExtension_bound (g : C(K, E)) (x : Space) :
    ‖boxExtension g x‖ ≤ K.indicator (fun _ => ‖g‖) x := by
  by_cases hx : x ∈ K
  · rw [boxExtension_mem g hx, Set.indicator_of_mem hx]
    exact g.norm_coe_le_norm _
  · rw [boxExtension_notMem g hx, Set.indicator_of_notMem hx, norm_zero]

omit [NormedSpace ℝ E] in
lemma boxExtension_memLp (g : C(K, E)) : MemLp (boxExtension g) 2 volume :=
  (memLp_indicator_const 2 K_compact.isClosed.measurableSet ‖g‖
    (Or.inr K_compact.measure_ne_top)).mono' (boxExtension_measurable g).aestronglyMeasurable
      (Filter.Eventually.of_forall (boxExtension_bound g))

noncomputable def boxToL2Linear : C(K, E) →ₗ[ℝ] Lp E 2 (volume : Measure Space) where
  toFun g := (boxExtension_memLp g).toLp (boxExtension g)
  map_add' g h := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (boxExtension_memLp (g + h)),
      Lp.coeFn_add ((boxExtension_memLp g).toLp _) ((boxExtension_memLp h).toLp _),
      MemLp.coeFn_toLp (boxExtension_memLp g), MemLp.coeFn_toLp (boxExtension_memLp h)]
      with x hsum hcoe hg hh
    rw [hsum, hcoe, Pi.add_apply, hg, hh]
    by_cases hx : x ∈ K
    · simp only [boxExtension_mem _ hx, ContinuousMap.add_apply]
    · simp only [boxExtension_notMem _ hx, add_zero]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (boxExtension_memLp (c • g)),
      Lp.coeFn_smul c ((boxExtension_memLp g).toLp _),
      MemLp.coeFn_toLp (boxExtension_memLp g)] with x hc hcoe hg
    simp only [RingHom.id_apply]
    rw [hc, hcoe, Pi.smul_apply, hg]
    by_cases hx : x ∈ K
    · simp only [boxExtension_mem _ hx, ContinuousMap.smul_apply]
    · simp only [boxExtension_notMem _ hx, smul_zero]

lemma coe_boxToL2Linear (g : C(K, E)) :
    (boxToL2Linear g : Space → E) =ᵐ[volume] boxExtension g :=
  MemLp.coeFn_toLp (boxExtension_memLp g)

lemma boxToL2Linear_bound (g : C(K, E)) :
    ‖boxToL2Linear g‖ ≤
      ‖indicatorConstLp 2 K_compact.isClosed.measurableSet
        (μ := (volume : Measure Space)) K_compact.measure_ne_top (1 : ℝ)‖ * ‖g‖ := by
  let e : Lp ℝ 2 (volume : Measure Space) :=
    indicatorConstLp 2 K_compact.isClosed.measurableSet K_compact.measure_ne_top 1
  have hbound : ‖boxToL2Linear g‖ ≤ ‖(‖g‖ : ℝ) • e‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [coe_boxToL2Linear g, Lp.coeFn_smul (‖g‖ : ℝ) e,
      (indicatorConstLp_coeFn : (e : Space → ℝ) =ᵐ[volume] K.indicator (fun _ => 1))]
      with x hx hs he
    change e x = _ at he
    rw [hx, hs, Pi.smul_apply, he]
    by_cases hx : x ∈ K
    · simpa [Set.indicator_of_mem hx] using boxExtension_bound g x
    · simp [Set.indicator_of_notMem hx, boxExtension_notMem g hx]
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg g), mul_comm, e] using hbound

noncomputable def boxToL2 : C(K, E) →L[ℝ] Lp E 2 (volume : Measure Space) :=
  boxToL2Linear.mkContinuous _ boxToL2Linear_bound

lemma coe_boxToL2 (g : C(K, E)) :
    (boxToL2 g : Space → E) =ᵐ[volume] boxExtension g := coe_boxToL2Linear g

end CompactLp

lemma hasDerivAt_continuousMap {α E : Type} [TopologicalSpace α] [CompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → C(α, E)} (hg : Continuous g)
    (hfg : ∀ t x, HasDerivAt (fun s => f s x) (g t x) t) (t : ℝ) :
    HasDerivAt f (g t) t := by
  have heq : f = fun t => f 0 + ∫ s in (0 : ℝ)..t, g s := by
    funext t
    ext x
    have hint := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hg.intervalIntegrable (μ := volume) 0 t)
    change f t x = f 0 x + (ContinuousMap.evalCLM ℝ x) (∫ s in (0 : ℝ)..t, g s)
    rw [← hint]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_hs : s ∈ uIcc (0 : ℝ) t) => hfg s x)
      (((ContinuousMap.evalCLM ℝ x).continuous.comp hg).intervalIntegrable (μ := volume) 0 t)
    change f t x = f 0 x + ∫ s in (0 : ℝ)..t, g s x
    rw [h, add_sub_cancel]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (μ := volume) 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add _

section L2Regularity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def boxCurve (v : Field E) (hv : Continuous (Function.uncurry v)) :
    C(ℝ, C(K, E)) :=
  ContinuousMap.curry ⟨fun p : ℝ × K => v p.1 p.2,
    hv.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩

omit [NormedSpace ℝ E] in
@[simp] lemma boxCurve_apply (v : Field E) (hv : Continuous (Function.uncurry v))
    (t : ℝ) (x : K) : boxCurve v hv t x = v t x := rfl

lemma boxToL2_curve_coe {v : Field E} (hv : Continuous (Function.uncurry v))
    (hs : Supported v) {t : ℝ} (ht : 0 ≤ t) :
    (boxToL2 (boxCurve v hv t) : Space → E) =ᵐ[volume] v t := by
  apply (coe_boxToL2 _).trans
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [boxExtension_mem _ hx, boxCurve_apply]
  · rw [boxExtension_notMem _ hx, hs.zero_off ht hx]

lemma l2Continuous_of_continuous_supported {v : Field E}
    (hv : Continuous (Function.uncurry v)) (hs : Supported v) (T : ℝ) :
    L2ContinuousOn v T := by
  refine ⟨fun t => boxToL2 (boxCurve v hv t),
    (boxToL2.continuous.comp (boxCurve v hv).continuous).continuousOn, ?_⟩
  intro t ht
  exact boxToL2_curve_coe hv hs ht.1

lemma spatialMulti_joint_smooth {v : Field E}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (α : MultiIndex) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (spatialMulti α v)) := by
  have h : ∀ (v : Field E), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v) →
      ∀ i n, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ((spatialD i)^[n] v)) := by
    intro v hv i n
    induction n with
    | zero => exact hv
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact spatialD_joint_smooth ih i
  exact h _ (h _ (h _ hv 2 (α 2)) 1 (α 1)) 0 (α 0)

end L2Regularity

lemma l2C1_of_smooth_supported {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v) (T : ℝ) :
    L2C1On v T := by
  let g : Field Space := fun t x => deriv (fun s => v s x) t
  have hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g) := ordinaryTimeD_joint_smooth hv
  have hgs : Supported g := by
    rw [supported_iff_zero_off]
    intro t ht x hx
    rw [show g t x = timeD v t x from (timeD_eq_ordinary hv ht x).symm]
    exact hs.timeD.zero_off ht hx
  refine ⟨fun t => boxToL2 (boxCurve v hv.continuous t),
    fun t => boxToL2 (boxCurve g hg.continuous t),
    (boxToL2.continuous.comp (boxCurve v hv.continuous).continuous).continuousOn,
    (boxToL2.continuous.comp (boxCurve g hg.continuous).continuous).continuousOn,
    fun t ht => boxToL2_curve_coe hv.continuous hs ht.1, ?_, ?_⟩
  · intro t ht
    exact (boxToL2_curve_coe hg.continuous hgs ht.1).trans
      (Filter.Eventually.of_forall (fun x => (timeD_eq_ordinary hv ht.1 x).symm))
  · intro t _ht
    have hdiff : HasDerivAt (boxCurve v hv.continuous)
        (boxCurve g hg.continuous t) t := by
      apply hasDerivAt_continuousMap (boxCurve g hg.continuous).continuous
      intro s x
      change HasDerivAt (fun t => v t (x : Space)) (deriv (fun t => v t (x : Space)) s) s
      exact ((hv.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) s).hasDerivAt
    exact (boxToL2.hasFDerivAt.comp_hasDerivAt t hdiff).hasDerivWithinAt

theorem energyRegularity_of_smooth_supported {u : Field Space} {p : Field ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    (hp : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry p))
    (hsu : Supported u) (hsp : Supported p) : EnergyRegularity u p := by
  intro T _hT
  refine ⟨?_, l2C1_of_smooth_supported hu hsu T, ?_⟩
  · intro α _hα
    exact l2Continuous_of_continuous_supported (spatialMulti_joint_smooth hu α).continuous
      (hsu.spatialMulti α) T
  · intro α _hα
    exact l2Continuous_of_continuous_supported (spatialMulti_joint_smooth hp α).continuous
      (hsp.spatialMulti α) T

theorem addressed_energyClass (M : Machine) (w : M.Input) :
    EnergyClass (addressedVelocity M w) (fun _ _ => 0) := by
  refine ⟨energyRegularity_of_smooth_supported (addressedVelocity_joint_smooth M w)
    contDiff_const (addressedVelocity_supported M w) ?_, ?_⟩
  · simp [Supported]
  · intro T _hT
    obtain ⟨L, C, h⟩ := finite_interval_bounds (addressedVelocity_joint_smooth M w)
      (addressedVelocity_supported M w) T
    exact ⟨(L : ℝ) + C, fun t ht x => add_le_add (h t ht x).1 (h t ht x).2⟩

end RapidForcing

end OAI
