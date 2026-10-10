import OAI.Analysis.HotSpots.BoundaryKernel

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section L2CutoffLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (s : Set X) (hs : MeasurableSet s)

include hs in
lemma extension_memLp (f : Lp ℝ 2 (ν.restrict s)) : MemLp (s.indicator f) 2 ν :=
  (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)

def extension : Lp ℝ 2 (ν.restrict s) →L[ℝ] Lp ℝ 2 ν := by
  let J : Lp ℝ 2 (ν.restrict s) →ₗ[ℝ] Lp ℝ 2 ν :=
    { toFun := fun f => (extension_memLp s hs f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(extension_memLp s hs (f+g)).coeFn_toLp,
          (extension_memLp s hs f).coeFn_toLp, (extension_memLp s hs g).coeFn_toLp,
          Lp.coeFn_add ((extension_memLp s hs f).toLp _) ((extension_memLp s hs g).toLp _),
          ae_imp_of_ae_restrict (Lp.coeFn_add f g)] with x hfg hf hg ha he
        rw [hfg,ha,Pi.add_apply,hf,hg]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx, he hx, Pi.add_apply]
        · simp [indicator_of_notMem hx]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(extension_memLp s hs (c • f)).coeFn_toLp,
          (extension_memLp s hs f).coeFn_toLp,
          Lp.coeFn_smul c ((extension_memLp s hs f).toLp _),
          ae_imp_of_ae_restrict (Lp.coeFn_smul c f)] with x hcf hf hc he
        simp only [RingHom.id_apply]
        rw [hcf,hc,Pi.smul_apply,hf]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx, he hx, Pi.smul_apply]
        · simp [indicator_of_notMem hx] }
  refine J.mkContinuous 1 (fun f => ?_)
  change ‖(extension_memLp s hs f).toLp _‖ ≤ 1 * ‖f‖
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs, one_mul]
  rfl

lemma extension_ae (f : Lp ℝ 2 (ν.restrict s)) :
    extension s hs f =ᵐ[ν] s.indicator f := (extension_memLp s hs f).coeFn_toLp

lemma extension_norm (f : Lp ℝ 2 (ν.restrict s)) : ‖extension s hs f‖ = ‖f‖ := by
  change ‖(extension_memLp s hs f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  rfl

lemma extension_norm_le : ‖extension (ν := ν) s hs‖ ≤ 1 := by
  apply (extension (ν := ν) s hs).opNorm_le_bound (by norm_num)
  intro f
  simp [extension_norm]

def restriction : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 (ν.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (show ν.restrict s ≤ 1 • ν by simpa using Measure.restrict_le_self)

lemma restriction_ae (f : Lp ℝ 2 ν) : restriction s f =ᵐ[ν.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

lemma restriction_norm (f : Lp ℝ 2 ν) : ‖restriction s f‖ ≤ ‖f‖ := by
  change (eLpNorm (restriction s f) 2 (ν.restrict s)).toReal ≤ (eLpNorm f 2 ν).toReal
  rw [eLpNorm_congr_ae (restriction_ae s f)]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)

lemma restriction_norm_le : ‖restriction (ν := ν) s‖ ≤ 1 := by
  apply (restriction (ν := ν) s).opNorm_le_bound (by norm_num)
  intro f
  simpa only [one_mul] using restriction_norm s f

lemma restriction_extension (f : Lp ℝ 2 (ν.restrict s)) :
    restriction s (extension s hs f) = f := by
  apply Lp.ext
  filter_upwards [restriction_ae s (extension s hs f), (extension_ae s hs f).restrict,
    ae_restrict_mem hs] with x hx he hxs
  rw [hx,he,indicator_of_mem hxs]

lemma extension_inner (f : Lp ℝ 2 (ν.restrict s)) (g : Lp ℝ 2 ν) :
    inner ℝ (extension s hs f) g = inner ℝ f (restriction s g) := by
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
  have he : (fun x => g x * extension s hs f x) =ᵐ[ν]
      s.indicator (fun x => g x * f x) := by
    filter_upwards [extension_ae s hs f] with x hx
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  rw [integral_congr_ae he, integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [restriction_ae s g] with x hx
  rw [hx]

lemma extension_eq_adjoint : extension (ν := ν) s hs = (restriction s).adjoint := by
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).2 (extension_inner s hs)

lemma extension_inner_extension (f g : Lp ℝ 2 (ν.restrict s)) :
    inner ℝ (extension s hs f) (extension s hs g) = inner ℝ f g := by
  rw [extension_inner, restriction_extension]

def projection : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν := (extension s hs).comp (restriction s)

lemma projection_ae (f : Lp ℝ 2 ν) : projection s hs f =ᵐ[ν] s.indicator f := by
  filter_upwards [extension_ae s hs (restriction s f),
    ae_imp_of_ae_restrict (restriction_ae s f)] with x hx hr
  change extension s hs (restriction s f) x = _
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [hxs, hr hxs]
  · simp [hxs]

lemma projection_norm (f : Lp ℝ 2 ν) : ‖projection s hs f‖ ≤ ‖f‖ := by
  exact (extension_norm s hs _).le.trans (restriction_norm s f)

lemma projection_norm_le : ‖projection (ν := ν) s hs‖ ≤ 1 := by
  apply (projection (ν := ν) s hs).opNorm_le_bound (by norm_num)
  intro f
  simpa only [one_mul] using projection_norm s hs f

lemma projection_idempotent (f : Lp ℝ 2 ν) :
    projection s hs (projection s hs f) = projection s hs f := by
  exact congrArg (extension s hs) (restriction_extension s hs (restriction s f))

lemma projection_symmetric (f g : Lp ℝ 2 ν) :
    inner ℝ (projection s hs f) g = inner ℝ f (projection s hs g) := by
  change inner ℝ (extension s hs (restriction s f)) g =
    inner ℝ f (extension s hs (restriction s g))
  calc
    _ = inner ℝ (restriction s f) (restriction s g) := extension_inner s hs _ _
    _ = inner ℝ (restriction s g) (restriction s f) := real_inner_comm _ _
    _ = inner ℝ (extension s hs (restriction s g)) f := (extension_inner s hs _ _).symm
    _ = _ := real_inner_comm _ _

end StrictHotSpots.L2Cutoff

end L2CutoffLayer

section CutoffConvergenceLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma projection_tendsto (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hex : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ s n) (f : Lp ℝ 2 ν) :
    Tendsto (fun n => projection (s n) (hs n) f) atTop (𝓝 f) := by
  let hf : ∀ n, MemLp ((s n).indicator f) 2 ν :=
    fun n => (Lp.memLp f).indicator (hs n)
  have ht := L2Limits.tendsto_toLp_of_dominated hf (Lp.memLp f) (Lp.memLp f).norm
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ s n <;> simp [hx])
    (by
      filter_upwards [hex] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn])
  have he (n : ℕ) : projection (s n) (hs n) f = (hf n).toLp _ :=
    Lp.ext ((projection_ae (s n) (hs n) f).trans (hf n).coeFn_toLp.symm)
  simpa only [← he, Lp.toLp_coeFn] using ht

end StrictHotSpots.L2Cutoff
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_strong_tendsto_moving (Q : ℕ → E →L[ℝ] E) (A : E →L[ℝ] E)
    {d : ℝ} (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => Q n (v n)) atTop (𝓝 (A w)) := by
  have hz : Tendsto (fun n => Q n (v n-w)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => d * ‖v n-w‖) atTop (𝓝 0) := by
      simpa using (hv.sub_const w).norm.const_mul d
    apply squeeze_zero_norm' _ hb
    filter_upwards [hQ] with n hn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  simpa only [map_sub, sub_add_cancel, zero_add] using hz.add (hs w)

lemma compression_norm_le (T P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    ‖P.comp (T.comp P)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖P‖ * (‖T‖ * ‖P‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hP
      (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = ‖T‖ := by ring

lemma compression_strong_tendsto (T : E →L[ℝ] E) (P : ℕ → E →L[ℝ] E)
    (hP : ∀ᶠ n in atTop, ‖P n‖ ≤ 1)
    (hs : ∀ v, Tendsto (fun n => P n v) atTop (𝓝 v)) (f : E) :
    Tendsto (fun n => (P n).comp (T.comp (P n)) f) atTop (𝓝 (T f)) := by
  exact bounded_strong_tendsto_moving P (ContinuousLinearMap.id ℝ E) hP hs
    (T.continuous.continuousAt.tendsto.comp (hs f))

end StrictHotSpots.BanachResolvent
end
end CutoffConvergenceLayer

section CutoffOperatorsLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (s : Set X) (hs : MeasurableSet s)

def restrictedOperator (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    Lp ℝ 2 (ν.restrict s) →L[ℝ] Lp ℝ 2 (ν.restrict s) :=
  (restriction s).comp (T.comp (extension s hs))

def compressedOperator (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (projection s hs).comp (T.comp (projection s hs))

lemma restrictedOperator_norm_le (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    ‖restrictedOperator s hs T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖restriction (ν := ν) s‖ * (‖T‖ * ‖extension (ν := ν) s hs‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul (restriction_norm_le s)
      (mul_le_mul_of_nonneg_left (extension_norm_le s hs) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = ‖T‖ := by ring

lemma compressedOperator_norm_le (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    ‖compressedOperator s hs T‖ ≤ ‖T‖ :=
  BanachResolvent.compression_norm_le T (projection s hs) (projection_norm_le s hs)

lemma extension_intertwine (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (f : Lp ℝ 2 (ν.restrict s)) :
    extension s hs (restrictedOperator s hs T f) =
      compressedOperator s hs T (extension s hs f) := by
  change extension s hs (restriction s (T (extension s hs f))) =
    extension s hs (restriction s (T (extension s hs (restriction s (extension s hs f)))))
  rw [restriction_extension]

lemma resolvent_extension (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hT : ‖T‖ < 1)
    (f : Lp ℝ 2 (ν.restrict s)) :
    BanachResolvent.resolvent (compressedOperator s hs T) (extension s hs f) =
      extension s hs (BanachResolvent.resolvent (restrictedOperator s hs T) f) := by
  symm
  apply BanachResolvent.resolvent_solution _ ((compressedOperator_norm_le s hs T).trans_lt hT)
  rw [← extension_intertwine, ← map_sub]
  congr 1
  exact congrArg (fun A : Lp ℝ 2 (ν.restrict s) →L[ℝ] Lp ℝ 2 (ν.restrict s) => A f)
    (BanachResolvent.resolvent_left _ ((restrictedOperator_norm_le s hs T).trans_lt hT))

lemma resolvent_inner_extension (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hT : ‖T‖ < 1)
    (f g : Lp ℝ 2 (ν.restrict s)) :
    inner ℝ (extension s hs f)
      (BanachResolvent.resolvent (compressedOperator s hs T) (extension s hs g)) =
      inner ℝ f (BanachResolvent.resolvent (restrictedOperator s hs T) g) := by
  rw [resolvent_extension s hs T hT, extension_inner_extension]

end StrictHotSpots.L2Cutoff
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk) (s : Set Plane)

include hν in
lemma restrictDensity : ν.restrict s ≤ C • volume.restrict disk :=
  Measure.restrict_le_self.trans hν

lemma inclusion_restrict : inclusion hC (restrictDensity hν s) =
    (L2Cutoff.restriction s).comp (inclusion hC hν) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [inclusion_ae hC (restrictDensity hν s) f,
    L2Cutoff.restriction_ae s (inclusion hC hν f), (inclusion_ae hC hν f).restrict]
    with x hx hr hi
  rw [hx, show ((L2Cutoff.restriction s).comp (inclusion hC hν)) f x = f x from hr.trans hi]

lemma weightedIntegralOperator_restrict (hs : MeasurableSet s) :
    weightedIntegralOperator hC (restrictDensity hν s) =
      L2Cutoff.restrictedOperator s hs (weightedIntegralOperator hC hν) := by
  unfold weightedIntegralOperator L2Cutoff.restrictedOperator
  rw [inclusion_restrict hC hν s, ContinuousLinearMap.adjoint_comp, L2Cutoff.extension_eq_adjoint]
  simp only [ContinuousLinearMap.comp_assoc]

lemma weightedValue_restrict (u : H10 diskOpen) :
    H10.weightedValue diskOpen hC (restrictDensity hν s) u =
      L2Cutoff.restriction s (H10.weightedValue diskOpen hC hν u) := by
  exact congrArg (fun T => T (H10.value diskOpen u)) (inclusion_restrict hC hν s)

lemma subcritical_restrict {d : ℝ}
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) :
    ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC (restrictDensity hν s) u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2 := by
  intro u
  rw [weightedValue_restrict hC hν s]
  exact (pow_le_pow_left₀ (norm_nonneg _) (L2Cutoff.restriction_norm s _) 2).trans (hsub u)

lemma row_restrict (p : disk) : row hC (restrictDensity hν s) p =
    L2Cutoff.restriction s (row hC hν p) := by
  apply Lp.ext
  exact (column_memLp hC (restrictDensity hν s) p).coeFn_toLp.trans
    (((L2Cutoff.restriction_ae s (row hC hν p)).trans
      (column_memLp hC hν p).coeFn_toLp.restrict).symm)

end StrictHotSpots.PlaneGreen
end
end CutoffOperatorsLayer

section DiskCutoffLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def cutoffRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)
def cutoffSet (n : ℕ) : Set Plane := closedBall 0 (cutoffRadius n)

lemma cutoffRadius_nonneg (n : ℕ) : 0 ≤ cutoffRadius n := by
  unfold cutoffRadius
  have hn : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hh : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 hn
  linarith

lemma cutoffRadius_lt_one (n : ℕ) : cutoffRadius n < 1 := by
  unfold cutoffRadius
  exact sub_lt_self _ (one_div_pos.mpr (by positivity))

lemma cutoffRadius_tendsto : Tendsto cutoffRadius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1)
  simpa only [sub_zero] using
    ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

lemma cutoffSet_compact (n : ℕ) : IsCompact (cutoffSet n) := isCompact_closedBall _ _
lemma cutoffSet_measurable (n : ℕ) : MeasurableSet (cutoffSet n) := measurableSet_closedBall
lemma cutoffSet_subset (n : ℕ) : cutoffSet n ⊆ disk := by
  intro x hx
  simpa [disk] using (show ‖x‖ ≤ cutoffRadius n by simpa [cutoffSet] using hx).trans_lt
    (cutoffRadius_lt_one n)

lemma eventually_mem_cutoffSet (x : Plane) (hx : x ∈ disk) :
    ∀ᶠ n in atTop, x ∈ cutoffSet n := by
  have ht := cutoffRadius_tendsto.eventually (eventually_gt_nhds (show ‖x‖ < 1 by simpa [disk] using hx))
  filter_upwards [ht] with n hn
  simpa [cutoffSet] using hn.le

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma ae_eventually_mem_cutoffSet : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ cutoffSet n := by
  filter_upwards [ae_mem_disk hν] with x hx
  exact eventually_mem_cutoffSet x hx

include hν in
lemma cutoffProjection_tendsto (f : Lp ℝ 2 ν) :
    Tendsto (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) f)
      atTop (𝓝 f) :=
  L2Cutoff.projection_tendsto cutoffSet cutoffSet_measurable (ae_eventually_mem_cutoffSet hν) f

include hν in
lemma cutoff_integral_tendsto {f : Plane → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x in cutoffSet n, f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hm : ∀ n, AEStronglyMeasurable ((cutoffSet n).indicator f) ν :=
    fun n => hf.aestronglyMeasurable.indicator (cutoffSet_measurable n)
  have ht := tendsto_integral_filter_of_dominated_convergence (f := f) (fun x => ‖f x‖)
    (Eventually.of_forall hm)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ cutoffSet n <;> simp [hx]) hf.norm
    (by
      filter_upwards [ae_eventually_mem_cutoffSet hν] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn])
  simpa only [integral_indicator (cutoffSet_measurable _)] using ht

include hν in
lemma smoothedPoisson_nonneg (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    0 ≤ smoothedPoisson (ν := ν) s x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with y hy
  exact mul_nonneg (kernel_nonneg hx hy) (poisson_nonneg s ⟨y,hy⟩)

include hC hν in
lemma smoothedPoisson_restrict_le (s : Boundary) (E : Set Plane) {x : Plane} (hx : x ∈ disk) :
    smoothedPoisson (ν := ν.restrict E) s x ≤ smoothedPoisson (ν := ν) s x := by
  apply setIntegral_le_integral (product_green_poisson_integrable hC hν x hx s)
  filter_upwards [ae_mem_disk hν] with y hy
  exact mul_nonneg (kernel_nonneg hx hy) (poisson_nonneg s ⟨y,hy⟩)

include hC hν in
lemma smoothedPoisson_full_memLp [IsFiniteMeasure ν] (s : Boundary) (E : Set Plane) :
    MemLp (smoothedPoisson (ν := ν.restrict E) s) 2 ν := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  apply MemLp.of_bound (smoothedPoisson_measurable s).aestronglyMeasurable B
  filter_upwards [ae_mem_disk hν] with x hx
  rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν E) s hx)]
  exact (smoothedPoisson_restrict_le hC hν s E hx).trans
    (le_abs_self _ |>.trans (hB x hx s))

include hC hν in
lemma smoothedPoisson_cutoff_tendsto (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    Tendsto (fun n => smoothedPoisson (ν := ν.restrict (cutoffSet n)) s x)
      atTop (𝓝 (smoothedPoisson (ν := ν) s x)) :=
  cutoff_integral_tendsto hν (product_green_poisson_integrable hC hν x hx s)

lemma smoothedPoisson_cutoff_L2_tendsto [IsFiniteMeasure ν] (s : Boundary) :
    Tendsto (fun n => (smoothedPoisson_full_memLp hC hν s (cutoffSet n)).toLp
      (smoothedPoisson (ν := ν.restrict (cutoffSet n)) s)) atTop
      (𝓝 ((smoothedPoisson_memLp hC hν s).toLp (smoothedPoisson (ν := ν) s))) := by
  apply L2Limits.tendsto_toLp_of_dominated
    (fun n => smoothedPoisson_full_memLp hC hν s (cutoffSet n))
    (smoothedPoisson_memLp hC hν s) (smoothedPoisson_memLp hC hν s)
  · apply Eventually.of_forall
    intro n
    filter_upwards [ae_mem_disk hν] with x hx
    rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν (cutoffSet n)) s hx)]
    exact smoothedPoisson_restrict_le hC hν s (cutoffSet n) hx
  · filter_upwards [ae_mem_disk hν] with x hx
    exact smoothedPoisson_cutoff_tendsto hC hν s hx

end StrictHotSpots.PlaneGreen
end
end DiskCutoffLayer

section FullBoundaryKernelLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.BanachResolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma apply_eq_add (T : H →L[ℝ] H) (hT : ‖T‖ < 1) (f : H) :
    resolvent T f = f + resolvent T (T f) := by
  have he := congrArg (fun A : H →L[ℝ] H => A f) (resolvent_right T hT)
  have hh : resolvent T f - resolvent T (T f) = f := by
    simpa only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, map_sub] using he
  exact sub_eq_iff_eq_add.mp hh

lemma apply_eq_add_left (T : H →L[ℝ] H) (hT : ‖T‖ < 1) (f : H) :
    resolvent T f = f + T (resolvent T f) := by
  have he := congrArg (fun A : H →L[ℝ] H => A f) (resolvent_left T hT)
  have hh : resolvent T f - T (resolvent T f) = f := by
    simpa only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self] using he
  exact sub_eq_iff_eq_add.mp hh

lemma inner_two_terms (T : H →L[ℝ] H) (hT : ‖T‖ < 1)
    (hsym : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g)) (f g : H) :
    inner ℝ f (resolvent T g) = inner ℝ f g + inner ℝ f (T g) +
      inner ℝ (T f) (resolvent T (T g)) := by
  have h1 := congrArg (fun v => inner ℝ f v) (apply_eq_add T hT g)
  have h2 := congrArg (fun v => inner ℝ f v) (apply_eq_add_left T hT (T g))
  rw [inner_add_right] at h1 h2
  rw [← hsym f (resolvent T (T g))] at h2
  rw [h1, h2]
  ring

end StrictHotSpots.BanachResolvent
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

def smoothedRow (s : Boundary) : Lp ℝ 2 ν :=
  (smoothedPoisson_memLp hC hν s).toLp (smoothedPoisson (ν := ν) s)

def cutoffSmoothedRow (n : ℕ) (s : Boundary) : Lp ℝ 2 ν :=
  (smoothedPoisson_full_memLp hC hν s (cutoffSet n)).toLp
    (smoothedPoisson (ν := ν.restrict (cutoffSet n)) s)

omit [IsFiniteMeasure ν] in
lemma cutoff_ae_norm (n : ℕ) : ∀ᵐ x ∂ν.restrict (cutoffSet n), ‖x‖ ≤ cutoffRadius n := by
  filter_upwards [ae_restrict_mem (cutoffSet_measurable n)] with x hx
  simpa [cutoffSet] using hx

lemma compactSmoothedRow_eq (n : ℕ) (s : Boundary) :
    weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s) =
    L2Cutoff.restriction (cutoffSet n) (cutoffSmoothedRow hC hν n s) := by
  apply Lp.ext
  filter_upwards [weightedIntegralOperator_ae hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s),
    L2Cutoff.restriction_ae (cutoffSet n) (cutoffSmoothedRow hC hν n s),
    ((smoothedPoisson_full_memLp hC hν s (cutoffSet n)).coeFn_toLp).restrict] with x hx hr hs
  rw [hx,hr,show cutoffSmoothedRow hC hν n s x =
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) s x from hs]
  apply integral_congr_ae
  filter_upwards [(poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s).coeFn_toLp]
    with y hy
  rw [show poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s y = poisson s y from hy]

lemma extendedSmoothedRow_tendsto (s : Boundary) :
    Tendsto (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
      (cutoffSmoothedRow hC hν n s)) atTop (𝓝 (smoothedRow hC hν s)) := by
  apply BanachResolvent.bounded_strong_tendsto_moving
    (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n))
    (ContinuousLinearMap.id ℝ (Lp ℝ 2 ν))
    (Eventually.of_forall fun n => L2Cutoff.projection_norm_le _ _)
    (cutoffProjection_tendsto hν)
  exact smoothedPoisson_cutoff_L2_tendsto hC hν s



def fullBoundaryK (p : disk) (s : Boundary) : ℝ := poisson s p + smoothedPoisson (ν := ν) s p +
  inner ℝ (row hC hν p) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (smoothedRow hC hν s))



def fullBoundaryN (s t : Boundary) : ℝ := boundaryInteraction s t +
  (∫ x, poisson s x * poisson t x ∂ν) +
  (∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν) +
  inner ℝ (smoothedRow hC hν s) (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
    (smoothedRow hC hν t))

lemma smoothedRow_nonneg (s : Boundary) : 0 ≤ smoothedRow hC hν s := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
  rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
  exact smoothedPoisson_nonneg hν s hxd

lemma fullBoundaryK_pos (hT : ‖weightedIntegralOperator hC hν‖ < 1) (p : disk) (s : Boundary) :
    0 < fullBoundaryK hC hν p s := by
  apply add_pos_of_pos_of_nonneg
  · exact add_pos_of_pos_of_nonneg (poisson_pos s p) (smoothedPoisson_nonneg hν s p.property)
  · apply L2Limits.inner_nonneg (row_nonneg hC hν p)
    exact BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν)
      (smoothedRow_nonneg hC hν s)

lemma fullBoundaryN_pos (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) (hst : s ≠ t) :
    0 < fullBoundaryN hC hν s t := by
  apply add_pos_of_pos_of_nonneg
  · apply add_pos_of_pos_of_nonneg
    · apply add_pos_of_pos_of_nonneg (boundaryInteraction_pos s t hst)
      apply integral_nonneg_of_ae
      filter_upwards [ae_mem_disk hν] with x hx
      exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩)
    · apply integral_nonneg_of_ae
      filter_upwards [ae_mem_disk hν] with x hx
      exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (smoothedPoisson_nonneg hν t hx)
  · apply L2Limits.inner_nonneg (smoothedRow_nonneg hC hν s)
    exact BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν)
      (smoothedRow_nonneg hC hν t)

end StrictHotSpots.PlaneGreen
end
end FullBoundaryKernelLayer

section PoissonProductsLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma poisson_measurable (s : Boundary) : Measurable (poisson s) := by
  unfold poisson DiskFormula.poisson
  fun_prop

lemma poisson_invnorm_bound (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    poisson s x ≤ Real.pi⁻¹ * ‖(s : Plane)-x‖⁻¹ := by
  have hh := DiskFormula.poisson_invnorm_bound (complexIso.symm s) (complexIso.symm x)
    (by simpa using s.property) (by simpa [disk] using hx)
  simpa only [poisson, ← map_sub, LinearIsometryEquiv.norm_map] using hh

lemma poisson_product_bound (s t : Boundary) (hst : s ≠ t) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ x ∈ disk, poisson s x * poisson t x ≤ A * (poisson s x + poisson t x) := by
  let D : ℝ := ‖(s : Plane)-(t : Plane)‖ / 2
  have hD : 0 < D := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr
    (fun h => hst (Subtype.ext h)))) (by norm_num)
  let A : ℝ := Real.pi⁻¹ * D⁻¹
  refine ⟨A, mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (inv_nonneg.mpr hD.le), fun x hx => ?_⟩
  have hdist : 2*D ≤ ‖(s : Plane)-x‖ + ‖(t : Plane)-x‖ := by
    have hh := norm_add_le ((s : Plane)-x) (x-(t : Plane))
    have he : (s : Plane)-x+(x-(t : Plane)) = (s : Plane)-(t : Plane) := by abel
    rw [he, norm_sub_rev x (t : Plane)] at hh
    dsimp [D]
    linarith
  have hb (v : Boundary) (hv : D ≤ ‖(v : Plane)-x‖) : poisson v x ≤ A := by
    apply (poisson_invnorm_bound v hx).trans
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using one_div_le_one_div_of_le hD hv) (inv_nonneg.mpr Real.pi_pos.le)
  have hs := poisson_nonneg s ⟨x,hx⟩
  have ht := poisson_nonneg t ⟨x,hx⟩
  by_cases hd : D ≤ ‖(s : Plane)-x‖
  · have h1 := mul_le_mul_of_nonneg_right (hb s hd) ht
    have h2 : A * poisson t x ≤ A * (poisson s x + poisson t x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by dsimp [A]; positivity)
    exact h1.trans h2
  · have h1 := mul_le_mul_of_nonneg_left (hb t (by linarith)) hs
    have h2 : poisson s x * A ≤ A * (poisson s x + poisson t x) := by
      have hA : 0 ≤ A := by dsimp [A]; positivity
      nlinarith
    exact h1.trans h2

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma poisson_integrable (s : Boundary) : Integrable (poisson s) ν :=
  (poisson_memLp_three_halves_weighted hC hν s).integrable (by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num)

include hC hν in
lemma poisson_product_integrable (s t : Boundary) (hst : s ≠ t) :
    Integrable (fun x => poisson s x * poisson t x) ν := by
  obtain ⟨A,_,hA⟩ := poisson_product_bound s t hst
  apply (((poisson_integrable hC hν s).add (poisson_integrable hC hν t)).const_mul A).mono'
    ((poisson_measurable s).mul (poisson_measurable t)).aestronglyMeasurable
  filter_upwards [ae_mem_disk hν] with x hx
  change ‖poisson s x * poisson t x‖ ≤ A * (poisson s x + poisson t x)
  rw [Real.norm_of_nonneg (mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩))]
  exact hA x hx

include hC hν in
lemma poisson_smoothed_integrable (s t : Boundary) :
    Integrable (fun x => poisson s x * smoothedPoisson (ν := ν) t x) ν := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  apply ((poisson_integrable hC hν s).norm.mul_const B).mono'
    ((poisson_measurable s).mul (smoothedPoisson_measurable t)).aestronglyMeasurable
  filter_upwards [ae_mem_disk hν] with x hx
  change ‖poisson s x * smoothedPoisson (ν := ν) t x‖ ≤ ‖poisson s x‖ * B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB x hx t) (norm_nonneg _)

include hC hν in
lemma poisson_smoothed_cutoff_tendsto (s t : Boundary) :
    Tendsto (fun n => ∫ x in cutoffSet n, poisson s x *
      smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x ∂ν) atTop
      (𝓝 (∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν)) := by
  obtain ⟨B,_,hB⟩ := green_poisson_uniform_bound hC hν
  let f (n : ℕ) (x : Plane) := (cutoffSet n).indicator (fun x => poisson s x *
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x) x
  have hm n : AEStronglyMeasurable (f n) ν :=
    (((poisson_measurable s).mul (smoothedPoisson_measurable t)).indicator
      (cutoffSet_measurable n)).aestronglyMeasurable
  have hd n : ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖poisson s x‖ * B := by
    filter_upwards [ae_mem_disk hν] with x hx
    by_cases he : x ∈ cutoffSet n
    · dsimp only [f]
      rw [indicator_of_mem he, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν (cutoffSet n)) t hx)]
      exact (smoothedPoisson_restrict_le hC hν t (cutoffSet n) hx).trans
        (le_abs_self _ |>.trans (hB x hx t))
    · simp only [f, indicator_of_notMem he, norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _ |>.trans (hB x hx t))
  have hl : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop
      (𝓝 (poisson s x * smoothedPoisson (ν := ν) t x)) := by
    filter_upwards [ae_mem_disk hν, ae_eventually_mem_cutoffSet hν] with x hx he
    apply ((smoothedPoisson_cutoff_tendsto hC hν t hx).const_mul (poisson s x)).congr'
    filter_upwards [he] with n hn
    simp [f,hn]
  have hh := tendsto_integral_filter_of_dominated_convergence (fun x => ‖poisson s x‖ * B)
    (Eventually.of_forall hm) (Eventually.of_forall hd)
    ((poisson_integrable hC hν s).norm.mul_const B) hl
  simpa only [f, integral_indicator (cutoffSet_measurable _)] using hh

end StrictHotSpots.PlaneGreen
end
end PoissonProductsLayer

section CutoffBoundaryLimitsLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

abbrev cutoffOperator (n : ℕ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  L2Cutoff.compressedOperator (cutoffSet n) (cutoffSet_measurable n) (weightedIntegralOperator hC hν)

abbrev cutoffK (n : ℕ) (p : disk) (s : Boundary) : ℝ :=
  boundaryK (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) hC
    (restrictDensity hν (cutoffSet n)) p s

abbrev cutoffN (n : ℕ) (s t : Boundary) : ℝ :=
  boundaryN (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) hC
    (restrictDensity hν (cutoffSet n)) s t

lemma cutoff_row_inner (n : ℕ) (p : disk) (s : Boundary) :
    inner ℝ (row hC (restrictDensity hν (cutoffSet n)) p)
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s) =
      smoothedPoisson (ν := ν.restrict (cutoffSet n)) s p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(column_memLp hC (restrictDensity hν (cutoffSet n)) p).coeFn_toLp,
    (poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s).coeFn_toLp] with x hx hs
  change poissonRow _ _ s x * row hC _ p x = _
  rw [show row hC (restrictDensity hν (cutoffSet n)) p x = kernel x p from hx,
    show poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s x = poisson s x from hs,
    kernel_symm, mul_comm]

lemma cutoff_poisson_inner (n : ℕ) (s t : Boundary) :
    inner ℝ (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t) =
      ∫ x in cutoffSet n, poisson s x * poisson t x ∂ν :=
  (MeasurableL2Kernel.integral_mul_eq_inner
    (poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)
    (poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t)).symm

lemma cutoff_poisson_smoothed_inner (n : ℕ) (s t : Boundary) :
    inner ℝ (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)
      (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
        (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t)) =
      ∫ x in cutoffSet n, poisson s x *
        smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x ∂ν := by
  rw [compactSmoothedRow_eq hC hν, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s).coeFn_toLp,
    L2Cutoff.restriction_ae (cutoffSet n) (cutoffSmoothedRow hC hν n t),
    ((smoothedPoisson_full_memLp hC hν t (cutoffSet n)).coeFn_toLp).restrict] with x hs hr ht
  change L2Cutoff.restriction (cutoffSet n) (cutoffSmoothedRow hC hν n t) x *
    poissonRow _ _ s x = _
  rw [hr,show cutoffSmoothedRow hC hν n t x =
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x from ht,
    show poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s x = poisson s x from hs,
    mul_comm]

lemma cutoffK_expansion (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (n : ℕ) (p : disk) (s : Boundary) :
    cutoffK hC hν n p s = poisson s p + smoothedPoisson (ν := ν.restrict (cutoffSet n)) s p +
      inner ℝ (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (row hC hν p))
        (BanachResolvent.resolvent (cutoffOperator hC hν n)
          (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s))) := by
  have hn : ‖weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))‖ < 1 := by
    rw [weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)]
    exact (L2Cutoff.restrictedOperator_norm_le _ _ _).trans_lt hT
  have he := L2Cutoff.resolvent_inner_extension (cutoffSet n) (cutoffSet_measurable n)
    (weightedIntegralOperator hC hν) hT (row hC (restrictDensity hν (cutoffSet n)) p)
    (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s))
  rw [← weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)] at he
  rw [row_restrict hC hν, compactSmoothedRow_eq hC hν] at he
  change inner ℝ (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (row hC hν p))
    (BanachResolvent.resolvent (cutoffOperator hC hν n)
      (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s))) = _ at he
  unfold cutoffK boundaryK
  rw [BanachResolvent.apply_eq_add _ hn, inner_add_right, cutoff_row_inner hC hν]
  rw [compactSmoothedRow_eq hC hν, row_restrict hC hν]
  rw [← he]
  ring

lemma cutoffN_expansion (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (n : ℕ) (s t : Boundary) :
    cutoffN hC hν n s t = boundaryInteraction s t +
      (∫ x in cutoffSet n, poisson s x * poisson t x ∂ν) +
      (∫ x in cutoffSet n, poisson s x * smoothedPoisson (ν := ν.restrict (cutoffSet n)) t x ∂ν) +
      inner ℝ (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s))
        (BanachResolvent.resolvent (cutoffOperator hC hν n)
          (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n t))) := by
  have hn : ‖weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))‖ < 1 := by
    rw [weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)]
    exact (L2Cutoff.restrictedOperator_norm_le _ _ _).trans_lt hT
  have he := L2Cutoff.resolvent_inner_extension (cutoffSet n) (cutoffSet_measurable n)
    (weightedIntegralOperator hC hν) hT
    (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s))
    (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) t))
  rw [← weightedIntegralOperator_restrict hC hν _ (cutoffSet_measurable n)] at he
  simp only [compactSmoothedRow_eq hC hν] at he
  change inner ℝ (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s))
    (BanachResolvent.resolvent (cutoffOperator hC hν n)
      (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n t))) = _ at he
  unfold cutoffN boundaryN
  rw [BanachResolvent.inner_two_terms _ hn (weightedIntegralOperator_symmetric hC _),
    cutoff_poisson_inner, cutoff_poisson_smoothed_inner hC hν]
  simp only [compactSmoothedRow_eq hC hν]
  rw [← he]
  ring

omit [IsFiniteMeasure ν] in
lemma cutoffOperator_strong_tendsto (f : Lp ℝ 2 ν) :
    Tendsto (fun n => cutoffOperator hC hν n f) atTop (𝓝 (weightedIntegralOperator hC hν f)) :=
  BanachResolvent.compression_strong_tendsto _ _
    (Eventually.of_forall fun n => L2Cutoff.projection_norm_le (cutoffSet n) (cutoffSet_measurable n)) (cutoffProjection_tendsto hν) f

lemma cutoff_resolvent_smoothed_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s : Boundary) :
    Tendsto (fun n => BanachResolvent.resolvent (cutoffOperator hC hν n)
      (L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) (cutoffSmoothedRow hC hν n s)))
      atTop (𝓝 (BanachResolvent.resolvent (weightedIntegralOperator hC hν) (smoothedRow hC hν s))) := by
  apply BanachResolvent.resolvent_strong_tendsto_moving _ _ hT hT
    (Eventually.of_forall fun n => L2Cutoff.compressedOperator_norm_le _ _ _)
    (cutoffOperator_strong_tendsto hC hν)
  exact extendedSmoothedRow_tendsto hC hν s

lemma cutoffK_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1) (p : disk) (s : Boundary) :
    Tendsto (fun n => cutoffK hC hν n p s) atTop (𝓝 (fullBoundaryK hC hν p s)) := by
  have ht := ((tendsto_const_nhds (x := poisson s p)).add
    (smoothedPoisson_cutoff_tendsto hC hν s p.property)).add
    ((cutoffProjection_tendsto hν (row hC hν p)).inner
      (cutoff_resolvent_smoothed_tendsto hC hν hT s))
  simpa only [cutoffK_expansion hC hν hT, fullBoundaryK] using ht

lemma cutoffN_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) (hst : s ≠ t) :
    Tendsto (fun n => cutoffN hC hν n s t) atTop (𝓝 (fullBoundaryN hC hν s t)) := by
  have ht := (((tendsto_const_nhds (x := boundaryInteraction s t)).add
    (cutoff_integral_tendsto hν (poisson_product_integrable hC hν s t hst))).add
    (poisson_smoothed_cutoff_tendsto hC hν s t)).add
    ((extendedSmoothedRow_tendsto hC hν s).inner (cutoff_resolvent_smoothed_tendsto hC hν hT t))
  simpa only [cutoffN_expansion hC hν hT, fullBoundaryN] using ht

end StrictHotSpots.PlaneGreen
end
end CutoffBoundaryLimitsLayer

section FullBoundaryReciprocalLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)



theorem boundary_reciprocal {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk)
    {ι : Type} [Fintype ι] (s : ι → Boundary) :
    ReciprocalKernel.OnePositiveSquare (ReciprocalKernel.bordered
      (Matrix.of fun i j => if s i = s j then 0 else (fullBoundaryN hC hν (s i) (s j))⁻¹)
      (fun i => (fullBoundaryK hC hν p (s i))⁻¹)) := by
  classical
  have hn : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  let A (n : ℕ) := ReciprocalKernel.bordered
    (Matrix.of fun i j => if s i = s j then 0 else (cutoffN hC hν n (s i) (s j))⁻¹)
    (fun i => (cutoffK hC hν n p (s i))⁻¹)
  have hA n : ReciprocalKernel.OnePositiveSquare (A n) := by
    exact boundary_reciprocal_compact_support (cutoff_ae_norm (ν := ν) n)
      (cutoffRadius_lt_one n) hC (restrictDensity hν (cutoffSet n))
      (cutoffSet n) (cutoffSet_compact n) (cutoffSet_subset n)
      (by rw [Measure.restrict_apply (cutoffSet_measurable n).compl]; simp)
      hd0 hd1 (subcritical_restrict hC hν (cutoffSet n) hsub) p s
  apply ReciprocalKernel.onePositiveSquare_of_entrywise_tendsto hA
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases he : s i = s j
    · simp [A, ReciprocalKernel.bordered, he]
    · simpa only [A, ReciprocalKernel.bordered, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, he, ite_false] using
        (cutoffN_tendsto hC hν hn (s i) (s j) he).inv₀
          (fullBoundaryN_pos hC hν hn (s i) (s j) he).ne'
  · simpa only [A, ReciprocalKernel.bordered, Matrix.of_apply, Matrix.fromBlocks_apply₁₂] using
      (cutoffK_tendsto hC hν hn p (s i)).inv₀ (fullBoundaryK_pos hC hν hn p (s i)).ne'
  · simpa only [A, ReciprocalKernel.bordered, Matrix.of_apply, Matrix.fromBlocks_apply₂₁] using
      (cutoffK_tendsto hC hν hn p (s j)).inv₀ (fullBoundaryK_pos hC hν hn p (s j)).ne'
  · simp [A, ReciprocalKernel.bordered]


def fullDistanceKernel (p : disk) (s t : Boundary) : ℝ :=
  if s = t then 0 else fullBoundaryK hC hν p s * fullBoundaryK hC hν p t /
    fullBoundaryN hC hν s t



theorem negative_kernel {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk)
    {ι : Type} [Fintype ι] (s : ι → Boundary) :
    ReciprocalKernel.ConditionallyNegative (Matrix.of fun i j =>
      fullDistanceKernel hC hν p (s i) (s j)) := by
  classical
  have hn : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  have h := ReciprocalKernel.conditionalNegative_scaled_of_bordered
    (fun i => fullBoundaryK hC hν p (s i))
    (fun i => (fullBoundaryK_pos hC hν hn p (s i)).ne')
    (boundary_reciprocal hC hν hd0 hd1 hsub p s)
  convert h using 1
  ext i j
  by_cases he : s i = s j
  · simp [fullDistanceKernel, he]
  · simp only [fullDistanceKernel, he, ite_false, Matrix.of_apply, div_eq_mul_inv]
    ring

end StrictHotSpots.PlaneGreen
end
end FullBoundaryReciprocalLayer



end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section FullBoundaryEmbeddingLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryK_bounded (p : disk) : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : Boundary,
    fullBoundaryK hC hν p s ≤ B := by
  obtain ⟨B,hB,h⟩ := green_poisson_uniform_bound hC hν
  let M : ℝ := (measureUnivNNReal ν : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * B
  have hM : 0 ≤ M := mul_nonneg (Real.rpow_nonneg (by positivity) _) hB
  have hs (s : Boundary) : ‖smoothedRow hC hν s‖ ≤ M := by
    apply Lp.norm_le_of_ae_bound hB
    filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
    rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
    exact h x hxd s
  let A : ℝ := 1 / (2 * Real.pi * (1 - ‖(p : Plane)‖) ^ 2)
  refine ⟨A + B + ‖row hC hν p‖ * ‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)‖ * M,
    by dsimp [A]; positivity, fun s => ?_⟩
  unfold fullBoundaryK
  apply add_le_add
  · apply add_le_add
    · exact DiskFormula.poisson_bounded _ _ (by simpa using s.property)
        (by simp) (by simpa [disk] using p.property)
    · exact (le_abs_self _).trans (h p p.property s)
  · calc
      _ ≤ ‖row hC hν p‖ * ‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)
          (smoothedRow hC hν s)‖ := real_inner_le_norm _ _
      _ ≤ ‖row hC hν p‖ * (‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)‖ * M) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hs s) (norm_nonneg _))
      _ = _ := (mul_assoc _ _ _).symm

lemma boundaryInteraction_eq_dist (s t : Boundary) :
    boundaryInteraction s t = 1 / (Real.pi * dist s t ^ 2) := by
  simp only [boundaryInteraction, DiskFormula.boundaryInteraction, ← map_sub,
    LinearIsometryEquiv.norm_map, Subtype.dist_eq, dist_eq_norm]

lemma boundaryInteraction_le_fullBoundaryN (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (s t : Boundary) : boundaryInteraction s t ≤ fullBoundaryN hC hν s t := by
  have h1 : 0 ≤ ∫ x, poisson s x * poisson t x ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_mem_disk hν] with x hx
    exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩)
  have h2 : 0 ≤ ∫ x, poisson s x * smoothedPoisson (ν := ν) t x ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_mem_disk hν] with x hx
    exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (smoothedPoisson_nonneg hν t hx)
  have h3 := L2Limits.inner_nonneg (smoothedRow_nonneg hC hν s)
    (BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν)
      (smoothedRow_nonneg hC hν t))
  unfold fullBoundaryN
  linarith

lemma fullDistanceKernel_pos (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (p : disk) (s t : Boundary) (hst : s ≠ t) : 0 < fullDistanceKernel hC hν p s t := by
  rw [fullDistanceKernel, ite_eq_right hst]
  exact div_pos (mul_pos (fullBoundaryK_pos hC hν hT p s) (fullBoundaryK_pos hC hν hT p t))
    (fullBoundaryN_pos hC hν hT s t hst)

lemma fullDistanceKernel_bound (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (p : disk) : ∃ L : ℝ≥0, ∀ s t, fullDistanceKernel hC hν p s t ≤ (L : ℝ)^2 * dist s t ^ 2 := by
  obtain ⟨B,hB,hK⟩ := fullBoundaryK_bounded hC hν p
  let L : ℝ≥0 := ⟨Real.sqrt Real.pi * B, mul_nonneg (Real.sqrt_nonneg _) hB⟩
  refine ⟨L, fun s t => ?_⟩
  by_cases hst : s = t
  · subst t; simp [fullDistanceKernel]
  have hd : 0 < dist s t := dist_pos.mpr hst
  have hn := boundaryInteraction_le_fullBoundaryN hC hν hT s t
  rw [boundaryInteraction_eq_dist] at hn
  have hp := fullBoundaryN_pos hC hν hT s t hst
  have hkk : fullBoundaryK hC hν p s * fullBoundaryK hC hν p t ≤ B^2 := by
    exact (mul_le_mul (hK s) (hK t) (fullBoundaryK_pos hC hν hT p t).le hB).trans_eq (pow_two B).symm
  rw [fullDistanceKernel, ite_eq_right hst]
  calc
    _ ≤ B^2 / fullBoundaryN hC hν s t := div_le_div_of_nonneg_right hkk hp.le
    _ ≤ B^2 / (1 / (Real.pi * dist s t ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hn
    _ = (L : ℝ)^2 * dist s t ^ 2 := by
      change B^2 / (1 / (Real.pi * dist s t ^ 2)) =
        (Real.sqrt Real.pi * B)^2 * dist s t ^ 2
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
      field_simp

lemma fullDistanceKernel_conditionallyNegative {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk) :
    SquaredDistanceKernel.ConditionallyNegative (Matrix.of (fullDistanceKernel hC hν p)) := by
  classical
  refine ⟨?_, fun s => by simp [fullDistanceKernel], ?_⟩
  · ext s t
    have hh := (negative_kernel hC hν hd0 hd1 hsub p (fun b : Bool => if b then s else t)).1.apply false true
    simpa [Matrix.conjTranspose_apply] using hh.symm
  · intro c hc
    let a : c.support → ℝ := fun i => c i
    have ha : (∑ i, a i) = 0 := by
      change (∑ i : c.support, c i) = 0
      rw [Finset.sum_coe_sort c.support (fun x : Boundary => c x)]
      exact hc
    have hh := (negative_kernel hC hν hd0 hd1 hsub p (fun i : c.support => (i : Boundary))).2 a ha
    simp only [ReciprocalKernel.pairing, dotProduct, Matrix.mulVec, Matrix.of_apply,
      Finset.mul_sum, ← mul_assoc, a] at hh
    have he : (∑ i : c.support, ∑ j : c.support,
        c i * fullDistanceKernel hC hν p i j * c j) =
        c.sum (fun x a => c.sum (fun y b => a * fullDistanceKernel hC hν p x y * b)) := by
      calc
        _ = ∑ i : c.support, ∑ j ∈ c.support, c i * fullDistanceKernel hC hν p i j * c j := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_coe_sort c.support (fun j => c i * fullDistanceKernel hC hν p i j * c j)
        _ = _ := Finset.sum_coe_sort c.support (fun i =>
          ∑ j ∈ c.support, c i * fullDistanceKernel hC hν p i j * c j)
    rw [he] at hh
    exact hh



theorem full_boundary_hilbert_embedding {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (p : disk) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H) (b : Boundary → H) (L : ℝ≥0),
      Function.Injective b ∧ LipschitzWith L b ∧
        ∀ s t, ‖b s - b t‖ ^ 2 = fullDistanceKernel hC hν p s t := by
  have hT : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  obtain ⟨L,hL⟩ := fullDistanceKernel_bound hC hν hT p
  let o : Boundary := ⟨complexIso 1, by simp⟩
  obtain ⟨H,hn,hi,hc,hs,b,hb,hl,hd⟩ := SquaredDistanceKernel.separable_lipschitz_embedding
    (fullDistanceKernel_conditionallyNegative hC hν hd0 hd1 hsub p) o
    (fullDistanceKernel_pos hC hν hT p) hL
  exact ⟨H,hn,hi,hc,hs,b,L,hb,hl,hd⟩

end StrictHotSpots.PlaneGreen
end
end FullBoundaryEmbeddingLayer
end FullBoundaryCombinedLayer


end

end DouglasLipschitzBase

end OAI
