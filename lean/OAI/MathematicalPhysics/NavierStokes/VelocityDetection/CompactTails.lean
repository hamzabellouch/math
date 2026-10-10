import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailDifferentiability
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailCompleteness

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def ofCompact {n : ℕ} (f : Coord n → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) : compatible n :=
  ⟨(⟨⟨f, hf⟩, hc.is_zero_at_infty⟩,
     (memLp_one_iff_integrable.mpr (hf.integrable_of_hasCompactSupport hc)).toLp f),
    (memLp_one_iff_integrable.mpr (hf.integrable_of_hasCompactSupport hc)).coeFn_toLp⟩

@[simp] theorem ofCompact_apply {n : ℕ} (f : Coord n → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) (X : Coord n) :
    (ofCompact f hf hc).val.1 X = f X := rfl

theorem ext_fun {n : ℕ} {v w : compatible n}
    (h : ∀ X, v.val.1 X = w.val.1 X) : v = w := by
  apply Subtype.ext
  apply Prod.ext
  · exact ZeroAtInftyContinuousMap.ext h
  · apply Lp.ext
    filter_upwards [v.property, w.property] with X hv hw
    exact hv.trans ((h X).trans hw.symm)

theorem norm_le_of_support {n : ℕ} (v : compatible n) {K : Set (Coord n)}
    (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ X ∉ K, v.val.1 X = 0)
    (hb : ∀ X, ‖v.val.1 X‖ ≤ B) :
    ‖v‖ ≤ (1 + volume.real K) * B := by
  have h₀ : ‖v.val.1‖ ≤ B := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact (BoundedContinuousFunction.norm_le hB).mpr hb
  have hi : Integrable (K.indicator (fun _ : Coord n => B)) volume := by
    exact (integrableOn_const (C := B) hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have h₁ : ‖v.val.2‖ ≤ volume.real K * B := by
    rw [L1.norm_eq_integral_norm]
    have hv : (fun X => v.val.2 X) =ᵐ[volume] (fun X => v.val.1 X) := v.property
    calc
      (∫ X, ‖v.val.2 X‖) = ∫ X, ‖v.val.1 X‖ := integral_congr_ae (hv.fun_comp norm)
      _ ≤ ∫ X, K.indicator (fun _ : Coord n => B) X := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
        filter_upwards [] with X
        by_cases hX : X ∈ K
        · simpa only [Set.indicator_of_mem hX] using hb X
        · simp [hX, hs X hX]
      _ = volume.real K * B := by
        rw [integral_indicator hK.measurableSet, setIntegral_const]
        rfl
  change max ‖v.val.1‖ ‖v.val.2‖ ≤ _
  refine max_le ?_ ?_
  · nlinarith [measureReal_nonneg (μ := (volume : Measure (Coord n))) (s := K)]
  · nlinarith [measureReal_nonneg (μ := (volume : Measure (Coord n))) (s := K)]

def LocalHorizontalSupport (f : ScalarField 2) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : Set (Coord 2), IsCompact K ∧
    ∀ t, |t| ≤ T → ∀ X ∉ K, f t X = 0

theorem LocalHorizontalSupport.slice {f : ScalarField 2}
    (hf : LocalHorizontalSupport f) (t : ℝ) : HasCompactSupport (f t) := by
  obtain ⟨K, hK, hzero⟩ := hf |t| (abs_nonneg _)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro X hX
  by_contra hnot
  exact hX (hzero t le_rfl X hnot)

theorem continuous_intersection_of_support (F : ℝ → compatible 2)
    (hf : Continuous (fun q : ℝ × Coord 2 => (F q.1).val.1 q.2))
    (hs : LocalHorizontalSupport (fun t X => (F t).val.1 X)) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨K, hK, hzero⟩ := hs (|t| + 1) (by positivity)
  change ∀ r, |r| ≤ |t| + 1 → ∀ X ∉ K, (F r).val.1 X = 0 at hzero
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : C(ℝ, C(K, ℝ)) := ContinuousMap.curry ⟨fun q : ℝ × K => (F q.1).val.1 q.2.val,
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have hG : Continuous G := G.continuous
  have hT : ∀ᶠ s in 𝓝 t, |s| ≤ |t| + 1 := by
    filter_upwards [(continuous_abs.tendsto t).eventually (gt_mem_nhds (by linarith : |t| < |t| + 1))] with s hs
    exact hs.le
  change Tendsto F (𝓝 t) (𝓝 (F t))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hV : 0 ≤ volume.real K := measureReal_nonneg
  have hC : 0 < 1 + volume.real K := by linarith
  have hε' : 0 < ε / (2 * (1 + volume.real K)) := div_pos hε (by positivity)
  have H := (Metric.tendsto_nhds.mp (hG.tendsto t)) _ hε'
  filter_upwards [H, hT] with s hdist hst
  rw [dist_eq_norm] at hdist
  change dist (F s).val (F t).val < ε
  rw [dist_eq_norm]
  change ‖F s - F t‖ < ε
  have hbound (X : Coord 2) : ‖(F s - F t).val.1 X‖ ≤ ε / (2 * (1 + volume.real K)) := by
    by_cases hX : X ∈ K
    · calc
        ‖(F s - F t).val.1 X‖ = ‖(G s - G t) ⟨X, hX⟩‖ := rfl
        _ ≤ ‖G s - G t‖ := ContinuousMap.norm_coe_le_norm _ _
        _ ≤ _ := hdist.le
    · change ‖(F s).val.1 X - (F t).val.1 X‖ ≤ _
      rw [hzero s hst X hX, hzero t (by linarith [le_abs_self t] : |t| ≤ |t| + 1) X hX]
      simpa using hε'.le
  have hz (X : Coord 2) (hX : X ∉ K) : (F s - F t).val.1 X = 0 := by
    change (F s).val.1 X - (F t).val.1 X = 0
    rw [hzero s hst X hX, hzero t (by linarith : |t| ≤ |t| + 1) X hX, sub_self]
  have hh := norm_le_of_support (F s - F t) hK hε'.le hz hbound
  have heq : (1 + volume.real K) * (ε / (2 * (1 + volume.real K))) = ε / 2 := by
    field_simp [hC.ne']
  exact hh.trans_lt (by rw [heq]; linarith)

theorem continuous_ofCompact_curve {f : ScalarField 2}
    (hf : Continuous (uncurry f)) (hs : LocalHorizontalSupport f) :
    Continuous (fun t => ofCompact (f t)
      (hf.comp (continuous_const.prodMk continuous_id)) (hs.slice t)) := by
  apply continuous_intersection_of_support
  · exact hf
  · exact hs

theorem LocalHorizontalSupport.dAlong {f : ScalarField 2}
    (hf : LocalHorizontalSupport f) (v : ℝ × Coord 2) :
    LocalHorizontalSupport (fun t X => JointCalculus.dAlong v (uncurry f) (t, X)) := by
  intro T hT
  obtain ⟨K, hK, hzero⟩ := hf (T + 1) (by linarith)
  refine ⟨K, hK, ?_⟩
  intro t ht X hX
  have ht' : ∀ᶠ q : ℝ × Coord 2 in 𝓝 (t, X), |q.1| < T + 1 :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).mem_nhds (by
      change |t| < T + 1
      linarith)
  have hX' : ∀ᶠ q : ℝ × Coord 2 in 𝓝 (t, X), q.2 ∉ K :=
    (hK.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hX
  have heq : uncurry f =ᶠ[𝓝 (t, X)] (fun _ => (0 : ℝ)) := by
    filter_upwards [ht', hX'] with q hq hqK
    exact hzero q.1 hq.le q.2 hqK
  have hd := (JointCalculus.eventuallyEq_dAlong v heq).eq_of_nhds
  simpa only [JointCalculus.dAlong, fderiv_const_apply, zero_apply] using hd

theorem LocalHorizontalSupport.spatialD {f : ScalarField 2}
    (hs : LocalHorizontalSupport f) (hf : ContDiff ℝ ∞ (uncurry f)) (i : Fin 2) :
    LocalHorizontalSupport (spatialD i f) := by
  have heq : VelocityDetection.spatialD i f = fun t X => JointCalculus.dAlong (0, Pi.single i 1) (uncurry f) (t, X) :=
    funext fun t => funext fun X => JointCalculus.spatialD_eq hf i t X
  rw [heq]
  exact hs.dAlong _

theorem hasDerivAt_intersection {F dF : ℝ → compatible 2}
    (hdF : Continuous dF)
    (hder : ∀ t X, HasDerivAt (fun s => (F s).val.1 X) ((dF t).val.1 X) t) (t : ℝ) :
    HasDerivAt F (dF t) t := by
  have heq (s : ℝ) : F s = F 0 + ∫ r in (0 : ℝ)..s, dF r := by
    apply ext_fun
    intro X
    change (F s).val.1 X = eval X (F 0 + ∫ r in (0 : ℝ)..s, dF r)
    rw [map_add]
    have hint : (∫ r in (0 : ℝ)..s, eval X (dF r)) = eval X (∫ r in (0 : ℝ)..s, dF r) :=
      ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (μ := volume) (E := compatible 2) (F := ℝ)
        (eval X) (Continuous.intervalIntegrable (E := compatible 2) hdF 0 s)
    rw [← hint]
    have hc : Continuous (fun r => (dF r).val.1 X) := (eval X).continuous.comp hdF
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ uIcc (0 : ℝ) s) => hder r X) (hc.intervalIntegrable 0 s)
    simp only [eval_apply]
    rw [hh]
    ring
  have hm : StronglyMeasurable dF := Continuous.stronglyMeasurable hdF
  have H := HasDerivAt.const_add (F := compatible 2) (F 0)
    (intervalIntegral.integral_hasDerivAt_right (E := compatible 2)
      (Continuous.intervalIntegrable (E := compatible 2) hdF 0 t)
      hm.stronglyMeasurableAtFilter hdF.continuousAt)
  exact HasDerivAt.congr_of_eventuallyEq (F := compatible 2) H (Filter.Eventually.of_forall heq)

theorem c1Tails_of_smooth_support {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) : C1Tails f := by
  let g : ScalarField 2 := fun t X => JointCalculus.dAlong (1, 0) (uncurry f) (t, X)
  have hg : ContDiff ℝ ∞ (uncurry g) := JointCalculus.contDiff_dAlong _ hf
  have hgs : LocalHorizontalSupport g := hs.dAlong _
  let F : ℝ → compatible 2 := fun t => ofCompact (f t)
    (hf.continuous.comp (continuous_const.prodMk continuous_id)) (hs.slice t)
  let dF : ℝ → compatible 2 := fun t => ofCompact (g t)
    (hg.continuous.comp (continuous_const.prodMk continuous_id)) (hgs.slice t)
  have hdF : Continuous dF := continuous_ofCompact_curve hg.continuous hgs
  refine ⟨F, dF, (continuous_ofCompact_curve hf.continuous hs).continuousOn,
    hdF.continuousOn, fun _ _ => rfl, ?_⟩
  intro t ht
  apply HasDerivAt.hasDerivWithinAt (𝕜 := ℝ) (F := compatible 2) (hasDerivAt_intersection hdF ?_ t)
  intro s X
  change HasDerivAt (fun r => f r X) (JointCalculus.dAlong (1, 0) (uncurry f) (s, X)) s
  simpa only [comp_def, JointCalculus.dAlong, uncurry_apply_pair, id_eq] using
    ((hf.differentiable (by simp) (s, X)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s X)))

theorem spatial_c1Tails_of_smooth_support {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) (i : Fin 2) :
    C1Tails (spatialD i f) := by
  have hdiff : ContDiff ℝ ∞ (uncurry (spatialD i f)) := by
    have heq : uncurry (spatialD i f) = JointCalculus.dAlong (0, Pi.single i 1) (uncurry f) :=
      funext fun q => JointCalculus.spatialD_eq hf i q.1 q.2
    rw [heq]
    exact JointCalculus.contDiff_dAlong _ hf
  exact c1Tails_of_smooth_support hdiff (hs.spatialD hf i)

theorem second_continuousTails_of_smooth_support {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) (i k : Fin 2) :
    ContinuousTails (spatialD k (spatialD i f)) := by
  have hdiff : ContDiff ℝ ∞ (uncurry (spatialD i f)) := by
    have heq : uncurry (spatialD i f) = JointCalculus.dAlong (0, Pi.single i 1) (uncurry f) :=
      funext fun q => JointCalculus.spatialD_eq hf i q.1 q.2
    rw [heq]
    exact JointCalculus.contDiff_dAlong _ hf
  exact (spatial_c1Tails_of_smooth_support hdiff (hs.spatialD hf i) k).continuous

end VelocityDetection.TailSpace
end

end OAI
