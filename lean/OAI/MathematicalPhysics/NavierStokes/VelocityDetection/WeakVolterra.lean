import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailDifferentiability

namespace OAI

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]
variable {T : ℝ} (hT : 0 ≤ T)

abbrev Curve (T : ℝ) (E : Type*) [TopologicalSpace E] := C(Icc (0 : ℝ) T, E)

def extend (q : Curve T E) (r : ℝ) : E := q (projIcc 0 T hT r)

theorem continuous_extend [NormedSpace ℝ E] [CompleteSpace E]
    (q : Curve T E) : Continuous (extend hT q) :=
  q.continuous.comp continuous_projIcc

@[simp] theorem extend_of_mem [NormedSpace ℝ E] [CompleteSpace E]
    (q : Curve T E) {r : ℝ} (hr : r ∈ Icc 0 T) :
    extend hT q r = q ⟨r, hr⟩ := by rw [extend, projIcc_of_mem hT hr]

theorem norm_extend_le [NormedSpace ℝ E] [CompleteSpace E]
    (q : Curve T E) (r : ℝ) : ‖extend hT q r‖ ≤ ‖q‖ :=
  q.norm_coe_le_norm _

end VelocityDetection.WeakVolterra
end

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} (hT : 0 ≤ T)
variable (K : ℝ → ℝ → E →L[ℝ] E) (β : ℝ → ℝ)

def raw (q : Curve T E) (t : ℝ) : E :=
  ∫ s in Ioc (0 : ℝ) T, (Iic t).indicator (fun s => K s (t - s) (extend hT q (t - s))) s

end VelocityDetection.WeakVolterra
end

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} (hT : 0 ≤ T)
variable (K : ℝ → ℝ → E →L[ℝ] E) (β : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (Ioi (0 : ℝ) ×ˢ univ))
variable (hβ : IntegrableOn β (Ioc (0 : ℝ) T))
variable (hβ0 : ∀ s ∈ Ioc (0 : ℝ) T, 0 ≤ β s)
variable (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ∀ r : ℝ, ∀ v : E, ‖K s r v‖ ≤ β s * ‖v‖)

include hK hβ hβ0 hbound

theorem integrable_raw (q : Curve T E) (t : ℝ) :
    Integrable (fun s => (Iic t).indicator (fun s => K s (t - s) (extend hT q (t - s))) s)
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hc : ContinuousOn (fun s => K s (t - s) (extend hT q (t - s))) (Ioc (0 : ℝ) T) := by
    apply hK.comp (continuous_id.prodMk ((continuous_const.sub continuous_id).prodMk
      ((continuous_extend hT q).comp (continuous_const.sub continuous_id)))).continuousOn
    intro s hs
    exact ⟨hs.1, mem_univ _⟩
  apply (hβ.mul_const ‖q‖).mono'
  · exact hc.aestronglyMeasurable measurableSet_Ioc |>.indicator measurableSet_Iic
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    by_cases hst : s ≤ t
    · rw [Set.indicator_of_mem (s := Iic t) hst]
      exact (hbound s hs _ _).trans (mul_le_mul_of_nonneg_left (norm_extend_le hT q _) (hβ0 s hs))
    · rw [Set.indicator_of_notMem (s := Iic t) hst]
      exact le_trans (by simp) (mul_nonneg (hβ0 s hs) (norm_nonneg q))

theorem continuous_raw (q : Curve T E) : Continuous (raw hT K q) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated (bound := fun s => β s * ‖q‖)
  · exact Eventually.of_forall (fun r => (integrable_raw hT K β hK hβ hβ0 hbound q r).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro r
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    by_cases hsr : s ≤ r
    · rw [Set.indicator_of_mem (s := Iic r) hsr]
      exact (hbound s hs _ _).trans (mul_le_mul_of_nonneg_left (norm_extend_le hT q _) (hβ0 s hs))
    · rw [Set.indicator_of_notMem (s := Iic r) hsr]
      exact le_trans (by simp) (mul_nonneg (hβ0 s hs) (norm_nonneg q))
  · exact hβ.mul_const ‖q‖
  · have hne : ∀ᵐ s : ℝ ∂volume.restrict (Ioc (0 : ℝ) T), s ≠ t := by
      rw [ae_iff]
      simp only [not_not, ofPred_eq_eq_singleton]
      simp
    filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with s hst hs
    have hc : Continuous (fun r => K s (r - s) (extend hT q (r - s))) := by
      rw [← continuousOn_univ]
      apply hK.comp (continuous_const.prodMk ((continuous_id.sub continuous_const).prodMk
        ((continuous_extend hT q).comp (continuous_id.sub continuous_const)))).continuousOn
      exact fun _ _ => ⟨hs.1, mem_univ _⟩
    rcases lt_or_gt_of_ne hst with hst | hts
    · have he : (fun r => (Iic r).indicator (fun s => K s (r - s) (extend hT q (r - s))) s) =ᶠ[𝓝 t]
          (fun r => K s (r - s) (extend hT q (r - s))) := by
        filter_upwards [lt_mem_nhds hst] with r hr
        exact Set.indicator_of_mem (s := Iic r) hr.le _
      exact hc.continuousAt.congr_of_eventuallyEq he
    · have he : (fun r => (Iic r).indicator (fun s => K s (r - s) (extend hT q (r - s))) s) =ᶠ[𝓝 t]
          (fun _ => (0 : E)) := by
        filter_upwards [gt_mem_nhds hts] with r hr
        exact Set.indicator_of_notMem (s := Iic r) (not_le.mpr hr) _
      exact continuousAt_const.congr_of_eventuallyEq he

theorem norm_raw_le (q : Curve T E) (t : ℝ) :
    ‖raw hT K q t‖ ≤ (∫ s in Ioc (0 : ℝ) T, β s) * ‖q‖ := by
  calc
    ‖raw hT K q t‖ ≤ ∫ s in Ioc (0 : ℝ) T,
        ‖(Iic t).indicator (fun s => K s (t - s) (extend hT q (t - s))) s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc (0 : ℝ) T, β s * ‖q‖ := by
      apply integral_mono_ae (integrable_raw hT K β hK hβ hβ0 hbound q t).norm (hβ.mul_const ‖q‖)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      by_cases hst : s ≤ t
      · rw [Set.indicator_of_mem (s := Iic t) hst]
        exact (hbound s hs _ _).trans (mul_le_mul_of_nonneg_left (norm_extend_le hT q _) (hβ0 s hs))
      · rw [Set.indicator_of_notMem (s := Iic t) hst]
        exact le_trans (by simp) (mul_nonneg (hβ0 s hs) (norm_nonneg q))
    _ = _ := integral_mul_const _ _

def operator : Curve T E →L[ℝ] Curve T E :=
  LinearMap.mkContinuous
    { toFun := fun q => ⟨fun t => raw hT K q t.val,
        (continuous_raw hT K β hK hβ hβ0 hbound q).comp continuous_subtype_val⟩
      map_add' := by
        intro q r
        ext t
        change raw hT K (q + r) t.val = raw hT K q t.val + raw hT K r t.val
        simp only [raw, extend, ContinuousMap.add_apply, map_add, indicator_add]
        exact integral_add (integrable_raw hT K β hK hβ hβ0 hbound q t.val)
          (integrable_raw hT K β hK hβ hβ0 hbound r t.val)
      map_smul' := by
        intro c q
        ext t
        change raw hT K (c • q) t.val = c • raw hT K q t.val
        simp only [raw, extend, ContinuousMap.smul_apply, map_smul, indicator_smul]
        exact integral_smul c _ }
    (∫ s in Ioc (0 : ℝ) T, β s) (by
      intro q
      apply (ContinuousMap.norm_le _ (mul_nonneg (integral_nonneg_of_ae
        ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hβ0 s hs))) (norm_nonneg q))).mpr
      intro t
      exact norm_raw_le hT K β hK hβ hβ0 hbound q t.val)

@[simp] theorem operator_apply (q : Curve T E) (t : Icc (0 : ℝ) T) :
    operator hT K β hK hβ hβ0 hbound q t = raw hT K q t.val := rfl

theorem norm_operator_apply_le (q : Curve T E) :
    ‖operator hT K β hK hβ hβ0 hbound q‖ ≤ (∫ s in Ioc (0 : ℝ) T, β s) * ‖q‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ioc).mono
      (fun s hs => hβ0 s hs))) (norm_nonneg q))).mpr
  intro t
  exact norm_raw_le hT K β hK hβ hβ0 hbound q t.val

end VelocityDetection.WeakVolterra
end

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ} (hT : 0 ≤ T) (K : ℝ → ℝ → E →L[ℝ] E)

theorem raw_eq_integral [CompleteSpace E] (q : Curve T E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    raw hT K q t = ∫ s in Ioc (0 : ℝ) t, K s (t - s) (extend hT q (t - s)) := by
  rw [raw, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le ht.2]

@[simp] theorem raw_zero [CompleteSpace E] (q : Curve T E) : raw hT K q 0 = 0 := by
  rw [raw_eq_integral hT K q ⟨le_rfl, hT⟩]
  simp

def weight (σ : ℝ) (q : Curve T E) : Curve T E :=
  ⟨fun t => Real.exp (σ * t.val) • q t,
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul q.continuous⟩

@[simp] theorem weight_apply [CompleteSpace E] (σ : ℝ) (q : Curve T E) (t : Icc (0 : ℝ) T) :
    weight σ q t = Real.exp (σ * t.val) • q t := rfl

@[simp] theorem weight_add [CompleteSpace E] (σ : ℝ) (q r : Curve T E) :
    weight σ (q + r) = weight σ q + weight σ r := by
  ext t
  simp [weight, smul_add]

@[simp] theorem weight_weight [CompleteSpace E] (σ κ : ℝ) (q : Curve T E) :
    weight σ (weight κ q) = weight (σ + κ) q := by
  ext t
  simp only [weight_apply, smul_smul, ← Real.exp_add]
  congr 2
  ring

@[simp] theorem weight_zero [CompleteSpace E] (q : Curve T E) : weight 0 q = q := by
  ext t
  simp

@[simp] theorem weight_neg_weight [CompleteSpace E] (σ : ℝ) (q : Curve T E) :
    weight (-σ) (weight σ q) = q := by rw [weight_weight, neg_add_cancel, weight_zero]

def dampKernel (σ : ℝ) (s r : ℝ) : E →L[ℝ] E := Real.exp (-σ * s) • K s r

def dampBound (β : ℝ → ℝ) (σ s : ℝ) : ℝ := Real.exp (-σ * s) * β s

theorem raw_weight [CompleteSpace E] (σ : ℝ) (q : Curve T E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    raw hT K (weight σ q) t = Real.exp (σ * t) • raw hT (dampKernel K σ) q t := by
  rw [raw_eq_integral hT K _ ht, raw_eq_integral hT (dampKernel K σ) _ ht,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hts : t - s ∈ Icc (0 : ℝ) T := ⟨sub_nonneg.mpr hs.2, by linarith [ht.2, hs.1]⟩
  rw [extend_of_mem hT _ hts, extend_of_mem hT _ hts, weight_apply, map_smul]
  simp only [dampKernel, smul_apply, smul_smul, ← Real.exp_add]
  congr 2
  ring

end VelocityDetection.WeakVolterra
end

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} (hT : 0 ≤ T) (K : ℝ → ℝ → E →L[ℝ] E)
variable (β : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (Ioi (0 : ℝ) ×ˢ univ))
variable (hβ : IntegrableOn β (Ioc (0 : ℝ) T))
variable (hβ0 : ∀ s ∈ Ioc (0 : ℝ) T, 0 ≤ β s)
variable (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ∀ r : ℝ, ∀ v : E, ‖K s r v‖ ≤ β s * ‖v‖)

theorem existsUnique_of_small (hsmall : (∫ s in Ioc (0 : ℝ) T, β s) < 1)
    (g : Curve T E) :
    ∃! q : Curve T E, q = g + operator hT K β hK hβ hβ0 hbound q := by
  let B := operator hT K β hK hβ hβ0 hbound
  let b : NNReal := ⟨∫ s in Ioc (0 : ℝ) T, β s,
    integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hβ0 s hs))⟩
  have hc : ContractingWith b (fun q => g + B q) := by
    refine ⟨hsmall, lipschitzWith_iff_norm_sub_le.mpr ?_⟩
    intro q r
    change ‖(g + B q) - (g + B r)‖ ≤ (∫ s in Ioc (0 : ℝ) T, β s) * ‖q - r‖
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact norm_operator_apply_le hT K β hK hβ hβ0 hbound (q - r)
  refine ⟨hc.fixedPoint (fun q => g + B q), hc.fixedPoint_isFixedPt.symm, ?_⟩
  intro q hq
  exact hc.fixedPoint_unique hq.symm

omit [CompleteSpace E] in
include hK in

theorem continuousOn_dampKernel [CompleteSpace E] (σ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ × E => dampKernel K σ p.1 p.2.1 p.2.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn).smul hK

include hβ hβ0 in

theorem integrableOn_dampBound {σ : ℝ} (hσ : 0 ≤ σ) :
    IntegrableOn (dampBound β σ) (Ioc (0 : ℝ) T) := by
  apply hβ.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
      hβ.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he : Real.exp (-σ * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.1])
    simp only [dampBound, Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg (hβ0 s hs)]
    exact mul_le_of_le_one_left (hβ0 s hs) he

include hβ0 in

theorem dampBound_nonneg (σ : ℝ) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) :
    0 ≤ dampBound β σ s := mul_nonneg (Real.exp_pos _).le (hβ0 s hs)

omit [CompleteSpace E] in
include hbound in

theorem norm_dampKernel_le [CompleteSpace E] (σ : ℝ) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) (r : ℝ) (v : E) :
    ‖dampKernel K σ s r v‖ ≤ dampBound β σ s * ‖v‖ := by
  simp only [dampKernel, smul_apply, norm_smul,
    Real.norm_eq_abs, Real.abs_exp, dampBound, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbound s hs r v) (Real.exp_pos _).le

include hβ hβ0 in

theorem tendsto_integral_dampBound :
    Tendsto (fun n : ℕ => ∫ s in Ioc (0 : ℝ) T, dampBound β (n : ℝ) s) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) T))
      (f := fun _ => (0 : ℝ)) β
      (fun n => (integrableOn_dampBound β hβ hβ0 (Nat.cast_nonneg n)).aestronglyMeasurable) hβ
  simp only [integral_zero] at hh
  apply hh
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he : Real.exp (-(n : ℝ) * s) ≤ 1 := Real.exp_le_one_iff.mpr (by
      rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hs.1.le))
    simp only [dampBound, Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg (hβ0 s hs)]
    exact mul_le_of_le_one_left (hβ0 s hs) he
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.atTop_mul_const hs.1 (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa only [dampBound, neg_mul, zero_mul, Function.comp_def] using he.mul_const (β s)

end VelocityDetection.WeakVolterra
end

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} (hT : 0 ≤ T) (K : ℝ → ℝ → E →L[ℝ] E) (β : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (Ioi (0 : ℝ) ×ˢ univ))
variable (hβ : IntegrableOn β (Ioc (0 : ℝ) T))
variable (hβ0 : ∀ s ∈ Ioc (0 : ℝ) T, 0 ≤ β s)
variable (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ∀ r : ℝ, ∀ v : E, ‖K s r v‖ ≤ β s * ‖v‖)

theorem existsUnique (g : Curve T E) :
    ∃! q : Curve T E, q = g + operator hT K β hK hβ hβ0 hbound q := by
  obtain ⟨n, hn⟩ := ((tendsto_integral_dampBound β hβ hβ0).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)).exists
  let σ : ℝ := n
  have hσ : 0 ≤ σ := Nat.cast_nonneg n
  let Kd := dampKernel K σ
  let bd := dampBound β σ
  have hc := continuousOn_dampKernel K hK σ
  have hi := integrableOn_dampBound β hβ hβ0 hσ
  have hb0 := fun s hs => dampBound_nonneg β hβ0 σ (s := s) hs
  have hb := fun s hs r v => norm_dampKernel_le K β hbound σ (s := s) hs r v
  let A := operator hT K β hK hβ hβ0 hbound
  let D := operator hT Kd bd hc hi hb0 hb
  have hcon (q : Curve T E) : weight σ (D q) = A (weight σ q) := by
    ext t
    exact (raw_weight hT K σ q t.property).symm
  obtain ⟨q, hq, huq⟩ := existsUnique_of_small hT Kd bd hc hi hb0 hb hn (weight (-σ) g)
  refine ⟨weight σ q, ?_, ?_⟩
  · change q = weight (-σ) g + D q at hq
    have hh := congrArg (weight σ) hq
    simpa only [weight_add, weight_weight, add_neg_cancel, weight_zero, hcon] using hh
  · intro y hy
    have hdinv : weight σ (D (weight (-σ) y)) = A y := by
      simpa only [weight_weight, add_neg_cancel, weight_zero] using hcon (weight (-σ) y)
    have hyq : weight (-σ) y = weight (-σ) g + D (weight (-σ) y) := by
      have hh := congrArg (weight (-σ)) hy
      rw [weight_add, ← hdinv, weight_neg_weight] at hh
      exact hh
    have heq := congrArg (weight σ) (huq _ hyq)
    simpa only [weight_weight, add_neg_cancel, weight_zero] using heq

include hK hβ hβ0 hbound in

theorem existsUnique_pointwise (g : Curve T E) :
    ∃! q : Curve T E, ∀ t : Icc (0 : ℝ) T,
      q t = g t + ∫ s in Ioc (0 : ℝ) t.val, K s (t.val - s) (extend hT q (t.val - s)) := by
  have heq (q : Curve T E) : (q = g + operator hT K β hK hβ hβ0 hbound q) ↔
      (∀ t : Icc (0 : ℝ) T,
        q t = g t + ∫ s in Ioc (0 : ℝ) t.val, K s (t.val - s) (extend hT q (t.val - s))) := by
    rw [ContinuousMap.ext_iff]
    simp only [ContinuousMap.add_apply, operator_apply]
    exact forall_congr' (fun t => by rw [raw_eq_integral hT K _ t.property])
  exact (existsUnique_congr heq).mp (existsUnique hT K β hK hβ hβ0 hbound g)

end VelocityDetection.WeakVolterra
end

end OAI
