import OAI.Combinatorics.PlanarL1.Cuts

namespace OAI

section

namespace PlanarL1.Rebase
open scoped NNReal

variable {K : ℝ≥0} {ψ : ℝ → ℝ}

lemma shear_strictMono (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) :
    StrictMono (fun H => H+ψ H) := by
  intro s t hst
  have h := hψ.dist_le_mul s t
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst.le)] at h
  have hb := (abs_le.mp h).2
  have hm : (1-(K:ℝ))*(t-s) > 0 := mul_pos (by linarith) (by linarith)
  nlinarith

lemma shear_surjective (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) :
    Function.Surjective (fun H => H+ψ H) := by
  intro t
  let T := (|ψ 0|+|t|+1)/(1-(K:ℝ))
  have hden : 0 < 1-(K:ℝ) := by linarith
  have hT : 0 < T := div_pos (by positivity) hden
  have he : T*(1-(K:ℝ)) = |ψ 0|+|t|+1 := div_mul_cancel₀ _ (ne_of_gt hden)
  have hr := hψ.dist_le_mul T 0
  have hl := hψ.dist_le_mul (-T) 0
  rw [Real.dist_eq,Real.dist_eq,sub_zero,abs_of_pos hT] at hr
  rw [Real.dist_eq,Real.dist_eq,sub_zero,abs_neg,abs_of_pos hT] at hl
  have hp : t ≤ T+ψ T := by
    have := (abs_le.mp hr).1
    nlinarith [le_abs_self t,neg_abs_le (ψ 0)]
  have hm : -T+ψ (-T) ≤ t := by
    have := (abs_le.mp hl).2
    nlinarith [neg_abs_le t,le_abs_self (ψ 0)]
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc (by linarith : -T ≤ T)
    (continuous_id.add hψ.continuous).continuousOn ⟨hm,hp⟩
  exact ⟨x,hx⟩

/-- The branch change of variable H ↦ H+ψ(H) is a genuine increasing
bijection on the WHOLE real line, not just on the current chart heights. -/
noncomputable def shear (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) : ℝ ≃o ℝ :=
  (shear_strictMono hK hψ).orderIsoOfSurjective _ (shear_surjective hK hψ)

@[simp] lemma shear_apply (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) (H : ℝ) :
    shear hK hψ H = H+ψ H := rfl

end PlanarL1.Rebase


namespace PlanarL1.Threshold
open MeasureTheory
open scoped ENNReal

noncomputable def half (a z : ℝ) : ℝ := if z < a then 1 else 0

lemma measurable_half (a : ℝ) : Measurable (half a) := by
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

lemma abs_sub_half_of_le {a b : ℝ} (hab : a ≤ b) (z : ℝ) :
    |half a z-half b z| = (Set.Ico a b).indicator (fun _ => (1:ℝ)) z := by
  by_cases ha : z < a
  · have hb : z < b := ha.trans_le hab
    simp [half,ha,hb,Set.mem_Ico,not_le.mpr ha]
  · by_cases hb : z < b
    · simp [half,ha,hb,Set.mem_Ico,le_of_not_gt ha]
    · simp [half,ha,hb,Set.mem_Ico]

lemma abs_sub_half (a b z : ℝ) :
    |half a z-half b z| = (Set.Ico (min a b) (max a b)).indicator (fun _ => (1:ℝ)) z := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h,max_eq_right h] using abs_sub_half_of_le h z
  · rw [abs_sub_comm]
    simpa only [min_eq_right h,max_eq_left h] using abs_sub_half_of_le h z

lemma integrable_abs_sub_half (a b : ℝ) :
    Integrable (fun z => |half a z-half b z|) volume := by
  simp only [abs_sub_half]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (measure_Ico_lt_top.ne))

lemma integrable_sub_half (a b : ℝ) : Integrable (fun z => half a z-half b z) volume := by
  apply (integrable_norm_iff ((measurable_half a).sub (measurable_half b)).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using integrable_abs_sub_half a b

lemma integral_abs_sub_half (a b : ℝ) :
    (∫ z, |half a z-half b z|) = |a-b| := by
  simp only [abs_sub_half,integral_indicator_const (1:ℝ) measurableSet_Ico,smul_eq_mul,mul_one]
  rw [Real.volume_real_Ico]
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h),max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h),max_eq_left (sub_nonneg.mpr h)]

/-- The elementary two-sign identity behind exact vertical control. -/
lemma two_sign_abs (a b : ℝ) : (|a+b|+|a-b|)/2 = max |a| |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha,abs_of_nonneg hb,abs_of_nonneg (add_nonneg ha hb)]
    rcases le_total a b with h | h
    · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  · rw [abs_of_nonneg ha,abs_of_nonpos hb,abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))]
    rcases le_total a (-b) with h | h
    · rw [max_eq_right h,abs_of_nonpos (by linarith : a+b ≤ 0)]; ring
    · rw [max_eq_left h,abs_of_nonneg (by linarith : 0 ≤ a+b)]; ring
  · rw [abs_of_nonpos ha,abs_of_nonneg hb,abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))]
    rcases le_total (-a) b with h | h
    · rw [max_eq_right h,abs_of_nonneg (by linarith : 0 ≤ a+b)]; ring
    · rw [max_eq_left h,abs_of_nonpos (by linarith : a+b ≤ 0)]; ring
  · rw [abs_of_nonpos ha,abs_of_nonpos hb,abs_of_nonpos (add_nonpos ha hb)]
    rcases le_total (-a) (-b) with h | h
    · rw [max_eq_right h,abs_of_nonneg (by linarith : 0 ≤ a-b)]; ring
    · rw [max_eq_left h,abs_of_nonpos (by linarith : a-b ≤ 0)]; ring

local instance signMeasurableSpace : MeasurableSpace Bool := ⊤

/-- Lebesgue times a fair sign; its total mass is infinite, as in the source. -/
noncomputable def labelMeasure : Measure (Bool × ℝ) :=
  (1/2 : ℝ≥0∞) • (Measure.count.prod (volume : Measure ℝ))

noncomputable def chartValue (h p : ℝ) (z : Bool × ℝ) : ℝ :=
  half (if z.1 then h+p else h-p) z.2

lemma measurable_chartValue (h p : ℝ) : Measurable (chartValue h p) := by
  apply measurable_from_prod_countable_right
  intro b
  change Measurable (half (if b then h+p else h-p))
  exact measurable_half _

lemma integrable_chart_difference_count (h p k q : ℝ) :
    Integrable (fun z => chartValue h p z-chartValue k q z)
      (Measure.count.prod volume) := by
  apply (integrable_prod_iff ((measurable_chartValue h p).sub
    (measurable_chartValue k q)).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun b => by
      change Integrable (fun z => half (if b then h+p else h-p) z-
        half (if b then k+q else k-q) z) volume
      exact integrable_sub_half _ _
  · exact memLp_one_iff_integrable.mp MemLp.of_discrete

lemma integrable_chart_difference (h p k q : ℝ) :
    Integrable (fun z => chartValue h p z-chartValue k q z) labelMeasure := by
  change Integrable _ ((1/2 : ℝ≥0∞) • (Measure.count.prod volume))
  exact (integrable_chart_difference_count h p k q).smul_measure (by norm_num)

lemma chart_distance (h p k q : ℝ) :
    (∫ z, |chartValue h p z-chartValue k q z| ∂labelMeasure) = max |h-k| |p-q| := by
  rw [labelMeasure,integral_smul_measure]
  have he : (∫ z : Bool × ℝ, |chartValue h p z-chartValue k q z| ∂Measure.count.prod volume) =
      |(h+p)-(k+q)|+|(h-p)-(k-q)| := by
    rw [integral_prod _ ((integrable_chart_difference_count h p k q).norm.congr
      (Filter.Eventually.of_forall fun _ => Real.norm_eq_abs _))]
    simp only [chartValue,integral_count]
    rw [Fintype.sum_bool]
    simp only [ite_true,Bool.false_eq_true,ite_false,integral_abs_sub_half]
  rw [he]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  rw [show h+p-(k+q) = (h-k)+(p-q) by ring,
    show h-p-(k-q) = (h-k)-(p-q) by ring]
  nlinarith [two_sign_abs (h-k) (p-q)]

lemma chart_vertical (h p k q : ℝ) (hv : |p-q| ≤ |h-k|) :
    (∫ z, |chartValue h p z-chartValue k q z| ∂labelMeasure) = |h-k| := by
  rw [chart_distance,max_eq_left hv]

lemma chart_movement (h p q : ℝ) :
    (∫ z, |chartValue h p z-chartValue h q z| ∂labelMeasure) = |p-q| := by
  rw [chart_distance,sub_self,abs_zero,max_eq_right (abs_nonneg _)]

noncomputable def rebase (ep em : ℝ ≃o ℝ) (z : Bool × ℝ) : ℝ :=
  (if z.1 then ep else em).symm z.2

lemma measurable_rebase (ep em : ℝ ≃o ℝ) : Measurable (rebase ep em) := by
  apply measurable_from_prod_countable_right
  intro b
  exact (if b then ep else em).symm.continuous.measurable

lemma rebase_preimage_Ioc (ep em : ℝ ≃o ℝ) (a b : ℝ) (σ : Bool) :
    Prod.mk σ ⁻¹' (rebase ep em ⁻¹' Set.Ioc a b) =
      Set.Ioc ((if σ then ep else em) a) ((if σ then ep else em) b) := by
  change (if σ then ep else em).symm ⁻¹' Set.Ioc a b = _
  rw [OrderIso.preimage_Ioc]
  rfl

/-- Rebasing is measure preserving AFTER averaging the old sign. It does not
claim that either conditional change of variable preserves Lebesgue measure. -/
lemma rebase_preserving (ep em : ℝ ≃o ℝ) (hmean : ∀ H, ep H+em H = 2*H) :
    MeasurePreserving (rebase ep em) labelMeasure volume := by
  refine ⟨measurable_rebase ep em, ?_⟩
  symm
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [Measure.map_apply (measurable_rebase ep em) measurableSet_Ioc,
    labelMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.prod_apply ((measurable_rebase ep em) measurableSet_Ioc)]
  simp_rw [rebase_preimage_Ioc,Real.volume_Ioc]
  rw [lintegral_count,tsum_fintype,Fintype.sum_bool]
  simp only [ite_true,Bool.false_eq_true,ite_false]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  have hp : 0 ≤ ep b-ep a := sub_nonneg.mpr (ep.monotone hab.le)
  have hm : 0 ≤ em b-em a := sub_nonneg.mpr (em.monotone hab.le)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal hm]
  linarith [hmean a,hmean b]

/-- Exact set equality, not merely equality in distribution. -/
lemma rebase_membership (ep em : ℝ ≃o ℝ) (H : ℝ) (z : Bool × ℝ) :
    z.2 < (if z.1 then ep else em) H ↔ rebase ep em z < H := by
  exact (if z.1 then ep else em).symm_apply_lt.symm

end PlanarL1.Threshold


end

section

namespace PlanarL1.Threshold
open MeasureTheory
open scoped NNReal

lemma threshold_mono {K : ℝ≥0} (hK : (K:ℝ) ≤ 1) {P : ℝ → ℝ}
    (hP : LipschitzWith K P) (b : Bool) :
    Monotone (fun H => if b then H+P H else H-P H) := by
  intro s t hst
  have h := hP.dist_le_mul s t
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst)] at h
  have hm := mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr hst)
  have hp := abs_le.mp h
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith

variable {n : ℕ} {M : Columns.Model n} {K : ℝ≥0}

noncomputable def chartActivity (F : M.Field Set.univ K) (hK : (K:ℝ) ≤ 1)
    (z : Bool × ℝ) : Columns.Model.Activity M where
  active i H := z.2 < if z.1 then H+F.value i ⟨H,Set.mem_univ H⟩
      else H-F.value i ⟨H,Set.mem_univ H⟩
  increasing i s t hst ha := by
    apply ha.trans_le
    apply threshold_mono hK _ z.1 hst
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (F.vertical i).dist_le_mul ⟨x,Set.mem_univ x⟩ ⟨y,Set.mem_univ y⟩
  switch i j H hH := by rw [F.switch i j ⟨H,Set.mem_univ H⟩ hH]

lemma chartIndicator (F : M.Field Set.univ K) (hK : (K:ℝ) ≤ 1)
    (z : Bool × ℝ) (i : Fin n) (H : ℝ) :
    (chartActivity F hK z).indicator i H = chartValue H (F.value i ⟨H,Set.mem_univ H⟩) z := rfl

noncomputable def chartSystem (F : M.Field Set.univ K) (hK : (K:ℝ) ≤ 1) :
    Columns.Model.SetSystem M (Bool × ℝ) labelMeasure where
  activity := chartActivity F hK
  measurable_active i H := by
    change MeasurableSet {z : Bool × ℝ | z.2 < if z.1 then
      H+F.value i ⟨H,Set.mem_univ H⟩ else H-F.value i ⟨H,Set.mem_univ H⟩}
    apply measurableSet_lt measurable_snd
    exact Measurable.ite (measurableSet_singleton true |>.preimage measurable_fst)
      measurable_const measurable_const
  vertical_integrable i s t := by
    simp only [chartIndicator]
    exact (integrable_chart_difference _ _ _ _).norm
  vertical_bound i s t := by
    simp only [chartIndicator]
    have h := (F.vertical i).dist_le_mul ⟨s,Set.mem_univ s⟩ ⟨t,Set.mem_univ t⟩
    rw [Real.dist_eq,Subtype.dist_eq,Real.dist_eq] at h
    have hb := h.trans (by simpa using mul_le_mul_of_nonneg_right hK (abs_nonneg (s-t)))
    exact (chart_vertical _ _ _ _ hb).le

/-- Rebasing a genuine strict Lipschitz height branch, with no differentiability
assumption. The old sign is averaged; its conditional laws are not asserted
Lebesgue preserving. -/
noncomputable def branchRebase {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) : Bool × ℝ → ℝ :=
  rebase (Rebase.shear hK hψ) (Rebase.shear hK hψ.neg)

lemma branchRebase_preserving {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) : MeasurePreserving (branchRebase hK hψ) labelMeasure volume := by
  apply rebase_preserving
  intro H
  simp only [Rebase.shear_apply,Pi.neg_apply]
  ring

lemma branchRebase_membership {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (H : ℝ) (z : Bool × ℝ) :
    chartValue H (ψ H) z = half H (branchRebase hK hψ z) := by
  unfold chartValue half
  congr 1
  apply propext
  unfold branchRebase
  have h := rebase_membership (Rebase.shear hK hψ) (Rebase.shear hK hψ.neg) H z
  cases hb : z.1 <;> simpa only [hb,Bool.false_eq_true,ite_false,ite_true,
    Rebase.shear_apply,Pi.neg_apply,sub_eq_add_neg] using h

end PlanarL1.Threshold


end

section

namespace PlanarL1.Threshold
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def fair : Measure Bool := (1/2 : ℝ≥0∞) • Measure.count

instance fair_probability : IsProbabilityMeasure fair := by
  constructor
  norm_num [fair,Measure.smul_apply,smul_eq_mul,Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

lemma labelMeasure_eq : labelMeasure = fair.prod (volume : Measure ℝ) := by
  simp only [fair,Measure.prod_smul_left,labelMeasure]

/-- A chart's actual label variables, not hypothetical independent coordinates.
The preservation proof is exactly the joint Lebesgue/fair-sign invariant. -/
structure Variables (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  value : Ω → Bool × ℝ
  preserving : MeasurePreserving value μ labelMeasure

namespace Variables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def initial : Variables (Bool × ℝ) labelMeasure :=
  ⟨id,MeasurePreserving.id labelMeasure⟩

noncomputable def lift (Z : Variables Ω μ) : Variables (Ω × Bool) (μ.prod fair) where
  value z := Z.value z.1
  preserving := Z.preserving.comp (measurePreserving_fst (μ := μ) (ν := fair))

noncomputable def rebase {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (Z : Variables Ω μ) [SFinite μ] :
    Variables (Ω × Bool) (μ.prod fair) where
  value z := (z.2,branchRebase hK hψ (Z.value z.1))
  preserving := by
    have hZ := (branchRebase_preserving hK hψ).comp Z.preserving
    have hp := hZ.prod (MeasurePreserving.id fair)
    have hs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := fair)).comp hp
    convert hs using 1
    · funext z
      rfl
    · exact labelMeasure_eq

lemma rebase_membership {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (Z : Variables Ω μ) [SFinite μ] (H : ℝ) (z : Ω × Bool) :
    chartValue H (ψ H) ((Z.lift).value z) =
      chartValue H 0 ((Z.rebase hK hψ).value z) := by
  change chartValue H (ψ H) (Z.value z.1) = _
  rw [branchRebase_membership hK hψ H (Z.value z.1)]
  change half H (branchRebase hK hψ (Z.value z.1)) =
    half (if z.2 then H+0 else H-0) (branchRebase hK hψ (Z.value z.1))
  simp

lemma integrable_difference (Z : Variables Ω μ) (h p k q : ℝ) :
    Integrable (fun z => chartValue h p (Z.value z)-chartValue k q (Z.value z)) μ := by
  exact Z.preserving.integrable_comp_of_integrable
    (integrable_chart_difference h p k q)

lemma distance (Z : Variables Ω μ) (h p k q : ℝ) :
    (∫ z, |chartValue h p (Z.value z)-chartValue k q (Z.value z)| ∂μ) =
      max |h-k| |p-q| := by
  rw [← chart_distance h p k q]
  rw [← Z.preserving.map_eq]
  exact (integral_map_of_stronglyMeasurable Z.preserving.measurable
    (((measurable_chartValue h p).sub (measurable_chartValue k q)).norm.stronglyMeasurable)).symm

end Variables
end PlanarL1.Threshold



end

section

namespace PlanarL1.Threshold
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def active (Z : Variables Ω μ) (H P : ℝ) (ω : Ω) : Prop :=
  (Z.value ω).2 < if (Z.value ω).1 then H+P else H-P

lemma active_indicator (Z : Variables Ω μ) (H P : ℝ) (ω : Ω) :
    (if active Z H P ω then (1:ℝ) else 0) = chartValue H P (Z.value ω) := rfl

lemma measurable_active (Z : Variables Ω μ) (H P : ℝ) :
    MeasurableSet {ω | active Z H P ω} := by
  apply measurableSet_lt (measurable_snd.comp Z.preserving.measurable)
  exact Measurable.ite ((measurableSet_singleton true).preimage
    (measurable_fst.comp Z.preserving.measurable)) measurable_const measurable_const

lemma active_increasing (Z : Variables Ω μ) {S : Set ℝ} {P : ℝ → ℝ}
    (hP : LipschitzOnWith 1 P S) (ω : Ω) : MonotoneOn (fun H => active Z H (P H) ω) S := by
  intro s hs t ht hst ha
  have hb := hP.dist_le_mul s hs t ht
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst),NNReal.coe_one,one_mul] at hb
  have hp := abs_le.mp hb
  unfold active at ha ⊢
  apply ha.trans_le
  cases h : (Z.value ω).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith

end PlanarL1.Threshold

end

section

namespace PlanarL1.Threshold.Variables
open MeasureTheory
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma active_rebase [SFinite μ] {K : ℝ≥0} (hK : (K:ℝ)<1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (Z : Variables Ω μ) (H : ℝ) (ω : Ω × Bool) :
    active Z.lift H (ψ H) ω ↔ active (Z.rebase hK hψ) H 0 ω := by
  classical
  have he := Z.rebase_membership hK hψ H ω
  change (if active Z.lift H (ψ H) ω then (1:ℝ) else 0) =
    (if active (Z.rebase hK hψ) H 0 ω then 1 else 0) at he
  by_cases hp : active Z.lift H (ψ H) ω <;>
    by_cases hq : active (Z.rebase hK hψ) H 0 ω <;> simp_all
end PlanarL1.Threshold.Variables


end

section

namespace PlanarL1.Threshold
open MeasureTheory
attribute [local instance] Classical.propDecidable

lemma half_mono {a b : ℝ} (h : a ≤ b) (z : ℝ) : half a z ≤ half b z := by
  by_cases hz : z < a
  · simp [half,hz,hz.trans_le h]
  · simp only [half,ite_eq_right hz]
    split_ifs <;> norm_num

lemma integral_sub_half (a b : ℝ) : (∫ z, half a z-half b z) = a-b := by
  rcases le_total a b with h | h
  · have he : (fun z => half a z-half b z) = fun z => -|half a z-half b z| := by
      funext z
      rw [abs_of_nonpos (sub_nonpos.mpr (half_mono h z)),neg_neg]
    rw [he,integral_neg,integral_abs_sub_half,abs_of_nonpos (sub_nonpos.mpr h),neg_neg]
  · have he : (fun z => half a z-half b z) = fun z => |half a z-half b z| := by
      funext z
      rw [abs_of_nonneg (sub_nonneg.mpr (half_mono h z))]
    rw [he,integral_abs_sub_half,abs_of_nonneg (sub_nonneg.mpr h)]

lemma integral_chart_difference (h p k q : ℝ) :
    (∫ z, chartValue h p z-chartValue k q z ∂labelMeasure) = h-k := by
  rw [labelMeasure,integral_smul_measure]
  have he : (∫ z : Bool × ℝ, chartValue h p z-chartValue k q z ∂Measure.count.prod volume) =
      ((h+p)-(k+q))+((h-p)-(k-q)) := by
    rw [integral_prod _ (integrable_chart_difference_count h p k q)]
    simp only [chartValue,integral_count]
    rw [Fintype.sum_bool]
    simp only [ite_true,Bool.false_eq_true,ite_false,integral_sub_half]
  rw [he]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  ring

namespace Variables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma integral_difference (Z : Variables Ω μ) (h p k q : ℝ) :
    (∫ z, chartValue h p (Z.value z)-chartValue k q (Z.value z) ∂μ) = h-k := by
  rw [← integral_chart_difference h p k q,← Z.preserving.map_eq]
  exact (integral_map_of_stronglyMeasurable Z.preserving.measurable
    (((measurable_chartValue h p).sub (measurable_chartValue k q)).stronglyMeasurable)).symm
end Variables
end PlanarL1.Threshold


end

section

namespace PlanarL1.Threshold
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma threshold_compare (Z : Variables Ω μ) {s t p q : ℝ}
    (h : |p-q| ≤ t-s) (ω : Ω) : active Z s p ω → active Z t q ω := by
  intro hs
  apply hs.trans_le
  have hd := abs_le.mp h
  cases (Z.value ω).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith

/-- A genuine gluing lemma for regions with arbitrarily complicated boundaries.
Small distance-tapered changes preserve nesting even though the identifiers
may have infinitely many changes along a column. All fields below already
include κ. No regularity of the name function is assumed. -/
lemma named_nested (name : ℝ → ι) (Z : ι → Variables Ω μ)
    (old newer : ℝ → ℝ) (A : ℝ → Ω → Prop)
    (hA : ∀ ω, Monotone (fun H => A H ω))
    (hrep : ∀ H ω, A H ω ↔ active (Z (name H)) H (old H) ω)
    (hold : ∀ s t, name s=name t → |old s-old t| ≤ |s-t|/2)
    (hnew : ∀ s t, name s=name t → |newer s-newer t| ≤ |s-t|)
    (hd : ∀ s t, name s≠name t → |newer s-old s| ≤ |s-t|/8)
    (ω : Ω) : Monotone (fun H => active (Z (name H)) H (newer H) ω) := by
  intro s t hst hs
  by_cases he : name s=name t
  · have hb := hnew s t he
    rw [abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] at hb
    rw [← he]
    exact threshold_compare (Z (name s)) hb ω hs
  let ds := |newer s-old s|
  let dt := |newer t-old t|
  have hds : 0 ≤ ds := abs_nonneg _
  have hdt : 0 ≤ dt := abs_nonneg _
  have hsbound : ds ≤ (t-s)/8 := by
    simpa only [ds,abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] using hd s t he
  have htbound : dt ≤ (t-s)/8 := by
    simpa only [dt,abs_of_nonneg (sub_nonneg.mpr hst)] using hd t s (Ne.symm he)
  let u := s+2*ds
  let v := t-2*dt
  have hsu : s ≤ u := by dsimp [u]; linarith
  have hvt : v ≤ t := by dsimp [v]; linarith
  have huv : u ≤ v := by dsimp [u,v]; linarith
  have hnameu : name s=name u := by
    by_contra hno
    have hb := hd s u hno
    rw [abs_of_nonpos (sub_nonpos.mpr hsu),neg_sub] at hb
    change ds ≤ (u-s)/8 at hb
    have hz : ds=0 := by dsimp [u] at hb; linarith
    have hu : u=s := by simp [u,hz]
    exact hno (congrArg name hu.symm)
  have hnamev : name v=name t := by
    by_contra hno
    have hb := hd t v (Ne.symm hno)
    rw [abs_of_nonneg (sub_nonneg.mpr hvt)] at hb
    change dt ≤ (t-v)/8 at hb
    have hz : dt=0 := by dsimp [v] at hb; linarith
    have hv : v=t := by simp [v,hz]
    exact hno (congrArg name hv)
  have hu : A u ω := by
    rw [hrep,← hnameu]
    apply threshold_compare (Z (name s)) (ω := ω) _ hs
    calc
      |newer s-old u| ≤ |newer s-old s|+|old s-old u| := abs_sub_le _ _ _
      _ ≤ ds+|s-u|/2 := add_le_add le_rfl (hold s u hnameu)
      _ = u-s := by rw [abs_of_nonpos (sub_nonpos.mpr hsu),neg_sub]; dsimp [u]; ring
  have hv : A v ω := hA ω huv hu
  rw [hrep,hnamev] at hv
  apply threshold_compare (Z (name t)) (ω := ω) _ hv
  calc
    |old v-newer t| ≤ |old v-old t|+|old t-newer t| := abs_sub_le _ _ _
    _ ≤ |v-t|/2+dt := by
      simpa only [dt,abs_sub_comm (old t)] using add_le_add (hold v t hnamev) (le_rfl : |old t-newer t| ≤ |old t-newer t|)
    _ = t-v := by rw [abs_of_nonpos (sub_nonpos.mpr hvt),neg_sub]; dsimp [v]; ring

end PlanarL1.Threshold



end

end OAI
