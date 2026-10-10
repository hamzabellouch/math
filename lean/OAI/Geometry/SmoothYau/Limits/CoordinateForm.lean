import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev CoordinateForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ

local instance dualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance dualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance formNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance formSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

def quadraticPlaneStrict (T : CoordinateForm E) (q : E) : Prop :=
  ∃ v, ‖v‖ = 1 ∧ inner ℝ q v = 0 ∧ 0 < T v v

def quadraticPlaneFull (T : CoordinateForm E) (q : E) : Prop :=
  ∀ v, ‖v‖ = 1 → inner ℝ q v = 0 → 0 < T v v

def metricProfileTraceForm (B H : CoordinateForm E) (a : E) : CoordinateForm E :=
  (H a a) • B + (1+B a a) • H

omit [FiniteDimensional ℝ E] in
lemma metricProfileTraceForm_apply (B H : CoordinateForm E) (a v : E) :
    metricProfileTraceForm B H a v v = B v v*H a a+(1+B a a)*H v v := by
  simp only [metricProfileTraceForm,add_apply,smul_apply,smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
lemma continuous_metricProfileTraceForm : Continuous
    (fun p : (CoordinateForm E × CoordinateForm E) × E => metricProfileTraceForm p.1.1 p.1.2 p.2) := by
  have hB : Continuous (fun p : (CoordinateForm E × CoordinateForm E) × E => p.1.1) := continuous_fst.fst
  have hH : Continuous (fun p : (CoordinateForm E × CoordinateForm E) × E => p.1.2) := continuous_fst.snd
  have ha : Continuous (fun p : (CoordinateForm E × CoordinateForm E) × E => p.2) := continuous_snd
  exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
    ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

omit [FiniteDimensional ℝ E] in

theorem quadraticPlaneStrict_eventually {H : CoordinateForm E} {a : E} (ha : a ≠ 0)
    (hs : quadraticPlaneStrict H a) : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), quadraticPlaneStrict p.1 p.2 := by
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w : CoordinateForm E × E → E := fun p => v - (inner ℝ p.2 v / ‖p.2‖ ^ 2) • p.2
  have han : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hsnd : Continuous (fun p : CoordinateForm E × E => p.2) := continuous_snd
  have hw : ContinuousAt w (H,a) := by
    exact continuousAt_const.sub (((hsnd.inner continuous_const).continuousAt.div
      (hsnd.norm.pow 2).continuousAt han).smul hsnd.continuousAt)
  have hwa : w (H,a) = v := by simp [w,hav]
  let z : CoordinateForm E × E → E := fun p => ‖w p‖⁻¹ • w p
  have hz : ContinuousAt z (H,a) :=
    (hw.norm.inv₀ (by rw [hwa,hv]; norm_num)).smul hw
  have hza : z (H,a) = v := by simp [z,hwa,hv]
  have hp : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), 0 < p.1 (z p) (z p) := by
    have hc : ContinuousAt (fun p : CoordinateForm E × E => p.1 (z p) (z p)) (H,a) :=
      (continuousAt_fst.clm_apply hz).clm_apply hz
    apply hc.eventually (Ioi_mem_nhds ?_)
    simpa [hza] using hpos
  have hane : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), p.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually_ne ha
  have hwne : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), w p ≠ 0 :=
    hw.eventually_ne (by rw [hwa]; exact norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  filter_upwards [hp,hane,hwne] with p hp hpa hpw
  refine ⟨z p,?_,?_,hp⟩
  · simp [z,norm_smul,norm_ne_zero_iff.mpr hpw]
  · have hpn : ‖p.2‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hpa)
    have hwperp : inner ℝ p.2 (w p) = 0 := by
      simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    simp [z,inner_smul_right,hwperp]

theorem isOpen_quadraticPlaneFull : IsOpen {p : CoordinateForm E × E | quadraticPlaneFull p.1 p.2} := by
  let S : Set E := sphere 0 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let B : Set ((CoordinateForm E × E) × S) := {p | inner ℝ p.1.2 (p.2 : E) = 0 ∧
    p.1.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : ((CoordinateForm E × E) × S) => p.1.1) := continuous_fst.fst
  have hv : Continuous (fun p : ((CoordinateForm E × E) × S) => (p.2 : E)) := continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.snd.inner (continuous_subtype_val.comp continuous_snd)) continuous_const
    · exact isClosed_le
        ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, B]
  constructor
  · intro hp
    rintro ⟨y,hy,hyp⟩
    subst p
    exact (not_le_of_gt (hp y.2 (by simpa only [S, mem_sphere_zero_iff_norm] using y.2.property) hy.1)) hy.2
  · intro hp v hv hav
    by_contra hh
    apply hp
    exact ⟨(p,⟨v,by simpa [S,mem_sphere_zero_iff_norm] using hv⟩),⟨hav,not_lt.mp hh⟩,rfl⟩

theorem compact_quadraticPlaneFull_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (T : X → CoordinateForm E) (q : X → E)
    (hT : Continuous T) (hq : Continuous q)
    (hfull : ∀ x ∈ K, quadraticPlaneFull (T x) (q x)) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v, inner ℝ (q x) v = 0 →
      m*‖v‖^2 ≤ T x v v := by
  let S : Set (X × E) := {p | p.1 ∈ K ∧ ‖p.2‖ = 1 ∧ inner ℝ (q p.1) p.2 = 0}
  have hS : IsCompact S := by
    have heq : S = (K ×ˢ sphere (0 : E) 1) ∩ {p | inner ℝ (q p.1) p.2 = 0} := by
      ext p
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_sphere_zero_iff_norm]
      tauto
    rw [heq]
    exact (hK.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq ((hq.comp continuous_fst).inner continuous_snd) continuous_const)
  have hc : Continuous (fun p : X × E => T p.1 p.2 p.2) :=
    ((hT.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v, ‖v‖ = 1 →
      inner ℝ (q x) v = 0 → m ≤ T x v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
      exact ⟨T p.1 p.2 p.2,hfull p.1 hp.1 p.2 hp.2.1 hp.2.2,
        fun x hx v hv hav => hmin (show (x,v) ∈ S from ⟨hx,hv,hav⟩)⟩
    · exact ⟨1,zero_lt_one,fun x hx v hv hav => (hne ⟨(x,v),hx,hv,hav⟩).elim⟩
  obtain ⟨m,hm,hml⟩ := hm
  refine ⟨m,hm,?_⟩
  intro x hx v hav
  by_cases hv : v = 0
  · simp [hv]
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hvn]
  have hqw : inner ℝ (q x) w = 0 := by simp [w,inner_smul_right,hav]
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hvn]
  have heq : T x v v = ‖v‖^2 * T x w w := by
    conv_lhs => rw [←hvw]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [heq,mul_comm m]
  exact mul_le_mul_of_nonneg_left (hml x hx w hw hqw) (sq_nonneg _)

theorem compact_variableMetric_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (B T : X → CoordinateForm E) (q : X → E)
    (hB : Continuous B) (hT : Continuous T) (hq : Continuous q)
    (hfull : ∀ x ∈ K, quadraticPlaneFull (T x) (q x)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, ∀ v,
      B x v v = 1 → inner ℝ (q x) v = 0 → m ≤ T x v v := by
  obtain ⟨m,hm,hml⟩ := compact_quadraticPlaneFull_margin hK T q hT hq hfull
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hB.continuousOn
  let C' := max C 1
  have hCp : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨min (m/C') 1,lt_min (div_pos hm hCp) zero_lt_one,min_le_right _ _,?_⟩
  intro x hx v hv hav
  have hbound : 1 ≤ C'*‖v‖^2 := by
    calc
      1 = |B x v v| := by rw [hv,abs_one]
      _ ≤ ‖B x‖*‖v‖*‖v‖ := (B x).le_opNorm₂ v v
      _ ≤ C'*‖v‖^2 := by
        have hh := mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left C 1)) (sq_nonneg ‖v‖)
        nlinarith only [hh]
  calc
    min (m/C') 1 ≤ m/C' := min_le_left _ _
    _ ≤ m*‖v‖^2 := (div_le_iff₀ hCp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hbound hm.le])
    _ ≤ T x v v := hml x hx v hav

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneFull_pos {T : CoordinateForm E} {q v : E}
    (h : quadraticPlaneFull T q) (hv : v ≠ 0) (hqv : inner ℝ q v = 0) : 0 < T v v := by
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hvn]
  have hqw : inner ℝ q w = 0 := by simp [w,inner_smul_right,hqv]
  have hp := h w hw hqw
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hvn]
  have heq : T v v = ‖v‖^2 * T w w := by
    conv_lhs => rw [←hvw]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [heq]
  exact mul_pos (sq_pos_of_ne_zero hvn) hp

local instance planeMapNorm : NormedAddCommGroup (E →L[ℝ] (ℝ × ℝ)) := inferInstance
local instance planeMapSpace : NormedSpace ℝ (E →L[ℝ] (ℝ × ℝ)) := inferInstance

def twoCoframeForm (D : E →L[ℝ] (ℝ × ℝ)) : CoordinateForm E :=
  let l := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp D
  let r := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp D
  l.smulRight l + r.smulRight r

omit [FiniteDimensional ℝ E] in
lemma twoCoframeForm_apply (D : E →L[ℝ] (ℝ × ℝ)) (v : E) :
    twoCoframeForm D v v = (D v).1^2+(D v).2^2 := by
  change (D v).1*(D v).1+(D v).2*(D v).2 = _
  ring

omit [FiniteDimensional ℝ E] in
lemma continuous_twoCoframeForm : Continuous (twoCoframeForm :
    (E →L[ℝ] (ℝ × ℝ)) → CoordinateForm E) := by
  have hl : Continuous (fun D : E →L[ℝ] (ℝ × ℝ) => (ContinuousLinearMap.fst ℝ ℝ ℝ).comp D) :=
    continuous_const.clm_comp continuous_id
  have hr : Continuous (fun D : E →L[ℝ] (ℝ × ℝ) => (ContinuousLinearMap.snd ℝ ℝ ℝ).comp D) :=
    continuous_const.clm_comp continuous_id
  exact ((isBoundedBilinearMap_smulRight.continuous).comp (hl.prodMk hl)).add
    ((isBoundedBilinearMap_smulRight.continuous).comp (hr.prodMk hr))

def scaledSubForm (B C : CoordinateForm E) : CoordinateForm E := (4:ℝ) • B - C

omit [FiniteDimensional ℝ E] in
lemma scaledSubForm_apply (B C : CoordinateForm E) (v : E) :
    scaledSubForm B C v v = 4*B v v-C v v := by
  simp only [scaledSubForm,sub_apply,smul_apply,smul_eq_mul]

omit [FiniteDimensional ℝ E] in
lemma continuousAt_scaledSubForm {X : Type*} [TopologicalSpace X]
    {B C : X → CoordinateForm E} {p : X} (hB : ContinuousAt B p) (hC : ContinuousAt C p) :
    ContinuousAt (fun x => scaledSubForm (B x) (C x)) p :=
  (hB.const_smul (4:ℝ)).sub hC

theorem twoCoframe_bounds_eventually {X : Type*} [TopologicalSpace X]
    (B : X → CoordinateForm E) (q : X → E) (D : X → E →L[ℝ] (ℝ × ℝ)) {p : X}
    (hB : ContinuousAt B p) (hq : ContinuousAt q p) (hD : ContinuousAt D p)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B p v v)
    (hup : ∀ v, twoCoframeForm (D p) v v ≤ B p v v)
    (heq : ∀ v, inner ℝ (q p) v = 0 → twoCoframeForm (D p) v v = B p v v) :
    ∀ᶠ x in 𝓝 p, (∀ v, twoCoframeForm (D x) v v ≤ 4*B x v v) ∧
      ∀ v, inner ℝ (q x) v = 0 → B x v v ≤ 4*twoCoframeForm (D x) v v := by
  let U : X → CoordinateForm E := fun x => scaledSubForm (B x) (twoCoframeForm (D x))
  let L : X → CoordinateForm E := fun x => scaledSubForm (twoCoframeForm (D x)) (B x)
  have hUc : ContinuousAt U p := continuousAt_scaledSubForm hB (continuous_twoCoframeForm.continuousAt.comp hD)
  have hLc : ContinuousAt L p := continuousAt_scaledSubForm (continuous_twoCoframeForm.continuousAt.comp hD) hB
  have hUf : quadraticPlaneFull (U p) (0:E) := by
    intro v hv _
    have hp := hpos v (norm_ne_zero_iff.mp (by rw [hv]; norm_num))
    dsimp only [U]
    rw [scaledSubForm_apply]
    linarith [hup v]
  have hLf : quadraticPlaneFull (L p) (q p) := by
    intro v hv hqv
    have hp := hpos v (norm_ne_zero_iff.mp (by rw [hv]; norm_num))
    dsimp only [L]
    rw [scaledSubForm_apply]
    rw [heq v hqv]
    linarith
  have hUe : ∀ᶠ x in 𝓝 p, quadraticPlaneFull (U x) (0:E) :=
    (hUc.prodMk continuousAt_const).eventually (isOpen_quadraticPlaneFull.mem_nhds hUf)
  have hLe : ∀ᶠ x in 𝓝 p, quadraticPlaneFull (L x) (q x) :=
    (hLc.prodMk hq).eventually (isOpen_quadraticPlaneFull.mem_nhds hLf)
  filter_upwards [hUe,hLe] with x hUx hLx
  constructor
  · intro v
    by_cases hv : v = 0
    · simp [hv]
    have hh := quadraticPlaneFull_pos hUx hv (by simp)
    dsimp only [U] at hh
    rw [scaledSubForm_apply] at hh
    linarith
  · intro v hqv
    by_cases hv : v = 0
    · simp [hv]
    have hh := quadraticPlaneFull_pos hLx hv hqv
    dsimp only [L] at hh
    rw [scaledSubForm_apply] at hh
    linarith

end YauCounterexamples

end

end OAI
