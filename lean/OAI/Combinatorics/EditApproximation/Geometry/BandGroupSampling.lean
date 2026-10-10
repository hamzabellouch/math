import OAI.Combinatorics.EditApproximation.Geometry.UnskippedBands
import OAI.Combinatorics.EditApproximation.Geometry.GroupSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem integerClosedRange_mem (lo hi value : ℤ) :
    value ∈ integerClosedRange lo hi ↔ lo ≤ value ∧ value ≤ hi := by
  constructor
  · intro h
    obtain ⟨i, hi', hequal⟩ := List.mem_map.mp h
    have hrange := List.mem_range.mp hi'
    omega
  · rintro ⟨hlower, hupper⟩
    apply List.mem_map.mpr
    refine ⟨(value - lo).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

theorem integerClosedRange_nodup (lo hi : ℤ) : (integerClosedRange lo hi).Nodup := by
  apply List.Nodup.map _ (List.nodup_range)
  intro i j hequal
  change lo + (i : ℤ) = lo + (j : ℤ) at hequal
  omega



theorem groupDyadicScales_mem {M b : ℕ} (hM : 0 < M) (hb : 0 < b)
    (F : ℚ) (hF : 0 < F) (exponent : ℤ) :
    (2 : ℚ) ^ exponent ∈ groupDyadicScales M b F ↔
      (b : ℚ) / M ≤ (2 : ℚ) ^ exponent ∧ (2 : ℚ) ^ exponent ≤ 64 * F * b := by
  have hlower : (0 : ℚ) < (b : ℚ) / M := by positivity
  have hupper : (0 : ℚ) < 64 * F * b := by positivity
  constructor
  · intro h
    obtain ⟨other, hother, hequal⟩ := List.mem_map.mp h
    have hsame : other = exponent :=
      zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1) hequal
    subst other
    have hrange := (integerClosedRange_mem _ _ _).mp hother
    exact ⟨(Int.le_zpow_iff_clog_le (by decide : 1 < 2) hlower).mpr hrange.1,
      (Int.zpow_le_iff_le_log (by decide : 1 < 2) hupper).mpr hrange.2⟩
  · rintro ⟨hlow, hhigh⟩
    apply List.mem_map.mpr
    refine ⟨exponent, (integerClosedRange_mem _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
    · exact (Int.le_zpow_iff_clog_le (by decide : 1 < 2) hlower).mp hlow
    · exact (Int.zpow_le_iff_le_log (by decide : 1 < 2) hupper).mp hhigh

theorem groupDyadicScales_nodup (M b : ℕ) (F : ℚ) : (groupDyadicScales M b F).Nodup := by
  exact (integerClosedRange_nodup _ _).map
    (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1))

theorem groupDyadicScales_pos {M b : ℕ} {F h : ℚ}
    (hh : h ∈ groupDyadicScales M b F) : 0 < h := by
  obtain ⟨exponent, _, rfl⟩ := List.mem_map.mp hh
  positivity



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

theorem groupSampleCount_pos {M Q b : ℕ} {h : ℚ}
    (hM : 0 < M) (hQ : 0 < Q) (hb : 0 < b) (hh : 0 < h) :
    0 < groupSampleCount M Q b h := by
  exact lt_min hM (Nat.ceil_pos.mpr (by positivity))

theorem groupSampleCount_sampled {M Q b : ℕ} {h : ℚ}
    (hsampled : groupSampleCount M Q b h < M) :
    (Q : ℚ) * M * h / b ≤ groupSampleCount M Q b h := by
  have hceil : groupSampleCount M Q b h = ⌈(Q : ℚ) * M * h / b⌉₊ := by
    unfold groupSampleCount at hsampled ⊢
    omega
  rw [hceil]
  exact Nat.le_ceil _





theorem groupScaleEstimate_exact {M : ℕ} (h : ℚ) (envelope value : Fin M → ℚ)
    (draw : Fin M → Fin M) : groupScaleEstimate M h envelope value draw = groupScaleTrueCost h envelope value := by
  simp only [groupScaleEstimate, ↓reduceIte]

/-- The sample and actual scale cost have exactly the normalized average
used in the published Bernstein specialization. -/
theorem groupScaleEstimate_normalized {M b k : ℕ} (h : ℚ)
    (envelope value : Fin M → ℚ) (draw : Fin k → Fin M)
    (hM : 0 < M) (hb : 0 < b) (hk : 0 < k) (hsampled : k ≠ M) :
    ((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ) =
      (b : ℝ) * ((∑ j, normalizedChildSample (b : ℝ) (h : ℝ)
        (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ)) (draw j)) / k -
          uniformMean (normalizedChildSample (b : ℝ) (h : ℝ)
            (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ)))) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hcast (i : Fin M) : normalizedChildSample (b : ℝ) (h : ℝ)
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ)) i =
        (M : ℝ) / b * ((if envelope i = h then value i else 0 : ℚ) : ℝ) := by
    by_cases hequal : envelope i = h
    · simp only [normalizedChildSample, hequal, ↓reduceIte]
      ring
    · have hequalR : (envelope i : ℝ) ≠ (h : ℝ) := by exact_mod_cast hequal
      simp only [normalizedChildSample, hequal, hequalR, ↓reduceIte, Rat.cast_zero, mul_zero]
  unfold uniformMean
  simp_rw [hcast]
  simp only [groupScaleEstimate, hsampled, ↓reduceIte, groupScaleTrueCost,
    Fintype.card_fin, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_sum]
  rw [← mul_sum, ← mul_sum]
  field_simp

/-- Fixed ordered minimization; negating the rational estimate turns the
finite maximum operation into the first cost minimum. -/


theorem selectGroupMember_spec {ι : Type*} (members : List ι) (hnonempty : members ≠ [])
    (estimate : ι → ℚ) :
    selectGroupMember members hnonempty estimate ∈ members ∧
      ∀ member ∈ members, estimate (selectGroupMember members hnonempty estimate) ≤ estimate member := by
  unfold selectGroupMember
  cases harg : members.argmax (fun member => -estimate member) with
  | none => exact False.elim (hnonempty (List.argmax_eq_none.mp harg))
  | some selected =>
    simp only [Option.getD_some]
    have hmem : selected ∈ members.argmax (fun member => -estimate member) := by rw [harg]; simp
    refine ⟨List.argmax_mem hmem, ?_⟩
    intro member hmember
    have h := List.le_of_mem_argmax (f := fun member => -estimate member) hmember hmem
    linarith

theorem groupScaleEstimate_concentration {M Q b k : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hQ : 0 < Q) (hb : 0 < b) (h F deviation : ℚ)
    (hh : 0 < h) (hF : 0 < F) (hdev : 0 < deviation)
    (envelope value : Fin M → ℚ)
    (henvelope : ∀ i, 0 ≤ envelope i)
    (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ 2 * envelope i)
    (hsum : (∑ i, envelope i) ≤ 64 * F * b)
    (hcount : k = groupSampleCount M Q b h)
    (bernstein : FiniteBernsteinInput
      (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure).real
      {draw | (deviation : ℝ) * b ≤
        |((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)|} ≤
      2 * Real.exp (-(Q : ℝ) * (deviation : ℝ) ^ 2 /
        (512 * (F : ℝ) + (4 / 3 : ℝ) * deviation)) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hdevr : (0 : ℝ) < deviation := by exact_mod_cast hdev
  by_cases hexact : k = M
  · have hempty : {draw : Fin k → Fin M | (deviation : ℝ) * b ≤
        |((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)|} = ∅ := by
      ext draw
      simp only [groupScaleEstimate, hexact, ↓reduceIte, sub_self, Rat.cast_zero, abs_zero,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (mul_pos hdevr hbr)
    rw [hempty, measureReal_empty]
    positivity
  · have hsampled : groupSampleCount M Q b h < M := by
      have hle : groupSampleCount M Q b h ≤ M := min_le_left _ _
      omega
    have hk : 0 < k := hcount ▸ groupSampleCount_pos hM hQ hb hh
    let sample := normalizedChildSample (b : ℝ) (h : ℝ)
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ))
    have hmoments := normalizedChildSample_moments hM (b : ℝ) (h : ℝ) (F : ℝ) hbr hhr
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ))
      (fun i => by exact_mod_cast henvelope i)
      (fun i => by exact_mod_cast hvalue i) (by exact_mod_cast hsum)
    have hsamples : (Q : ℝ) * ((M : ℝ) * (h : ℝ) / b) ≤ k := by
      have hsampleLower := groupSampleCount_sampled hsampled
      rw [← hcount] at hsampleLower
      have hcast : (Q : ℝ) * M * (h : ℝ) / b ≤ k := by exact_mod_cast hsampleLower
      convert hcast using 1
      ring
    have htail := group_scale_concentration k hk sample ((M : ℝ) * (h : ℝ) / b)
      (F : ℝ) (Q : ℝ) (deviation : ℝ) (by positivity) hFr hdevr
      hmoments.1 hmoments.2 hsamples bernstein
    have hevent : {draw : Fin k → Fin M | (deviation : ℝ) * b ≤
        |((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)|} =
        {draw | (deviation : ℝ) ≤ |(∑ j, sample (draw j)) / k - uniformMean sample|} := by
      ext draw
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        groupScaleEstimate_normalized h envelope value draw hM hb hk hexact,
        abs_mul, abs_of_pos hbr, mul_comm (deviation : ℝ) (b : ℝ)]
      exact mul_le_mul_iff_right₀ hbr
    rw [hevent]
    exact htail

noncomputable def groupSharedDrawLaw {M T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] (count : Fin T → ℕ) :
    Measure (∀ scale : Fin T, Fin (count scale) → Fin M) :=
  Measure.pi fun scale : Fin T =>
    Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure

instance groupSharedDrawLaw_isProbabilityMeasure {M T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (count : Fin T → ℕ) :
    IsProbabilityMeasure (groupSharedDrawLaw (M := M) count) := by
  unfold groupSharedDrawLaw
  infer_instance

theorem groupSharedDraw_projection {M T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin T → ℕ) (scale : Fin T) (bad : Set (Fin (count scale) → Fin M)) :
    (groupSharedDrawLaw count).real {draw | draw scale ∈ bad} =
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure).real bad := by
  let ν (scale : Fin T) :=
    Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure
  have hmap := (measurePreserving_eval (μ := ν) scale).map_eq
  have hpreimage := Measure.map_apply (μ := Measure.pi ν) (measurable_pi_apply scale)
    (Set.toFinite bad).measurableSet
  rw [hmap] at hpreimage
  exact congrArg ENNReal.toReal hpreimage.symm

/-- Actual shared draws are reused for all group members at this scale;
no independence between representatives is imposed. -/


theorem selectGroupMember_cost_le {ι : Type*} (members : List ι) (hnonempty : members ≠ [])
    (cost estimate : ι → ℚ) (specified : ι) (hspecified : specified ∈ members) (error : ℚ)
    (haccurate : ∀ member ∈ members, |estimate member - cost member| ≤ error) :
    cost (selectGroupMember members hnonempty estimate) ≤ cost specified + 2 * error := by
  classical
  have hspec := selectGroupMember_spec members hnonempty estimate
  have hreal := selected_group_cost_le members.toFinset (fun member => (cost member : ℝ))
    (fun member => (estimate member : ℝ)) (selectGroupMember members hnonempty estimate) specified (error : ℝ)
    (by simpa only [List.mem_toFinset] using hspec.1)
    (by simpa only [List.mem_toFinset] using hspecified)
    (fun member hmember => by exact_mod_cast haccurate member (List.mem_toFinset.mp hmember))
    (by exact_mod_cast hspec.2 specified hspecified)
  exact_mod_cast hreal

theorem groupScaleTrueCost_sum {M T : ℕ} (scales : Fin T → ℚ)
    (hinjective : Function.Injective scales) (envelope value : Fin M → ℚ)
    (hcover : ∀ i, ∃ scale, scales scale = envelope i) :
    (∑ scale, groupScaleTrueCost (scales scale) envelope value) = ∑ i, value i := by
  unfold groupScaleTrueCost
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  obtain ⟨scale, hscale⟩ := hcover i
  have h : (∑ other : Fin T, if scales scale = scales other then value i else 0) = value i := by
    simp only [hinjective.eq_iff, sum_ite_eq, mem_univ, ↓reduceIte]
  simpa only [hscale] using h

theorem uniform_sample_average_integral {M k : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hk : 0 < k) (value : Fin M → ℝ) :
    (∫ draw, (∑ j : Fin k, value (draw j)) / k
      ∂Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure)) = uniformMean value := by
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [integral_div, integral_finsetSum univ (by intro j hj; exact .of_finite)]
  have hpoint (j : Fin k) :
      (∫ draw, value (draw j)
        ∂Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure)) = uniformMean value := by
    rw [integral_comp_eval (μ := fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure)
      (i := j) (f := value) (measurable_of_finite _).aestronglyMeasurable, uniform_integral]
  simp_rw [hpoint]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem groupScaleEstimate_integral {M b k : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (h : ℚ) (envelope value : Fin M → ℚ) (hM : 0 < M) (hb : 0 < b) (hk : 0 < k) :
    (∫ draw, (groupScaleEstimate k h envelope value draw : ℝ)
      ∂Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure)) =
      (groupScaleTrueCost h envelope value : ℝ) := by
  let μ := Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure
  by_cases hexact : k = M
  · simp only [groupScaleEstimate, hexact, ↓reduceIte, integral_const, probReal_univ, one_smul]
  · let sample := normalizedChildSample (b : ℝ) (h : ℝ)
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ))
    have herror : (∫ draw, ((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)
        ∂μ) = 0 := by
      simp_rw [groupScaleEstimate_normalized h envelope value _ hM hb hk hexact]
      rw [integral_const_mul, integral_sub (.of_finite) (integrable_const _),
        uniform_sample_average_integral hk, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
    simp only [Rat.cast_sub] at herror
    rw [integral_sub (.of_finite) (integrable_const _), integral_const, probReal_univ, one_smul] at herror
    linarith

theorem groupMemberEstimate_error {M T : ℕ} (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (hinjective : Function.Injective scales) (connection : ℚ) (envelope value : Fin M → ℚ)
    (hcover : ∀ i, ∃ scale, scales scale = envelope i)
    (draw : ∀ scale : Fin T, Fin (count scale) → Fin M) (error : ℚ)
    (herror : ∀ scale, |groupScaleEstimate (count scale) (scales scale) envelope value (draw scale) -
        groupScaleTrueCost (scales scale) envelope value| ≤ error) :
    |groupMemberEstimate scales count connection envelope value draw - (connection + ∑ i, value i)| ≤
      T * error := by
  rw [← groupScaleTrueCost_sum scales hinjective envelope value hcover]
  unfold groupMemberEstimate
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hsum := sum_le_sum (s := univ) fun scale _ => herror scale
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

section ActualUnskippedGroup

variable {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
  {parent : TargetInterval source.length} {tau F : ℚ}
  {child initial : Fin M → TargetInterval target.length → ℚ}

theorem testUnskippedBand_accept
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial) :
    testUnskippedBand source target parent b P thetaExponent tau F child initial member.center = some member := by
  cases member with
  | mk center nonempty hsum hwide hgap =>
    simp only [testUnskippedBand, dite_eq_right nonempty, dite_eq_left hsum,
      dite_eq_left hwide, dite_eq_left hgap]

theorem testUnskippedBand_center
    (center : TargetInterval target.length)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (haccepted : testUnskippedBand source target parent b P thetaExponent tau F child initial center = some member) :
    member.center = center := by
  unfold testUnskippedBand at haccepted
  dsimp only at haccepted
  split_ifs at haccepted
  cases haccepted
  rfl

theorem unskippedBandList_mem_iff
    (centers : List (TargetInterval target.length))
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial) :
    member ∈ unskippedBandList source target parent b P thetaExponent tau F child initial centers ↔
      member.center ∈ centers := by
  constructor
  · intro hmember
    obtain ⟨center, hcenter, haccepted⟩ := List.mem_filterMap.mp hmember
    rwa [testUnskippedBand_center center member haccepted]
  · intro hcenter
    exact List.mem_filterMap.mpr ⟨member.center, hcenter, testUnskippedBand_accept member⟩

theorem unskippedBand_envelope_scale
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hM : 0 < M) (hb : 0 < b) (hF : 0 < F) (i : Fin M) :
    member.envelope i ∈ groupDyadicScales M b F := by
  have hlower := (bandChildEnvelope_lower b member.actions initial i).1
  change (b : ℚ) / M ≤ member.envelope i at hlower
  have hsingle : member.envelope i ≤ ∑ j, member.envelope j :=
    single_le_sum (fun j _ => (member.envelope_pos j).le) (mem_univ i)
  have hupper := hsingle.trans member.sum_guard
  have hpower : member.envelope i = (2 : ℚ) ^ bandEnvelopeExponent b member.actions initial i := rfl
  rw [hpower]
  exact (groupDyadicScales_mem hM hb F hF _).mpr ⟨by simpa only [hpower] using hlower,
    by simpa only [hpower] using hupper⟩

theorem unskippedBand_rounded_value_bounds
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (value : Fin M → TargetInterval target.length → ℚ) (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hsmall : 2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (hvalue : ∀ i s, 0 ≤ value i s ∧ value i s ≤ initial i s) (i : Fin M) :
    0 ≤ value i (member.rounded i) ∧ value i (member.rounded i) ≤ 2 * member.envelope i := by
  refine ⟨(hvalue i (member.rounded i)).1, (hvalue i (member.rounded i)).2.trans ?_⟩
  exact roundedBandAction_initialValue_le_twice thetaExponent b member.actions initial
    (member.actions.head member.nonempty) (List.head_mem member.nonempty) L0 hL0 hsmall hspatial i










theorem unskippedGroupEstimate_error {T : ℕ} (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b F)
    (value : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hM : 0 < M) (hb : 0 < b) (hF : 0 < F)
    (draw : ∀ scale : Fin T, Fin (count scale) → Fin M) (error : ℚ)
    (herror : ∀ scale, |groupScaleEstimate (count scale) (scales scale) member.envelope
      (fun i => value i (member.rounded i)) (draw scale) -
        groupScaleTrueCost (scales scale) member.envelope (fun i => value i (member.rounded i))| ≤ error) :
    |unskippedGroupEstimate scales count value member draw -
      rationalEndpointActionValue member.center member.rounded value| ≤ T * error := by
  have hinjective : Function.Injective scales := List.nodup_ofFn.mp
    (hscales.symm ▸ groupDyadicScales_nodup M b F)
  have hcover (i : Fin M) : ∃ scale, scales scale = member.envelope i := by
    have hmember := unskippedBand_envelope_scale member hM hb hF i
    rw [← hscales] at hmember
    exact List.mem_ofFn.mp hmember
  exact groupMemberEstimate_error scales count hinjective _ member.envelope
    (fun i => value i (member.rounded i)) hcover draw error herror

/-- Uniform simultaneous accuracy for the actual fixed list of unskipped
records. The same per-scale samples are reused by every record. -/
theorem unskippedGroupEstimate_failure {T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (scales : Fin T → ℚ) (count : Fin T → ℕ) (Q : ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b F)
    (hcount : ∀ scale, count scale = groupSampleCount M Q b (scales scale))
    (value : Fin M → TargetInterval target.length → ℚ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hM : 0 < M) (hQ : 0 < Q) (hb : 0 < b) (hF : 0 < F)
    (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hsmall : 2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (hvalue : ∀ i s, 0 ≤ value i s ∧ value i s ≤ initial i s)
    (deviation : ℚ) (hdev : 0 < deviation)
    (bernstein : ∀ scale : Fin T, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    (groupSharedDrawLaw count).real
      {draw | ∃ member ∈ members, (T : ℝ) * (deviation : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ≤
      (members.length : ℝ) * T *
        (2 * Real.exp (-(Q : ℝ) * (deviation : ℝ) ^ 2 /
          (512 * (F : ℝ) + (4 / 3 : ℝ) * deviation))) := by
  classical
  let μ := groupSharedDrawLaw (M := M) count
  let : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let bad (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
      (scale : Fin T) : Set (∀ scale : Fin T, Fin (count scale) → Fin M) :=
    {draw | (deviation : ℝ) * b ≤
      |((groupScaleEstimate (count scale) (scales scale) member.envelope
          (fun i => value i (member.rounded i)) (draw scale) -
        groupScaleTrueCost (scales scale) member.envelope
          (fun i => value i (member.rounded i)) : ℚ) : ℝ)|}
  let failure := 2 * Real.exp (-(Q : ℝ) * (deviation : ℝ) ^ 2 /
    (512 * (F : ℝ) + (4 / 3 : ℝ) * deviation))
  have hpoint (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
      (_hmember : member ∈ members.toFinset) (scale : Fin T) (_hscale : scale ∈ (univ : Finset (Fin T))) :
      μ.real (bad member scale) ≤ failure := by
    have hscaleMember : scales scale ∈ groupDyadicScales M b F := by
      rw [← hscales]
      exact List.mem_ofFn.mpr ⟨scale, rfl⟩
    have hscalePos := groupDyadicScales_pos hscaleMember
    change μ.real {draw | draw scale ∈ {sample |
      (deviation : ℝ) * b ≤
      |((groupScaleEstimate (count scale) (scales scale) member.envelope
          (fun i => value i (member.rounded i)) sample -
        groupScaleTrueCost (scales scale) member.envelope
          (fun i => value i (member.rounded i)) : ℚ) : ℝ)|}} ≤ failure
    rw [groupSharedDraw_projection]
    exact groupScaleEstimate_concentration hM hQ hb (scales scale) F deviation hscalePos hF hdev
      member.envelope (fun i => value i (member.rounded i)) (fun i => (member.envelope_pos i).le)
      (unskippedBand_rounded_value_bounds member value L0 hL0 hsmall hspatial hvalue)
      member.sum_guard (hcount scale) (bernstein scale)
  have hsubset : {draw | ∃ member ∈ members, (T : ℝ) * (deviation : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ⊆
      ⋃ member ∈ members.toFinset, ⋃ scale ∈ (univ : Finset (Fin T)), bad member scale := by
    intro draw hdraw
    obtain ⟨member, hmember, herror⟩ := hdraw
    by_contra hnot
    have hscaleError (scale : Fin T) :
        |groupScaleEstimate (count scale) (scales scale) member.envelope
            (fun i => value i (member.rounded i)) (draw scale) -
          groupScaleTrueCost (scales scale) member.envelope (fun i => value i (member.rounded i))| ≤ deviation * b := by
      have hnotScale : draw ∉ bad member scale := by
        intro hbad
        apply hnot
        exact Set.mem_iUnion.mpr ⟨member, Set.mem_iUnion.mpr ⟨List.mem_toFinset.mpr hmember,
          Set.mem_iUnion.mpr ⟨scale, Set.mem_iUnion.mpr ⟨mem_univ scale, hbad⟩⟩⟩⟩
      have hlt : |((groupScaleEstimate (count scale) (scales scale) member.envelope
          (fun i => value i (member.rounded i)) (draw scale) -
        groupScaleTrueCost (scales scale) member.envelope (fun i => value i (member.rounded i)) : ℚ) : ℝ)| <
          (deviation : ℝ) * b := lt_of_not_ge hnotScale
      exact_mod_cast hlt.le
    have htotal := unskippedGroupEstimate_error scales count hscales value member hM hb hF draw
      (deviation * b) hscaleError
    have htotalR : |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)| ≤
        (T : ℝ) * (deviation : ℝ) * b := by
      have hcast : |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)| ≤
          (T : ℝ) * ((deviation : ℝ) * b) := by exact_mod_cast htotal
      simpa only [mul_assoc] using hcast
    exact (not_lt_of_ge htotalR) herror
  have hunion := group_failure_union_bound μ members.toFinset (univ : Finset (Fin T)) bad failure hpoint
  have hcard : (members.toFinset.card : ℝ) ≤ members.length := by exact_mod_cast members.toFinset_card_le
  have hfailure : 0 ≤ (T : ℝ) * failure := by dsimp [failure]; positivity
  calc
    _ ≤ μ.real (⋃ member ∈ members.toFinset, ⋃ scale ∈ (univ : Finset (Fin T)), bad member scale) :=
      measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ (members.toFinset.card : ℝ) * T * failure := by simpa only [card_univ, Fintype.card_fin] using hunion
    _ ≤ (members.length : ℝ) * T * failure := by
      convert mul_le_mul_of_nonneg_right hcard hfailure using 1 <;> ring



theorem chooseUnskippedGroup_spec (Q : ℕ)
    (value : Fin M → TargetInterval target.length → ℚ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hnonempty : members ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) :
    chooseUnskippedGroup Q value members hnonempty draw ∈ members ∧
      ∀ member ∈ members,
        dyadicUnskippedGroupEstimate Q value (chooseUnskippedGroup Q value members hnonempty draw) draw ≤
          dyadicUnskippedGroupEstimate Q value member draw :=
  selectGroupMember_spec members hnonempty (fun member => dyadicUnskippedGroupEstimate Q value member draw)

theorem chooseUnskippedGroup_cost_le (Q : ℕ)
    (value : Fin M → TargetInterval target.length → ℚ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hnonempty : members ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (specified : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hspecified : specified ∈ members) (error : ℚ)
    (haccurate : ∀ member ∈ members, |dyadicUnskippedGroupEstimate Q value member draw -
      rationalEndpointActionValue member.center member.rounded value| ≤ error) :
    let selected := chooseUnskippedGroup Q value members hnonempty draw
    rationalEndpointActionValue selected.center selected.rounded value ≤
      rationalEndpointActionValue specified.center specified.rounded value + 2 * error :=
  selectGroupMember_cost_le members hnonempty
    (fun member => rationalEndpointActionValue member.center member.rounded value)
    (fun member => dyadicUnskippedGroupEstimate Q value member draw) specified hspecified error haccurate


end ActualUnskippedGroup

end EditApproximation

end OAI
