import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Reconstruction.Uniqueness
import OAI.Geometry.CAT0Fillings.Gradient.Pairing

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma ae_fullSlice_borel_weighted {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B)
    (φ : Euc k → ℝ) :
    ∀ᵐ z : Euc k, currentBorelAction (fullSlice h π z)
      (fun x => φ (coordinateMap π x)*b x) (fun j => Fin.elim0 j) =
      φ z*currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j) := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  have he : (fun x => φ (coordinateMap π x)*b x) =ᵐ[currentMassMeasure (fullSlice_approx h π z).metric]
      (φ z • b) := by
    have hh : ∀ᵐ x ∂currentMassMeasure (fullSlice_approx h π z).metric, coordinateMap π x = z := by
      simpa only [ae_iff,not_not] using hz
    filter_upwards [hh] with x hx
    simp only [hx,Pi.smul_apply,smul_eq_mul]
  rw [currentBorelAction_eq (fullSlice_approx h π z).metric]
  rw [borelAction_congr_ae _ (fullSlice_approx h π z).metric he]
  rw [borelAction_smul _ (fullSlice_approx h π z).metric
    (integrable_bounded_measurable _ hb hB) _ (φ z) (fun j => Fin.elim0 j)]
  rw [currentBorelAction_eq (fullSlice_approx h π z).metric]

lemma fullSlice_borel_weighted_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B)
    {φ : Euc k → ℝ} (hφ : Measurable φ) (C : ℝ≥0) (hC : ∀ z, |φ z| ≤ C) :
    Integrable (fun z => φ z*currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)) ∧
    currentBorelAction T (fun x => φ (coordinateMap π x)*b x) π =
      ∫ z, φ z*currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j) := by
  obtain ⟨L,hL⟩ := coordinateMap_lipschitz π hπ
  have hf : Measurable (fun x => φ (coordinateMap π x)*b x) :=
    (hφ.comp hL.continuous.measurable).mul hb
  have hfB (x) : |φ (coordinateMap π x)*b x| ≤ (C*B : ℝ≥0) := by
    rw [abs_mul]
    exact mul_le_mul (hC _) (hB _) (abs_nonneg _) C.coe_nonneg
  have hi := fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hf (C*B) hfB
  have he := ae_fullSlice_borel_weighted h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb hB φ
  exact ⟨hi.1.congr he,hi.2.trans (integral_congr_ae he)⟩

lemma fullSlice_borel_L1_bound {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B) :
    (∫ z, |currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)|) ≤
      (K:ℝ)^k * ∫ x, |b x| ∂currentMassMeasure h.metric := by
  let f (z : Euc k) := currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)
  have hi := (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1
  let g := hi.aestronglyMeasurable.mk f
  have hg : Measurable g := hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hi.aestronglyMeasurable.ae_eq_mk
  let φ (z : Euc k) : ℝ := if 0 ≤ g z then 1 else -1
  have hφ : Measurable φ := Measurable.ite (measurableSet_le measurable_const hg) measurable_const measurable_const
  have hφ1 (z) : |φ z| ≤ (1:ℝ≥0) := by dsimp [φ]; split <;> norm_num
  have hw := fullSlice_borel_weighted_integral h hX π hπ hb B hB hφ 1 hφ1
  have he : (∫ z, |f z|) = ∫ z, φ z*f z := by
    apply integral_congr_ae
    filter_upwards [hfg] with z hz
    dsimp only [φ]
    rw [hz]
    split_ifs with hg0
    · simp [abs_of_nonneg hg0]
    · simp [abs_of_neg (lt_of_not_ge hg0)]
  rw [he,←hw.2]
  apply (le_abs_self _).trans
  rw [currentBorelAction_eq h.metric]
  obtain ⟨L,hL⟩ := coordinateMap_lipschitz π hπ
  have hf : Measurable (fun x => φ (coordinateMap π x)*b x) :=
    (hφ.comp hL.continuous.measurable).mul hb
  have hfb (x) : |φ (coordinateMap π x)*b x| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hφ1 _) (abs_nonneg _)).trans (by simpa using hB x)
  have hh := borelAction_bound _ h.metric (currentMassMeasure_controls h.metric)
    (integrable_bounded_measurable _ hf hfb) π (fun _ => K) hπ
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg K.coe_nonneg _)
  apply integral_mono (integrable_bounded_measurable _ hf hfb).abs
    (integrable_bounded_measurable _ hb hB).abs
  intro x
  change |φ (coordinateMap π x)*b x| ≤ |b x|
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_right (hφ1 (coordinateMap π x)) (abs_nonneg (b x))

lemma ae_fullSlice_borel_support {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B) :
    ∀ᵐ z : Euc k, z ∉ range (coordinateMap π) →
      currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j) = 0 := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  intro hn
  have hzero : currentMassMeasure (fullSlice_approx h π z).metric univ = 0 := by
    apply measure_mono_null (t := {x | coordinateMap π x ≠ z}) ?_ hz
    intro x _ hx
    exact hn ⟨x,hx⟩
  have hm : mass (fullSlice h π z) = 0 := by
    rw [←currentMassMeasure_total (fullSlice_approx h π z).metric,measureReal_def,hzero,ENNReal.toReal_zero]
  have hh := currentBorelAction_bound (fullSlice_approx h π z).metric hb hB
    (fun j => Fin.elim0 j) (fun _ => (1:ℝ≥0)) (fun j => Fin.elim0 j)
  simp only [hm,mul_zero] at hh
  exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma abs_head_intrinsic_bound {u b : X → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ j, LipschitzWith K (π j)) :
    |T b (Fin.cons u π)| ≤ (K:ℝ)^k*
      ∫ w, |b (q.atlasParam w)| * ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  rw [←q.testWeight_gradient π (fun _ => K) hπ hu hb]
  obtain ⟨B,hB⟩ := hb.2
  have hbi : MemLp (fun w => b (q.atlasParam w)) 2 q.atlasMeasure :=
    MemLp.of_bound (hb.1.choose_spec.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable B
      (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hB _)
  have hi : Integrable (fun w => (K:ℝ)^k*(|b (q.atlasParam w)| * ‖q.gradientFunction u w‖)) q.atlasMeasure :=
    (hbi.norm.integrable_mul (q.memLp_gradientFunction hu).norm).const_mul _
  have hh := norm_integral_le_of_norm_le hi (by
    filter_upwards [q.ae_testWeight_bound π (fun _ => K) hπ (q.gradientFunction u)] with w hw
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hw
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans_eq (by ring))
  rw [integral_const_mul] at hh
  exact hh

lemma abs_cycle_head_intrinsic_bound (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0)
    {u b : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ j, LipschitzWith K (π j)) :
    |T u (Fin.cons b π)| ≤ (K:ℝ)^k*
      ∫ w, |b (q.atlasParam w)| * ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  have hh := h.product_rule (boundedLip_of_lipschitz hu) hb π (fun j => ⟨K,hπ j⟩)
  rw [hz] at hh
  change T u (Fin.cons b π)+T b (Fin.cons u π) = 0 at hh
  have he : T u (Fin.cons b π) = -T b (Fin.cons u π) := by linarith
  rw [he,abs_neg]
  exact q.abs_head_intrinsic_bound hu hb π hπ

lemma abs_cycle_coordinate_intrinsic_bound (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0)
    {u b : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (hb : BoundedLip b)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ j, LipschitzWith K (π j)) (i : Fin (k+1)) :
    |T u (Function.update π i b)| ≤ (K:ℝ)^k*
      ∫ w, |b (q.atlasParam w)| * ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  classical
  let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 i
  let ρ : Fin k → X → ℝ := fun j => π (σ j.succ)
  have hne (j : Fin k) : σ j.succ ≠ i := by
    intro he
    have hh := congrArg σ he
    simp [σ] at hh
  have he : (Function.update π i b) ∘ σ = Fin.cons b ρ := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [σ]
    · simp only [Function.comp_apply,Function.update_of_ne (hne j),Fin.cons_succ,ρ]
  have ha : Admissible u (Function.update π i b) := by
    refine ⟨boundedLip_of_lipschitz hu,?_⟩
    intro j
    by_cases hj : j = i
    · simpa [hj] using hb.1
    · simpa only [Function.update_of_ne hj] using (show ∃ M, LipschitzWith M (π j) from ⟨K,hπ j⟩)
  rw [←h.abs_apply_permute ha σ,he]
  exact q.abs_cycle_head_intrinsic_bound h hz hu hb ρ (fun j => hπ (σ j.succ))

noncomputable def intrinsicSliceControl (π : Fin (k+1) → X → ℝ) (K : ℝ≥0) (u : X → ℝ) :
    Measure (Euc (k+1)) :=
  (K^k) • Measure.map (fun w => coordinateMap π (q.atlasParam w))
    (q.atlasMeasure.withDensity (fun w => ENNReal.ofReal ‖q.gradientFunction u w‖))

lemma intrinsicSliceControl_finite (π : Fin (k+1) → X → ℝ) (K : ℝ≥0)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    IsFiniteMeasure (q.intrinsicSliceControl π K u) := by
  have := isFiniteMeasure_withDensity_ofReal
    ((q.memLp_gradientFunction hu).integrable (by norm_num)).norm.hasFiniteIntegral
  unfold intrinsicSliceControl
  infer_instance

lemma intrinsicSliceControl_integral (π : Fin (k+1) → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) {u : X → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {φ : Euc (k+1) → ℝ} (hφ : Continuous φ) :
    (∫ z, |φ z| ∂q.intrinsicSliceControl π K u) =
      (K:ℝ)^k * ∫ w, |φ (coordinateMap π (q.atlasParam w))| *
        ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  obtain ⟨M,hM⟩ := coordinateMap_lipschitz π hπ
  rw [intrinsicSliceControl,integral_smul_nnreal_measure,
    integral_map (show Measurable (fun w => coordinateMap π (q.atlasParam w)) from
      hM.continuous.measurable.comp q.measurable_atlasParam).aemeasurable
      hφ.abs.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      (q.aestronglyMeasurable_gradientFunction hu).norm.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _),NNReal.smul_def,smul_eq_mul,
    NNReal.coe_pow]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun w => mul_comm _ _

lemma fullSlice_intrinsic_directional_variation (h : NormalApprox (k+1) T)
    (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (i : Fin (k+1)) :
    DirectionalVariation (fun z => fullSlice h π z u (fun j => Fin.elim0 j))
      (EuclideanSpace.basisFun (Fin (k+1)) ℝ i) volume
      (q.intrinsicSliceControl π K u) := by
  intro φ hφ hc
  let A := parameterEquiv (k+1)
  let v := EuclideanSpace.basisFun (Fin (k+1)) ℝ i
  let ψ : (Fin (k+1) → ℝ) → ℝ := fun z => φ (A z)
  let dψ (z : Fin (k+1) → ℝ) := (fderiv ℝ φ (A z)).comp A.toContinuousLinearMap
  have hψ (z) : HasFDerivAt ψ (dψ z) z :=
    ((hφ.differentiable (by simp)) (A z)).hasFDerivAt.comp z A.hasFDerivAt
  have he (z : Fin (k+1) → ℝ) : dψ z (Pi.single i 1) = fderiv ℝ φ (A z) v := by
    simp only [dψ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    congr 1
    simp only [v,EuclideanSpace.basisFun_apply]
    rfl
  obtain ⟨M,hM⟩ := coordinateMap_lipschitz π hπ
  obtain ⟨N,hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)
  have hbφ : BoundedLip (fun x => φ (coordinateMap π x)) := boundedLip_of_lipschitz (hN.comp hM)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc : HasCompactSupport (fun z => fderiv ℝ φ z v) := by
    exact (hc.fderiv ℝ).comp_left (g := fun L => L v) rfl
  obtain ⟨N',hN'⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hdc hd (by simp)
  have hbd : BoundedLip (fun x => dψ (fun j => π j x) (Pi.single i 1)) := by
    simp only [he]
    exact boundedLip_of_lipschitz (hN'.comp hM)
  have huB := boundedLip_of_lipschitz hu
  have hint := (fullSlice_weighted_integral h hX π
    (fun j => boundedLip_of_lipschitz (hπ j))
    (φ := fun z => dψ (WithLp.ofLp z) (Pi.single i 1)) hbd huB).2
  have hchain := h.apply_update_multi huB π (fun j => ⟨K,hπ j⟩) hψ i hbφ hbd
  have hbound := q.abs_cycle_coordinate_intrinsic_bound h hz hu hbφ π hπ i
  have hw : (fun x => dψ (fun j => π j x) (Pi.single i 1)*u x) =
      (fun x => u x*dψ (fun j => π j x) (Pi.single i 1)) := by funext x; ring
  have hA (z : Euc (k+1)) : A (WithLp.ofLp z) = z := rfl
  change |∫ z, (fderiv ℝ φ z) v * fullSlice h π z u (fun j => Fin.elim0 j)| ≤ _
  rw [q.intrinsicSliceControl_integral π hπ hu hφ.continuous]
  have ht : |∫ z, (fderiv ℝ φ z) v * fullSlice h π z u (fun j => Fin.elim0 j)| =
      |T (fun x => dψ (fun j => π j x) (Pi.single i 1)*u x) π| := by
    rw [hint]
    simp only [he,hA]
  rw [ht]
  rw [hw,←hchain]
  exact hbound

end CAT0Fillings.ChartGeometry
end

end OAI
