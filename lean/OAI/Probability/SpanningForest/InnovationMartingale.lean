import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace Problem336.Innovation

theorem integrable_bounded_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (A : Set Ω) :
    Integrable (Function.uncurry b)
      ((volume.restrict (uIoc u v)).prod (P.restrict A)) := by
  let : IsFiniteMeasure (volume.restrict (uIoc u v)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min u v) (max u v)))
    infer_instance
  exact Integrable.of_bound hb.aestronglyMeasurable C
    (Eventually.of_forall (fun q => hbound q.1 q.2))

theorem integral_integrated_drift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (A : Set Ω) (m : ℝ)
    (hmean : ∀ t ∈ uIoc u v, ∫ ω in A, b t ω ∂P = m) :
    (∫ ω in A, (∫ t in u..v, b t ω) ∂P) = (v - u) * m := by
  rw [← intervalIntegral_integral_swap
    (integrable_bounded_field P hb hbound u v A)]
  calc
    (∫ t in u..v, ∫ ω in A, b t ω ∂P) = ∫ _t in u..v, m := by
      apply intervalIntegral.integral_congr_ae
      exact Eventually.of_forall hmean
    _ = (v - u) * m := by simp

theorem integral_posterior_on_past {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ mΩ)
    {X : Ω → ℝ} (hX : Integrable X P) {b : ℝ → Ω → ℝ}
    (hposterior : ∀ t, b t =ᵐ[P] P[X | ℱ t])
    {u t : ℝ} (hut : u ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ u] A) :
    (∫ ω in A, b t ω ∂P) = ∫ ω in A, X ω ∂P := by
  calc
    (∫ ω in A, b t ω ∂P) = ∫ ω in A, P[X | ℱ t] ω ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hposterior t))
    _ = ∫ ω in A, X ω ∂P :=
      setIntegral_condExp (ℱ.le t) hX ((ℱ.mono hut) A hA)

theorem integral_integrated_posterior {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ mΩ)
    {X : Ω → ℝ} (hX : Integrable X P) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t, b t =ᵐ[P] P[X | ℱ t])
    {u v : ℝ} (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[ℱ u] A) :
    (∫ ω in A, (∫ t in u..v, b t ω) ∂P) =
      (v - u) * ∫ ω in A, X ω ∂P := by
  apply integral_integrated_drift P hb hbound u v A
  intro t ht
  rw [uIoc_of_le huv] at ht
  exact integral_posterior_on_past P ℱ hX hposterior ht.1.le hA

theorem integrable_integrated_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) :
    Integrable (fun ω => ∫ t in u..v, b t ω) P := by
  have hprod := integrable_bounded_field P hb hbound u v univ
  simp only [Measure.restrict_univ] at hprod
  have hint := hprod.integral_prod_right
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc,
    Function.uncurry_apply_pair, Pi.smul_def] using
    hint.smul (if u ≤ v then (1 : ℝ) else -1)

theorem intervalIntegrable_field {Ω : Type*} [MeasurableSpace Ω]
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (ω : Ω) :
    IntervalIntegrable (fun t => b t ω) volume u v := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (uIoc u v)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min u v) (max u v)))
    infer_instance
  exact Integrable.of_bound
    (hb.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
    (Eventually.of_forall (fun t => hbound t ω))

def innovation {Ω : Type*} (X : Ω → ℝ) (B b : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  t * X ω + B t ω - ∫ s in 0..t, b s ω

theorem innovation_sub {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (B : ℝ → Ω → ℝ) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (ω : Ω) :
    innovation X B b v ω - innovation X B b u ω =
      (v - u) * X ω + (B v ω - B u ω) - ∫ t in u..v, b t ω := by
  have hi := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_field hb hbound 0 v ω)
    (intervalIntegrable_field hb hbound 0 u ω)
  simp only [innovation]
  rw [← hi]
  ring

theorem integrable_innovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {B b : ℝ → Ω → ℝ} (hB : ∀ t, Integrable (B t) P)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (t : ℝ) :
    Integrable (innovation X B b t) P :=
  ((hX.const_mul t).add (hB t)).sub (integrable_integrated_field P hb hbound 0 t)

theorem integral_innovation_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ mΩ)
    {X : Ω → ℝ} (hX : Integrable X P) {B b : ℝ → Ω → ℝ}
    (hB : ∀ t, Integrable (B t) P)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t, b t =ᵐ[P] P[X | ℱ t])
    {u v : ℝ} (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[ℱ u] A)
    (hnoise : (∫ ω in A, (B v ω - B u ω) ∂P) = 0) :
    (∫ ω in A, (innovation X B b v ω - innovation X B b u ω) ∂P) = 0 := by
  simp_rw [innovation_sub X B hb hbound u v]
  have hs : Integrable (fun ω => (v - u) * X ω) (P.restrict A) :=
    (hX.const_mul (v - u)).integrableOn
  have hn : Integrable (fun ω => B v ω - B u ω) (P.restrict A) := by
    simpa only [IntegrableOn, Pi.sub_def] using ((hB v).sub (hB u)).integrableOn (s := A)
  have hsum : Integrable (fun ω => (v - u) * X ω + (B v ω - B u ω))
      (P.restrict A) := by
    simpa only [Pi.add_def] using hs.add hn
  rw [integral_sub hsum (integrable_integrated_field P hb hbound u v).integrableOn]
  rw [integral_add hs hn]
  rw [integral_const_mul, hnoise,
    integral_integrated_posterior P ℱ hX hb hbound hposterior huv hA]
  ring

theorem martingale_innovation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ mΩ)
    {X : Ω → ℝ} (hX : Integrable X P) {B b : ℝ → Ω → ℝ}
    (hB : ∀ t, Integrable (B t) P)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t, b t =ᵐ[P] P[X | ℱ t])
    (hadapted : StronglyAdapted ℱ (innovation X B b))
    (hnoise : ∀ u v, u ≤ v → ∀ A : Set Ω, MeasurableSet[ℱ u] A →
      (∫ ω in A, (B v ω - B u ω) ∂P) = 0) :
    Martingale (innovation X B b) ℱ P := by
  have hint := integrable_innovation P hX hB hb hbound
  refine ⟨hadapted, fun u v huv => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le u) (hint v)
  · intro A _ _
    exact (hint u).integrableOn
  · intro A hA _
    have hzero := integral_innovation_sub P ℱ hX hB hb hbound hposterior
      huv hA (hnoise u v huv A hA)
    rw [integral_sub (hint v).integrableOn (hint u).integrableOn] at hzero
    linarith
  · exact (hadapted u).aestronglyMeasurable

theorem condExp_innovation_sub_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ mΩ)
    {X : Ω → ℝ} {B b : ℝ → Ω → ℝ}
    (hM : Martingale (innovation X B b) ℱ P)
    {u v : ℝ} (huv : u ≤ v) :
    P[(fun ω => innovation X B b v ω - innovation X B b u ω) | ℱ u]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have hsub := condExp_sub (hM.integrable v) (hM.integrable u) (ℱ u)
  have hv := hM.condExp_ae_eq huv
  have hu := hM.condExp_ae_eq (le_refl u)
  filter_upwards [hsub, hv, hu] with ω hω hvω huω
  simpa only [Pi.sub_def, hvω, huω, sub_self] using hω

theorem integral_weighted_eq_zero_of_condExp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {D : Ω → ℝ} (hD : Integrable D P)
    (hzero : P[D | m] =ᵐ[P] (fun _ => (0 : ℝ)))
    {K : Ω → ℂ} (hK : StronglyMeasurable[m] K) {C : ℝ}
    (hKbound : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    (∫ ω, K ω * (D ω : ℂ) ∂P) = 0 := by
  let M : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hprod : Integrable (fun ω => M (K ω) (D ω)) P :=
    M.integrable_of_bilin_of_bdd_left C (hK.mono hm).aestronglyMeasurable hKbound hD
  have hpull := condExp_bilin_of_stronglyMeasurable_left M hK hprod hD
  have hz : P[(fun ω => M (K ω) (D ω)) | m] =ᵐ[P] (fun _ => (0 : ℂ)) := by
    filter_upwards [hpull, hzero] with ω hω hzω
    simpa only [hzω, map_zero] using hω
  have hi : (∫ ω, M (K ω) (D ω) ∂P) = 0 := by
    rw [← integral_condExp hm]
    simpa only [integral_zero] using integral_congr_ae hz
  simpa only [M, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, mul_comm] using hi

theorem integral_weighted_innovation_sub_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ mΩ)
    {X : Ω → ℝ} {B b : ℝ → Ω → ℝ}
    (hM : Martingale (innovation X B b) ℱ P)
    {u v : ℝ} (huv : u ≤ v) {K : Ω → ℂ}
    (hK : StronglyMeasurable[ℱ u] K) {C : ℝ}
    (hKbound : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    (∫ ω, K ω * ((innovation X B b v ω - innovation X B b u ω : ℝ) : ℂ) ∂P) = 0 := by
  apply integral_weighted_eq_zero_of_condExp P (ℱ.le u)
    (D := fun ω => innovation X B b v ω - innovation X B b u ω)
  · simpa only [Pi.sub_def] using (hM.integrable v).sub (hM.integrable u)
  · exact condExp_innovation_sub_eq_zero P ℱ hM huv
  · exact hK
  · exact hKbound

def nnInnovation {Ω : Type*} (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (b : ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  innovation X (fun s => B s.toNNReal) b t ω

@[simp]
theorem nnInnovation_apply {Ω : Type*} (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (b : ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    nnInnovation X B b t ω = (t : ℝ) * X ω + B t ω - ∫ s in 0..t, b s ω := by
  simp [nnInnovation, innovation]

theorem integral_integrated_posterior_nnreal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    {X : Ω → ℝ} (hX : Integrable X P) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, b t =ᵐ[P] P[X | ℱ t])
    {u v : ℝ≥0} (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[ℱ u] A) :
    (∫ ω in A, (∫ t in (u : ℝ)..v, b t ω) ∂P) =
      ((v : ℝ) - u) * ∫ ω in A, X ω ∂P := by
  apply integral_integrated_drift P hb hbound u v A
  intro t ht
  rw [uIoc_of_le (show (u : ℝ) ≤ v from huv)] at ht
  let t' : ℝ≥0 := ⟨t, u.2.trans ht.1.le⟩
  have hut : u ≤ t' := ht.1.le
  calc
    (∫ ω in A, b t ω ∂P) = ∫ ω in A, P[X | ℱ t'] ω ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hposterior t'))
    _ = ∫ ω in A, X ω ∂P :=
      setIntegral_condExp (ℱ.le t') hX ((ℱ.mono hut) A hA)

theorem martingale_nnInnovation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    {X : Ω → ℝ} (hX : Integrable X P)
    {B : ℝ≥0 → Ω → ℝ} {b : ℝ → Ω → ℝ}
    (hB : ∀ t, Integrable (B t) P)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, b t =ᵐ[P] P[X | ℱ t])
    (hadapted : StronglyAdapted ℱ (nnInnovation X B b))
    (hnoise : ∀ u v, u ≤ v → ∀ A : Set Ω, MeasurableSet[ℱ u] A →
      (∫ ω in A, (B v ω - B u ω) ∂P) = 0) :
    Martingale (nnInnovation X B b) ℱ P := by
  have hint (t : ℝ≥0) : Integrable (nnInnovation X B b t) P :=
    integrable_innovation P hX (fun s => hB s.toNNReal) hb hbound t
  refine ⟨hadapted, fun u v huv => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le u) (hint v)
  · intro A _ _
    exact (hint u).integrableOn
  · intro A hA _
    have hid (ω : Ω) :
        nnInnovation X B b v ω - nnInnovation X B b u ω =
          ((v : ℝ) - u) * X ω + (B v ω - B u ω) -
            ∫ t in (u : ℝ)..v, b t ω := by
      simpa only [nnInnovation, Real.toNNReal_coe] using
        innovation_sub X (fun s => B s.toNNReal) hb hbound u v ω
    have hs : Integrable (fun ω => ((v : ℝ) - u) * X ω) (P.restrict A) :=
      (hX.const_mul ((v : ℝ) - u)).integrableOn
    have hn : Integrable (fun ω => B v ω - B u ω) (P.restrict A) := by
      simpa only [IntegrableOn, Pi.sub_def] using
        ((hB v).sub (hB u)).integrableOn (s := A)
    have hsum : Integrable
        (fun ω => ((v : ℝ) - u) * X ω + (B v ω - B u ω)) (P.restrict A) := by
      simpa only [Pi.add_def] using hs.add hn
    have hzero : (∫ ω in A,
        (nnInnovation X B b v ω - nnInnovation X B b u ω) ∂P) = 0 := by
      simp_rw [hid]
      rw [integral_sub hsum
        (integrable_integrated_field P hb hbound u v).integrableOn]
      rw [integral_add hs hn, integral_const_mul, hnoise u v huv A hA,
        integral_integrated_posterior_nnreal P ℱ hX hb hbound hposterior huv hA]
      ring
    rw [integral_sub (hint v).integrableOn (hint u).integrableOn] at hzero
    linarith
  · exact (hadapted u).aestronglyMeasurable

theorem integral_weighted_martingale_sub_eq_zero
    {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ι mΩ)
    {M : ι → Ω → ℝ} (hM : Martingale M ℱ P)
    {u v : ι} (huv : u ≤ v) {K : Ω → ℂ}
    (hK : StronglyMeasurable[ℱ u] K) {C : ℝ}
    (hKbound : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    (∫ ω, K ω * ((M v ω - M u ω : ℝ) : ℂ) ∂P) = 0 := by
  have hD : Integrable (fun ω => M v ω - M u ω) P := by
    simpa only [Pi.sub_def] using (hM.integrable v).sub (hM.integrable u)
  apply integral_weighted_eq_zero_of_condExp P (ℱ.le u) hD _ hK hKbound
  have hsub := condExp_sub (hM.integrable v) (hM.integrable u) (ℱ u)
  filter_upwards [hsub, hM.condExp_ae_eq huv, hM.condExp_ae_eq (le_refl u)]
    with ω hω hvω huω
  simpa only [Pi.sub_def, hvω, huω, sub_self] using hω

theorem innovation_sub_noise_bound {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (B : ℝ → Ω → ℝ) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b))
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1)
    (u v : ℝ) (ω : Ω) :
    ‖innovation X B b v ω - innovation X B b u ω - (B v ω - B u ω)‖ ≤
      |v - u| := by
  have hbound : ∀ t ω, ‖b t ω‖ ≤ 1 := by
    intro t ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hbbound t ω).1]
    exact (hbbound t ω).2
  rw [innovation_sub X B hb hbound u v]
  have hid : (v - u) * X ω + (B v ω - B u ω) -
      (∫ t in u..v, b t ω) - (B v ω - B u ω) =
        ∫ t in u..v, (X ω - b t ω) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_field hb hbound u v ω)]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hid]
  have hdiff : ∀ t ∈ uIoc u v, ‖X ω - b t ω‖ ≤ 1 := by
    intro t _
    rw [Real.norm_eq_abs, abs_le]
    have hx := hXbound ω
    have ht := hbbound t ω
    constructor <;> linarith [hx.1, hx.2, ht.1, ht.2]
  simpa only [one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const hdiff

end Problem336.Innovation

end

end OAI
