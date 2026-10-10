import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.Conditional3

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOriginalForgetting_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem IsNuclearBarrier.forget_original {N K : ℕ} (ρ : Measure (Configuration N))
    [IsProbabilityMeasure ρ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    {Z κ B C R T η : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (old : IsNuclearBarrier (physicalObservationLaw ρ K)
      (originalMasterField ρ ell j c₁ r₀ s g) Z κ B C R T η a p) :
    IsNuclearBarrier (physicalObservationLaw ρ K) (originalMasterField ρ ell k c₁ r₀ s g)
      Z κ B C R T η
      (fun sample => conditionalField (physicalObservationLaw ρ K) (originalDatum ell k) a (originalDatum ell k sample))
      (fun sample => conditionalField (physicalObservationLaw ρ K) (originalDatum ell k) p (originalDatum ell k sample)) := by
  exact (old.forget (physicalObservationLaw ρ K) (originalDatum ell k)
    (originalDatum_measurable ell k) hR hκ
    (originalMasterField_measurable ρ ell j hc hr hs hg)
    (originalMasterField_deterministicBound ρ ell j hc hr hs hrs hg hcg)).congr_density
      (originalMasterField_tower ρ ell hjk hc hr hs hrs hg hcg)

end Work_BarrierOriginalForgetting_barrier_scope

section Work_BarrierBadMass_barrier_scope

open MeasureTheory Set Filter Metric
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation

lemma event_integral_le_of_square_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Integrable f P) (hf2 : Integrable (fun sample => (f sample)^2) P)
    (A : Set Ω) {p L : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hprob : P.real A ≤ p^2) (hmoment : (∫ sample, (f sample)^2 ∂P) ≤ L^2) :
    (∫ sample in A, f sample ∂P) ≤ p*L := by
  by_cases hzero : P.real A = 0
  · have hz : P A = 0 := (measureReal_eq_zero_iff).mp hzero
    rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
    positivity
  have hpos : 0 < P.real A := lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hzero)
  have hsq := event_even_moment_le f (k := 1) (by norm_num) hf (by simpa using hf2) A hpos
  norm_num only [mul_one,pow_one] at hsq
  have hbound : P.real A*(∫ sample, (f sample)^2 ∂P) ≤ p^2*L^2 :=
    mul_le_mul hprob hmoment (integral_nonneg fun sample => sq_nonneg (f sample)) (sq_nonneg p)
  have hnon : 0 ≤ p*L := mul_nonneg hp hL
  nlinarith only [hsq,hbound,hnon]

lemma bounded_density_square_data_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ρ : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry ρ)) {D : ℝ}
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ D) (x : TFSpace) :
    Integrable (fun sample => (ρ sample x)^2) P := by
  apply Integrable.of_bound ((hm.comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable (D^2)
  exact ae_of_all _ fun sample => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hn sample x) (hb sample x) 2

theorem addedError_expected_mass_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ))
    {D R p L : ℝ} (hD : 0 ≤ D) (hR : 0 < R) (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ D)
    (hprob : P.real {sample | ¬ good sample} ≤ p^2)
    (hmoment : ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < R → (∫ sample, (ρ sample x)^2 ∂P) ≤ L^2) :
    (∫ sample, (∫ x, addedError (good sample) R (ρ sample) (fun _ => 0) x) ∂P) ≤
      (4*Real.pi/3)*R^3*p*L := by
  let q (sample : Ω) (x : TFSpace) := addedError (good sample) R (ρ sample) (fun _ => 0) x
  have hqm : Measurable (Function.uncurry q) := addedError_measurable good hg (p := fun _ _ => 0) hm measurable_const R
  have hqb : DeterministicLocalBound q := nonneg_bounded_deterministicBound
    (fun sample x => addedError_nonneg (good sample) (R := R) (hn sample) (fun _ => le_refl 0) x)
    (fun sample x => by simpa only [zero_add] using addedError_le (good sample) (R := R) hD (hb sample) (fun _ => le_refl 0) x)
  have hqs : ∀ sample x, R < ‖x‖ → q sample x = 0 :=
    fun sample x hx => addedError_support (good sample) hR.le (fun _ _ => rfl) hx
  have hqi := compactBound_integrable_prod (P := P) hqm hqb hqs
  have hpi : Integrable ((ball (0 : TFSpace) R).indicator (fun _ => p*L)) volume :=
    (integrableOn_const (C := p*L) (measure_ball_lt_top.ne)).integrable_indicator measurableSet_ball
  change (∫ sample, (∫ x, q sample x) ∂P) ≤ _
  rw [integral_integral_swap hqi]
  calc
    _ ≤ ∫ x, (ball (0 : TFSpace) R).indicator (fun _ => p*L) x := by
      apply integral_mono hqi.integral_prod_right hpi
      intro x
      change (∫ sample, q sample x ∂P) ≤ (ball (0 : TFSpace) R).indicator (fun _ => p*L) x
      by_cases hx : ‖x‖ < R
      · rw [indicator_of_mem (mem_ball_zero_iff.mpr hx)]
        by_cases hx' : R/2 ≤ ‖x‖
        · have he : (fun sample => q sample x) = {sample | ¬ good sample}.indicator (fun sample => ρ sample x) := by
            funext sample
            simp only [q,addedError,ite_eq_left (show R/2 ≤ ‖x‖ ∧ ‖x‖ < R from ⟨hx',hx⟩),zero_add]
            by_cases hh : good sample <;> simp [hh]
          rw [he]
          change (∫ sample, {sample | ¬ good sample}.indicator (fun sample => ρ sample x) sample ∂P) ≤ p*L
          rw [integral_indicator (show MeasurableSet {sample | ¬ good sample} from hg.compl)]
          exact event_integral_le_of_square_bounds
            (deterministicBound_integrable_section hm (nonneg_bounded_deterministicBound hn hb) x)
            (bounded_density_square_data_integrable hm hn hb x) _ hp hL hprob (hmoment x hx' hx)
        · have he : (fun sample => q sample x) = 0 := by
            funext sample
            simp [q,addedError,hx']
          rw [he]
          change (∫ sample : Ω, (0 : ℝ) ∂P) ≤ p*L
          rw [integral_zero]
          positivity
      · rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hx)]
        have he : (fun sample => q sample x) = 0 := by
          funext sample
          simp [q,addedError,hx]
        rw [he]
        change (∫ sample : Ω, (0 : ℝ) ∂P) ≤ 0
        rw [integral_zero]
    _ = _ := by
      rw [integral_indicator measurableSet_ball,setIntegral_const,smul_eq_mul]
      have hv : volume.real (ball (0 : TFSpace) R) = R^3*(Real.pi*4/3) := by
        rw [measureReal_def,EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_mul,ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hR.le,ENNReal.toReal_ofReal (by positivity)]
      rw [hv]
      ring

end Work_BarrierBadMass_barrier_scope

open Set Filter MeasureTheory
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis

def barrierErrorExponent : ℝ := 19/2-3*masterExponent

lemma barrierErrorExponent_one_le : 1 ≤ barrierErrorExponent := by
  norm_num [barrierErrorExponent,masterExponent]

lemma barrierErrorExponent_pos : 0 < barrierErrorExponent := lt_of_lt_of_le (by norm_num) barrierErrorExponent_one_le

lemma addedError_expected_mass_power {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (good : Ω → Prop) [DecidablePred good] (hg : MeasurableSet {sample | good sample})
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ))
    {D r A B : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ D)
    (hprob : P.real {sample | ¬ good sample} ≤ A*r^(25:ℕ))
    (hmoment : ∀ x, r ≤ ‖x‖ → ‖x‖ < 2*r →
      (∫ sample, (ρ sample x)^2 ∂P) ≤ B*r^(-12-6*masterExponent)) :
    (∫ sample, (∫ x, addedError (good sample) (2*r) (ρ sample) (fun _ => 0) x) ∂P) ≤
      (32*Real.pi/3*Real.sqrt A*Real.sqrt B)*r^barrierErrorExponent := by
  have he1 : (Real.sqrt A*r^(25/2:ℝ))^2 = A*r^(25:ℕ) := by
    rw [mul_pow,Real.sq_sqrt hA,←Real.rpow_mul_natCast hr.le]
    norm_num
  have he2 : (Real.sqrt B*r^(-6-3*masterExponent))^2 = B*r^(-12-6*masterExponent) := by
    rw [mul_pow,Real.sq_sqrt hB,←Real.rpow_mul_natCast hr.le]
    congr 2
    ring
  apply (addedError_expected_mass_le good hg hm hD (by positivity)
    (p := Real.sqrt A*r^(25/2:ℝ)) (L := Real.sqrt B*r^(-6-3*masterExponent))
    (by positivity) (by positivity) hn hb (by rwa [he1])
    (fun x hx hx' => by rw [he2]; exact hmoment x (by linarith) hx')).trans_eq
  calc
    (4*Real.pi/3)*(2*r)^3*(Real.sqrt A*r^(25/2:ℝ))*(Real.sqrt B*r^(-6-3*masterExponent)) =
        (32*Real.pi/3*Real.sqrt A*Real.sqrt B)*((r^(3:ℝ)*r^(25/2:ℝ))*r^(-6-3*masterExponent)) := by
          rw [show r^(3:ℝ) = r^(3:ℕ) by exact_mod_cast Real.rpow_natCast r 3]
          ring
    _ = _ := by
      rw [←Real.rpow_add hr,←Real.rpow_add hr]
      congr 2
      dsimp only [barrierErrorExponent]
      ring

lemma sum_dyadic_powers_le {r a : ℝ} (hr : 0 < r) (ha : 1 ≤ a) (K : ℕ) :
    (∑ j ∈ Finset.range K, ((2:ℝ)^j*r)^a) ≤ ((2:ℝ)^K*r)^a-r^a := by
  have htwo : 2 ≤ (2:ℝ)^a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ha
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have he : ((2:ℝ)^(K+1)*r)^a = (2:ℝ)^a*((2:ℝ)^K*r)^a := by
      rw [pow_succ,show (2:ℝ)^K*2*r = 2*((2:ℝ)^K*r) by ring,Real.mul_rpow (by norm_num) (by positivity)]
    rw [he]
    have hh := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity : 0 ≤ (2:ℝ)^K*r) a)
    linarith

lemma sum_dyadic_errors_le {r s C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (K : ℕ)
    (hend : (2:ℝ)^K*r ≤ s) :
    (∑ j ∈ Finset.range K, C*((2:ℝ)^j*r)^barrierErrorExponent) ≤ C*s^barrierErrorExponent := by
  rw [←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC
  apply (sum_dyadic_powers_le hr barrierErrorExponent_one_le K).trans
  have hmon := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^K*r) hend barrierErrorExponent_pos.le
  linarith [Real.rpow_nonneg hr.le barrierErrorExponent]

lemma total_barrier_budget_tendsto_zero {ι : Type*} {F : Filter ι}
    {s : ι → ℝ} (hs : Tendsto s F (𝓝 0)) (C : ℝ) :
    Tendsto (fun j => 5184*(s j)^32+C*(s j)^barrierErrorExponent) F (𝓝 0) := by
  have h₁ := (hs.pow 32).const_mul 5184
  have h₂ := (hs.rpow_const (Or.inr barrierErrorExponent_pos.le)).const_mul C
  simpa only [zero_pow (by norm_num : (32:ℕ) ≠ 0),
    Real.zero_rpow barrierErrorExponent_pos.ne',mul_zero,zero_add] using h₁.add h₂

lemma initial_budget_le_final_radius {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    5184*r^32 ≤ 5184*s^32 :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs 32) (by norm_num)

end CoulombBarrier

end

end OAI
