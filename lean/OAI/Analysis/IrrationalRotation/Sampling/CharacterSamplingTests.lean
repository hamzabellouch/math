import OAI.Analysis.IrrationalRotation.Model.CharacterSampling
import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingLimit
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingContinuity
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.CharacterSampling

lemma fract_sub_fract (z v : ℝ) : Int.fract (z - Int.fract v) = Int.fract (z - v) := by
  have heq : z - Int.fract v = z - v + (⌊v⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [heq, Int.fract_add_intCast]

theorem kernel_fract_right (endpoint : Bool) (m : ℕ) (z v : ℝ) :
    kernel endpoint m z (Int.fract v) = kernel endpoint m z v := by
  cases endpoint <;>
    simp only [kernel, Bool.false_eq_true, ↓reduceIte, ScalarSampling.manuscriptEndpointKernel,
      ScalarSampling.manuscriptKernel, ScalarSampling.circleKernel, Int.fract_fract,
      fract_sub_fract]

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

lemma measurable_representative : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

lemma continuousAt_representative {x : UnitAddCircle} (hx : x ≠ 0) :
    ContinuousAt representative x :=
  continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hx)

lemma measurable_kernel (endpoint : Bool) (m : ℕ) :
    Measurable (fun p : ℝ × ℝ => kernel endpoint m p.1 p.2) := by
  cases endpoint
  · exact ScalarSampling.measurable_circleKernel _ _
  · exact (ScalarSampling.measurable_circleKernel _ _).comp
      ((measurable_fst.sub measurable_snd).prodMk measurable_snd)

lemma kernel_nonneg (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    0 ≤ kernel endpoint m z v := by
  have hh := (ScalarSampling.manuscript_parameters hm).1.le
  cases endpoint <;> exact ScalarSampling.rawKernel_nonneg hh
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

lemma kernel_le_height (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    kernel endpoint m z v ≤ (m : ℝ) ^ (13 / 5 : ℝ) := by
  cases endpoint <;> exact ScalarSampling.manuscriptKernel_le_height hm _ _

lemma kernel_abs_le_height (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    |kernel endpoint m z v| ≤ (m : ℝ) ^ (13 / 5 : ℝ) := by
  rw [abs_of_nonneg (kernel_nonneg endpoint hm z v)]
  exact kernel_le_height endpoint hm z v

theorem ae_joint_continuousAt_kernel {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (n τ : ℝ) (hphase : Int.fract (n * τ) ≠ 0) :
    ∀ᵐ x : UnitAddCircle,
      ContinuousAt (fun p : ℝ × UnitAddCircle =>
        kernel endpoint m (representative p.2) (n * p.1)) (τ, x) := by
  have hreal : ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => kernel endpoint m p.1 (n * p.2)) (z, τ) := by
    cases endpoint
    · exact ScalarSampling.ae_joint_continuousAt_manuscriptPower hm n τ hphase
    · exact ScalarSampling.ae_joint_continuousAt_manuscriptEndpointPower hm n τ hphase
  have hpull := CocycleSupport.measurePreserving_circleRepresentative.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (s := Ico (0 : ℝ) 1) hreal)
  have hnotzero := CocycleSupport.measurePreserving_circleRepresentative.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (s := Ico (0 : ℝ) 1) ((volume : Measure ℝ).ae_ne 0))
  filter_upwards [hpull, hnotzero] with x hx hrepzero
  have hzero : x ≠ 0 := by
    intro heq
    subst x
    apply hrepzero
    exact AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := 0) (by norm_num)
  have hc : ContinuousAt
      (fun p : ℝ × UnitAddCircle => (representative p.2, p.1)) (τ, x) :=
    ((continuousAt_representative hzero).comp continuous_snd.continuousAt).prodMk
      continuous_fst.continuousAt
  exact hx.comp_of_eq hc rfl

lemma measurable_squaredError (m : ℕ) (powers : Finset ℕ) (endpoint : Bool) :
    Measurable (squaredError m powers endpoint) := by
  apply Measurable.pow_const
  apply Measurable.sub _ measurable_const
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_kernel endpoint m).comp
    ((measurable_representative.comp ((measurable_pi_apply i).comp measurable_snd)).prodMk
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)))

theorem ae_continuousAt_coordinateFactor {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (n : ℕ) (phase : Fin m → ℝ) (i : Fin m)
    (hphase : Int.fract ((n : ℝ) * phase i) ≠ 0) :
    ∀ᵐ y : UnitAddTorus (Fin m), ContinuousAt
      (fun p : (Fin m → ℝ) × UnitAddTorus (Fin m) =>
        kernel endpoint m (representative (p.2 i)) ((n : ℝ) * p.1 i))
      (phase, y) := by
  have heval : ∀ᵐ y : UnitAddTorus (Fin m), ContinuousAt
      (fun p : ℝ × UnitAddCircle => kernel endpoint m (representative p.2) ((n : ℝ) * p.1))
      (phase i, y i) :=
    (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) i).quasiMeasurePreserving.ae
      (ae_joint_continuousAt_kernel hm endpoint (n : ℝ) (phase i) hphase)
  filter_upwards [heval] with y hy
  have hc : ContinuousAt
      (fun p : (Fin m → ℝ) × UnitAddTorus (Fin m) => (p.1 i, p.2 i)) (phase,y) :=
    ((continuous_apply i).continuousAt.comp continuous_fst.continuousAt).prodMk
      ((continuous_apply i).continuousAt.comp continuous_snd.continuousAt)
  exact ContinuousAt.comp (x := (phase,y)) hy hc

theorem ae_continuousAt_squaredError {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool) (phase : Fin m → ℝ)
    (hphase : ∀ n ∈ powers, ∀ i, Int.fract ((n : ℝ) * phase i) ≠ 0) :
    ∀ᵐ y : UnitAddTorus (Fin m),
      ContinuousAt (squaredError m powers endpoint) (phase, y) := by
  have hall : ∀ᵐ y : UnitAddTorus (Fin m), ∀ n ∈ powers, ∀ i : Fin m,
      ContinuousAt
        (fun p : (Fin m → ℝ) × UnitAddTorus (Fin m) =>
          kernel endpoint m (representative (p.2 i)) ((n : ℝ) * p.1 i))
        (phase, y) := by
    rw [Finset.eventually_all]
    intro n hn
    exact Filter.eventually_all.mpr (fun i => ae_continuousAt_coordinateFactor hm endpoint n phase i (hphase n hn i))
  filter_upwards [hall] with y hy
  apply ContinuousAt.pow
  apply ContinuousAt.sub _ continuousAt_const
  apply ContinuousAt.const_mul
  exact tendsto_finsetSum powers (fun n hn =>
    tendsto_finsetProd Finset.univ (fun i _ => hy n hn i))

lemma average_nonneg {m : ℕ} (hm : 200 ≤ m) (powers : Finset ℕ)
    (endpoint : Bool) (phase : Fin m → ℝ) (spatial : UnitAddTorus (Fin m)) :
    0 ≤ average m powers endpoint phase spatial := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro n hn
  exact Finset.prod_nonneg (fun i _ => kernel_nonneg endpoint hm _ _)

lemma average_le_height {m : ℕ} (hm : 200 ≤ m) (powers : Finset ℕ)
    (endpoint : Bool) (phase : Fin m → ℝ) (spatial : UnitAddTorus (Fin m)) :
    average m powers endpoint phase spatial ≤ ((m : ℝ) ^ (13 / 5 : ℝ)) ^ m := by
  by_cases hp : powers.Nonempty
  · have hcard : (0 : ℝ) < powers.card := by exact_mod_cast hp.card_pos
    have hs : (∑ n ∈ powers, ∏ i : Fin m,
        kernel endpoint m (representative (spatial i)) ((n : ℝ) * phase i)) ≤
        (powers.card : ℝ) * ((m : ℝ) ^ (13 / 5 : ℝ)) ^ m := by
      calc
        _ ≤ ∑ _n ∈ powers, ((m : ℝ) ^ (13 / 5 : ℝ)) ^ m := by
          apply Finset.sum_le_sum
          intro n hn
          calc
            _ ≤ ∏ _i : Fin m, (m : ℝ) ^ (13 / 5 : ℝ) :=
              Finset.prod_le_prod₀ (fun i _ => kernel_nonneg endpoint hm _ _)
                (fun i _ => kernel_le_height endpoint hm _ _)
            _ = _ := by simp
        _ = _ := by simp
    calc
      average m powers endpoint phase spatial ≤
          (powers.card : ℝ)⁻¹ * ((powers.card : ℝ) * ((m : ℝ) ^ (13 / 5 : ℝ)) ^ m) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hcard.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]
  · have hempty : powers = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    simp only [hempty, average, Finset.card_empty, Nat.cast_zero, inv_zero, Finset.sum_empty, mul_zero]
    positivity

theorem squaredError_abs_le {m : ℕ} (hm : 200 ≤ m) (powers : Finset ℕ)
    (endpoint : Bool) (p : (Fin m → ℝ) × UnitAddTorus (Fin m)) :
    |squaredError m powers endpoint p| ≤ (((m : ℝ) ^ (13 / 5 : ℝ)) ^ m + 1) ^ 2 := by
  rw [squaredError, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _)
  calc
    |average m powers endpoint p.1 p.2 - 1| ≤
        |average m powers endpoint p.1 p.2| + |(1 : ℝ)| := by simpa using (abs_sub_le (average m powers endpoint p.1 p.2) 0 1)
    _ = average m powers endpoint p.1 p.2 + 1 := by
      rw [abs_of_nonneg (average_nonneg hm powers endpoint p.1 p.2), abs_one]
    _ ≤ _ := by linarith [average_le_height hm powers endpoint p.1 p.2]

theorem tendsto_integral_squaredError {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool)
    (q : ℕ → ℕ → ℕ) (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {phase : ℕ → Fin m → ℝ} {target : Fin m → ℝ}
    (hphase : Tendsto phase atTop (𝓝 target))
    (hcut : ∀ n ∈ powers, ∀ i, Int.fract ((n : ℝ) * target i) ≠ 0) :
    Tendsto (fun j => ∫ x : UnitAddCircle,
      squaredError m powers endpoint
        (phase j, fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), squaredError m powers endpoint (target, y))) := by
  exact CharacterLaws.tendsto_integral_character_phase_of_ae_continuous q m hq hmono hgap
    hphase (measurable_squaredError m powers endpoint)
    (ae_continuousAt_squaredError hm powers endpoint target hcut)
    (sq_nonneg _) (squaredError_abs_le hm powers endpoint)

theorem integrable_squaredError_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool)
    {F : X → (Fin m → ℝ) × UnitAddTorus (Fin m)} (hF : Measurable F) :
    Integrable (fun x => squaredError m powers endpoint (F x)) μ := by
  apply Integrable.of_bound ((measurable_squaredError m powers endpoint).comp hF).aestronglyMeasurable
    ((((m : ℝ) ^ (13 / 5 : ℝ)) ^ m + 1) ^ 2)
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using squaredError_abs_le hm powers endpoint (F x))

theorem lintegral_squaredError_eq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {m : ℕ} (hm : 200 ≤ m)
    (powers : Finset ℕ) (endpoint : Bool)
    {F : X → (Fin m → ℝ) × UnitAddTorus (Fin m)} (hF : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (squaredError m powers endpoint (F x)) ∂μ) =
      ENNReal.ofReal (∫ x, squaredError m powers endpoint (F x) ∂μ) := by
  apply (ofReal_integral_eq_lintegral_ofReal
    (integrable_squaredError_comp hm powers endpoint hF) _).symm
  exact Eventually.of_forall (fun x => sq_nonneg _)

end Invariant233.CharacterSampling

end

end OAI
