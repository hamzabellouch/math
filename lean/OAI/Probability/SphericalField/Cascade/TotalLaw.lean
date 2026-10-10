import Mathlib
import OAI.Probability.SphericalField.Poisson.WeightedTotal

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma poissonWeightedTotal_law {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (poissonWeightedTotal X) =
      (poissonRandomMeasureLaw (stableLogIntensity b)).map
        (fun η => Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η) := by
  let c := Real.log (∫ x, Real.exp (b*X x) ∂ν)/b
  let F := fun x => X x-c
  have hF : Measurable F := hX.sub_const c
  have hMpos := integral_exp_pos hI
  have hfac (x : S) : Real.exp (b*F x) = Real.exp (-b*c)*Real.exp (b*X x) := by
    dsimp [F]
    rw [← Real.exp_add]
    congr 1
    ring
  have hFI : Integrable (fun x => Real.exp (b*F x)) ν := by
    simp_rw [hfac]
    exact hI.const_mul _
  have hFM : (∫ x, Real.exp (b*F x) ∂ν) = 1 := by
    simp_rw [hfac]
    rw [integral_const_mul,show -b*c = -Real.log (∫ x, Real.exp (b*X x) ∂ν) by dsimp [c]; field_simp,
      Real.exp_neg,Real.exp_log hMpos,inv_mul_cancel₀ hMpos.ne']
  have he := stablePoisson_normalized_mark_projection ν hb.le hF hFI hFM
  have hm : Measurable (fun p : ℝ×S => p.1+F p.2) := measurable_fst.add (hF.comp measurable_snd)
  have hT : poissonWeightedTotal X = fun η => Real.exp c*stablePoissonTotal
      (η.map (fun p : ℝ×S => p.1+F p.2)) := by
    funext η
    rw [← poissonWeightedTotal_eq hF]
    convert poissonWeightedTotal_add_const hF c η using 1
    congr 1
    funext x
    dsimp [F]
    ring
  rw [hT,show (fun η : Measure (ℝ×S) => Real.exp c*stablePoissonTotal
      (η.map (fun p => p.1+F p.2))) =
      (fun η : Measure ℝ => Real.exp c*stablePoissonTotal η) ∘ Measure.map (fun p : ℝ×S => p.1+F p.2) from rfl,
    ← Measure.map_map ((stablePoissonTotal_measurable.const_mul _))
      (Measure.measurable_map _ hm),he]

def StableCascade : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×StableCascade n))

instance stableCascadeNonempty (n : ℕ) : Nonempty (StableCascade n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×StableCascade n))⟩

def cascadeTotalE : (n : ℕ) → StableCascade n → ℝ≥0∞
  | 0, _ => 1
  | n+1, η => ∫⁻ p : ℝ×StableCascade n,
      ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 ∂η

lemma cascadeTotalE_measurable (n : ℕ) : Measurable (cascadeTotalE n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_lintegral
      ((Real.measurable_exp.comp measurable_fst).ennreal_ofReal.mul (ih.comp measurable_snd))

def cascadeTotal (n : ℕ) (η : StableCascade n) : ℝ := (cascadeTotalE n η).toReal

lemma cascadeTotal_measurable (n : ℕ) : Measurable (cascadeTotal n) :=
  (cascadeTotalE_measurable n).ennreal_toReal

def cascadeLaw : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (StableCascade n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      (cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n))),by exact poissonRandomMeasureLaw_probability _⟩

lemma poissonWeightedTotal_identDistrib {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    IdentDistrib (poissonWeightedTotal X)
      (fun η => Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η)
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
  ⟨(poissonWeightedTotal_measurable hX).aemeasurable,
    (stablePoissonTotal_measurable.const_mul _).aemeasurable,
    poissonWeightedTotal_law ν hb hX hI⟩

lemma poissonWeightedTotal_pos {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν), 0 < poissonWeightedTotal X η := by
  apply (poissonWeightedTotal_identDistrib ν hb hX hI).symm.ae_snd measurableSet_Ioi
  filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
  exact mul_pos (Real.exp_pos _) hη

lemma poissonWeightedTotal_rpow_integrable {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b a : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    Integrable (fun η => (poissonWeightedTotal X η)^a)
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) := by
  have hid := (poissonWeightedTotal_identDistrib ν hb hX hI).comp
    (measurable_id.pow_const a : Measurable (fun x : ℝ => x^a))
  apply hid.integrable_iff.mpr
  have he (η : Measure ℝ) : (Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η)^a =
      (Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b))^a*(stablePoissonTotal η)^a :=
    Real.mul_rpow (Real.exp_pos _).le ENNReal.toReal_nonneg
  simpa only [Function.comp_def,id_eq,he] using (stablePoissonTotal_rpow_integrable hb hb1 ha).const_mul
    ((Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b))^a)

lemma poissonRandomMeasureLaw_ae_ae {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {p : S → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ x ∂κ, p x) : ∀ᵐ η ∂poissonRandomMeasureLaw κ, ∀ᵐ x ∂η, p x := by
  have hh := poissonRandomMeasureLaw_ae_null κ hp.compl (ae_iff.mp h)
  exact hh.mono fun η hη => ae_iff.mpr hη

lemma cascadeTotal_succ_eq {n : ℕ} (z : Fin (n+1) → ℝ)
    (hp : ∀ᵐ η ∂(cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n)),
      0 < cascadeTotal n η) :
    ∀ᵐ η ∂(cascadeLaw (n+1) z : Measure (StableCascade (n+1))),
      cascadeTotal (n+1) η = poissonWeightedTotal (fun C => Real.log (cascadeTotal n C)) η := by
  let ν : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
  have hpκ : ∀ᵐ p ∂(stableLogIntensity (z 0)).prod ν, 0 < cascadeTotal n p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const ((cascadeTotal_measurable n).comp measurable_snd))).mpr
      (ae_of_all _ fun _ => hp)
  have he := poissonRandomMeasureLaw_ae_ae ((stableLogIntensity (z 0)).prod ν)
    (measurableSet_lt measurable_const ((cascadeTotal_measurable n).comp measurable_snd)) hpκ
  change ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ν), _
  filter_upwards [he] with η hη
  unfold cascadeTotal poissonWeightedTotal
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hη] with p hp
  change ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 =
    ENNReal.ofReal (Real.exp (p.1+Real.log (cascadeTotal n p.2)))
  change 0 < cascadeTotal n p.2 at hp
  rw [Real.exp_add,Real.exp_log hp,ENNReal.ofReal_mul (Real.exp_pos _).le,cascadeTotal,
    ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hp).2.ne]

theorem cascadeTotal_regular (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    (∀ᵐ η ∂(cascadeLaw n z : Measure (StableCascade n)), 0 < cascadeTotal n η) ∧
    ∀ a : ℝ, (∀ i, a < z i) → Integrable (fun η => (cascadeTotal n η)^a)
      (cascadeLaw n z : Measure (StableCascade n)) := by
  induction n with
  | zero =>
    constructor
    · exact ae_of_all _ fun _ => by simp [cascadeTotal,cascadeTotalE]
    · intro a _; simpa only [cascadeTotal,cascadeTotalE,ENNReal.toReal_one,Real.one_rpow] using
        (integrable_const (1:ℝ) : Integrable (fun _ : StableCascade 0 => (1:ℝ)) (cascadeLaw 0 z : Measure (StableCascade 0)))
  | succ n ih =>
    let ν : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
    have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    obtain ⟨hpos,hint⟩ := ih (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
    have hM : Integrable (fun C => Real.exp (z 0*Real.log (cascadeTotal n C))) ν := by
      have hh := hint (z 0) (fun i => hz (by simp))
      apply hh.congr
      filter_upwards [hpos] with C hC
      rw [Real.rpow_def_of_pos hC]
      congr 1
      ring
    have hEq := cascadeTotal_succ_eq z hpos
    have hlog : Measurable (fun C : StableCascade n => Real.log (cascadeTotal n C)) :=
      (cascadeTotal_measurable n).log
    constructor
    · have hp := poissonWeightedTotal_pos ν (hz0 0) (hz1 0) hlog hM
      filter_upwards [hp,hEq] with η hp he
      rwa [he]
    · intro a ha
      have hI := poissonWeightedTotal_rpow_integrable ν (hz0 0) (hz1 0) (ha 0) hlog hM
      exact hI.congr (hEq.mono fun η he => congrArg (fun t : ℝ => t^a) he.symm)

end SphericalPerceptron
end
end
end

end OAI
