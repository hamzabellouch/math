import OAI.Probability.SpanningForest.PosteriorDrift

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.TiltLimit

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tiltedMean_congr_ae (μ : ProbabilityMeasure Ω)
    {h h' X X' : Ω → ℝ}
    (hh : h =ᵐ[(μ : Measure Ω)] h') (hX : X =ᵐ[(μ : Measure Ω)] X') :
    tiltedMean μ h X = tiltedMean μ h' X' := by
  unfold tiltedMean
  congr 1
  · apply integral_congr_ae
    filter_upwards [hh, hX] with x hx hXx
    rw [hx, hXx]
  · apply integral_congr_ae
    filter_upwards [hh] with x hx
    rw [hx]

variable {I : Type*}

theorem finiteTiltMean_eq_zero_of_ae_absent
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (e : I)
    (he : ∀ᵐ x ∂(μ : Measure (I → Bool)), x e = false) :
    finiteTiltMean μ S h e = 0 := by
  unfold finiteTiltMean tiltedMean
  have hn : (∫ x, bit (x e) * Real.exp (finiteEnergy S h x)
      ∂(μ : Measure (I → Bool))) = 0 := by
    calc
      _ = ∫ _x, (0 : ℝ) ∂(μ : Measure (I → Bool)) := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        simp [hx, bit]
      _ = 0 := integral_zero _ _
  rw [hn, zero_div]

theorem finiteEnergy_congr_on_support
    (μ : ProbabilityMeasure (I → Bool)) (active : I → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure (I → Bool)), ∀ i, ¬ active i → x i = false)
    (S : Finset I) {h h' : I → ℝ} (hh : ∀ i, active i → h i = h' i) :
    finiteEnergy S h =ᵐ[(μ : Measure (I → Bool))] finiteEnergy S h' := by
  filter_upwards [hμ] with x hx
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : active i
  · rw [hh i ha]
  · simp [hx i ha, bit]

theorem finiteTiltMean_congr_on_support
    (μ : ProbabilityMeasure (I → Bool)) (active : I → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure (I → Bool)), ∀ i, ¬ active i → x i = false)
    (S : Finset I) {h h' : I → ℝ} (hh : ∀ i, active i → h i = h' i) (e : I) :
    finiteTiltMean μ S h e = finiteTiltMean μ S h' e :=
  tiltedMean_congr_ae μ (finiteEnergy_congr_on_support μ active hμ S hh)
    (Filter.Eventually.of_forall fun _ => rfl)

theorem limsup_finiteTiltMean_eq_zero_of_ae_absent
    (μ : ProbabilityMeasure (I → Bool)) (S : ℕ → Finset I)
    (h : ℕ → I → ℝ) (e : I)
    (he : ∀ᵐ x ∂(μ : Measure (I → Bool)), x e = false) :
    Filter.limsup (fun n => finiteTiltMean μ (S n) (h n) e) Filter.atTop = 0 := by
  simp only [finiteTiltMean_eq_zero_of_ae_absent μ _ _ e he]
  exact Filter.limsup_const (f := (Filter.atTop : Filter ℕ)) (b := (0 : ℝ))

theorem limsup_finiteTiltMean_congr_on_support
    (μ : ProbabilityMeasure (I → Bool)) (active : I → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure (I → Bool)), ∀ i, ¬ active i → x i = false)
    (S : ℕ → Finset I) {h h' : ℕ → I → ℝ}
    (hh : ∀ n i, active i → h n i = h' n i) (e : I) :
    Filter.limsup (fun n => finiteTiltMean μ (S n) (h n) e) Filter.atTop =
      Filter.limsup (fun n => finiteTiltMean μ (S n) (h' n) e) Filter.atTop := by
  congr 1
  funext n
  exact finiteTiltMean_congr_on_support μ active hμ (S n) (hh n) e

end Problem336.TiltLimit

namespace Problem336.PosteriorDrift
open TiltLimit

variable {I : Type*}

theorem drift_eq_zero_of_ae_absent
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I)
    (he : ∀ᵐ x ∂(μ : Measure (I → Bool)), x e = false) :
    drift μ S t y e = 0 :=
  limsup_finiteTiltMean_eq_zero_of_ae_absent μ (S e) (fun _ i => y i - t / 2) e he

theorem drift_congr_on_support
    (μ : ProbabilityMeasure (I → Bool)) (active : I → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure (I → Bool)), ∀ i, ¬ active i → x i = false)
    (S : I → ℕ → Finset I) (t : ℝ) {y y' : I → ℝ}
    (hy : ∀ i, active i → y i = y' i) (e : I) :
    drift μ S t y e = drift μ S t y' e := by
  apply limsup_finiteTiltMean_congr_on_support μ active hμ (S e)
  intro n i hi
  change y i - t / 2 = y' i - t / 2
  rw [hy i hi]

theorem drift_eq_zero_off_support
    (μ : ProbabilityMeasure (I → Bool)) (active : I → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure (I → Bool)), ∀ i, ¬ active i → x i = false)
    (S : I → ℕ → Finset I) (t : ℝ) (y : I → ℝ) (e : I) (he : ¬ active e) :
    drift μ S t y e = 0 :=
  drift_eq_zero_of_ae_absent μ S t y e (hμ.mono fun _ hx => hx e he)

end Problem336.PosteriorDrift

end

end OAI
