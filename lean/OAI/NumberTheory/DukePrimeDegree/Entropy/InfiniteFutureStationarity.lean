import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteLabelProbability
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureSigma

namespace OAI

/-! # Preservation of mass by conditioning on the entire future

The actual normalized restrictions supplied by the increasing finite-label
conditionings preserve the original measure when integrated over samples.
This is a local disintegration identity, before any gluing of root boxes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V : Type*} [mS : MeasurableSpace S] [mV : MeasurableSpace V]
    [StandardBorelSpace V] [Nonempty V]

/-- Integrating the probability of a measurable set under the genuine
whole-future conditional recovers its original mass. -/
theorem integral_infinite_label_conditional_probability
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {k : ℕ → ℕ} (Q : ∀ n, S × V → Fin (k n)) (hQ : ∀ n, Measurable (Q n))
    (hmono : Monotone (fun n => transverseLabelSigma (Q n)))
    (hdec : ∀ z, Antitone (fun n => labelFiber (Q n) z))
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (⋂ n, labelFiber (Q n) z) ≠ 0)
    (A : Set (S × V)) (hA : MeasurableSet A) :
    let f := fun z =>
      ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
        (⋂ n, labelFiber (Q n) z)).real {t | (z.1,t) ∈ A}
    Integrable f ρ ∧ (∫ z, f z ∂ρ) = ρ.real A := by
  let P : S × V → Fin 2 := fun z => if z ∈ A then 0 else 1
  have hP : Measurable P := measurable_const.piecewise hA measurable_const
  have hp (z : S × V) : P z = 0 ↔ z ∈ A := by simp [P]
  have heq : {z | P z = 0} = A := by ext z; exact hp z
  have heval (z : S × V) : {t | P (z.1,t)=0} = {t | (z.1,t) ∈ A} := by
    ext t
    exact hp (z.1,t)
  have hcond := condExp_infinite_label_probability ρ hP Q hQ hmono hdec hpos 0
  simp only [heq,heval] at hcond
  have hm : (⨆ n, transverseLabelSigma (Q n)) ≤ mS.prod mV := by
    apply iSup_le
    intro n
    exact (measurable_fst.prodMk (hQ n)).comap_le
  refine ⟨integrable_condExp.congr hcond, ?_⟩
  exact (integral_congr_ae hcond).symm.trans
    ((integral_condExp hm).trans (integral_indicator_one hA))

/-- The disintegration identity remains valid on any event determined
by the whole future and the transverse coordinate. This is the local
restriction identity needed when gluing boxes along future events. -/
theorem setIntegral_infinite_label_conditional_probability
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {k : ℕ → ℕ} (Q : ∀ n, S × V → Fin (k n)) (hQ : ∀ n, Measurable (Q n))
    (hmono : Monotone (fun n => transverseLabelSigma (Q n)))
    (hdec : ∀ z, Antitone (fun n => labelFiber (Q n) z))
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (⋂ n, labelFiber (Q n) z) ≠ 0)
    (A : Set (S × V)) (hA : MeasurableSet A)
    (E : Set (S × V)) (hE : MeasurableSet[⨆ n, transverseLabelSigma (Q n)] E) :
    (∫ z in E,
      ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
        (⋂ n, labelFiber (Q n) z)).real {t | (z.1,t) ∈ A} ∂ρ) = ρ.real (A ∩ E) := by
  let P : S × V → Fin 2 := fun z => if z ∈ A then 0 else 1
  have hP : Measurable P := measurable_const.piecewise hA measurable_const
  have hp (z : S × V) : P z = 0 ↔ z ∈ A := by simp [P]
  have heq : {z | P z = 0} = A := by ext z; exact hp z
  have heval (z : S × V) : {t | P (z.1,t)=0} = {t | (z.1,t) ∈ A} := by
    ext t
    exact hp (z.1,t)
  have hcond := condExp_infinite_label_probability ρ hP Q hQ hmono hdec hpos 0
  simp only [heq,heval] at hcond
  have hm : (⨆ n, transverseLabelSigma (Q n)) ≤ mS.prod mV := by
    apply iSup_le
    intro n
    exact (measurable_fst.prodMk (hQ n)).comap_le
  calc
    _ = ∫ z in E, ρ[A.indicator (fun _ => (1 : ℝ)) |
        ⨆ n, transverseLabelSigma (Q n)] z ∂ρ :=
      integral_congr_ae (ae_restrict_of_ae (Filter.EventuallyEq.symm hcond))
    _ = ∫ z in E, A.indicator (fun _ => (1 : ℝ)) z ∂ρ :=
      setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hA) hE
    _ = ρ.real (A ∩ E) := by
      simpa only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply hA] using
        (integral_indicator_const (μ := ρ.restrict E) (1 : ℝ) hA)

/-- The same preservation identity for the actual countable dynamical
future, retaining any additional transverse coordinate. -/
theorem integral_countableFuture_conditional_probability
    {Y : Type*} [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0)
    (A : Set (S × V)) (hA : MeasurableSet A) :
    let f := fun z =>
      ((anchorNormalize (ρ.condKernel z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A}
    Integrable f ρ ∧ (∫ z, f z ∂ρ) = ρ.real A := by
  simpa only [countableFutureFiber_eq_iInter] using
    integral_infinite_label_conditional_probability ρ
      (fun m z => countableFutureCode T Q m (F z))
      (fun m => (countableFutureCode_measurable hT hQ m).comp hF)
      (transverse_countableFutureCode_monotone T Q F)
      (countableFutureCode_fibers_antitone T Q F)
      (by simpa only [countableFutureFiber_eq_iInter] using hpos) A hA

theorem setIntegral_countableFuture_conditional_probability
    {Y : Type*} [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0)
    (A : Set (S × V)) (hA : MeasurableSet A)
    (E : Set (S × V))
    (hE : MeasurableSet[⨆ m,
      transverseLabelSigma (fun z => countableFutureCode T Q m (F z))] E) :
    (∫ z in E,
      ((anchorNormalize (ρ.condKernel z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A} ∂ρ) = ρ.real (A ∩ E) := by
  simpa only [countableFutureFiber_eq_iInter] using
    setIntegral_infinite_label_conditional_probability ρ
      (fun m z => countableFutureCode T Q m (F z))
      (fun m => (countableFutureCode_measurable hT hQ m).comp hF)
      (transverse_countableFutureCode_monotone T Q F)
      (countableFutureCode_fibers_antitone T Q F)
      (by simpa only [countableFutureFiber_eq_iInter] using hpos) A hA E hE

end DukePrimeDegree

end

end OAI
