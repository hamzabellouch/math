import OAI.NumberTheory.DukePrimeDegree.Entropy.SelfConditionalKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteFutureStationarity
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureMap
import Mathlib.Probability.Kernel.Composition.Prod

namespace OAI

/-! # The local future conditional as a self-consistent Markov kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]

private def futureSliceKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) V where
  toFun z := (κ z.1).restrict (countableFutureFiber T Q F z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp only [Measure.restrict_apply hA]
    have h := measurable_countableFuture_mass κ hT hQ hF
      (Prod.snd ⁻¹' A) (hA.preimage measurable_snd)
    have hm : (⨆ m, transverseLabelSigma
        (fun z => countableFutureCode T Q m (F z))) ≤
        (inferInstance : MeasurableSpace (S × V)) := by
      apply iSup_le
      intro m
      exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
    exact h.mono hm le_rfl

private def normalizedFutureSliceKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) V where
  toFun z :=
    ((futureSliceKernel κ hT hQ hF z) univ)⁻¹ • futureSliceKernel κ hT hQ hF z
  measurable' := by
    let ν := futureSliceKernel κ hT hQ hF
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun z => (ν z univ)⁻¹ * ν z A)
    exact (ν.measurable_coe MeasurableSet.univ).inv.mul (ν.measurable_coe hA)

def futureFiberTimeKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) V :=
  let ν := futureSliceKernel κ hT hQ hF
  Kernel.piecewise
    (measurableSet_eq_fun (g := fun _ => (0 : ℝ≥0∞))
      (ν.measurable_coe MeasurableSet.univ) measurable_const).compl
    (normalizedFutureSliceKernel κ hT hQ hF)
    (Kernel.deterministic Prod.snd measurable_snd)

lemma futureFiberTimeKernel_apply_good (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V)
    (hz : κ z.1 (countableFutureFiber T Q F z) ≠ 0) :
    futureFiberTimeKernel κ hT hQ hF z =
      (anchorNormalize (κ z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z) := by
  change (if (futureSliceKernel κ hT hQ hF z) univ ≠ 0 then
    normalizedFutureSliceKernel κ hT hQ hF z else Measure.dirac z.2) = _
  have hm : (futureSliceKernel κ hT hQ hF z) univ =
      κ z.1 (countableFutureFiber T Q F z) := Measure.restrict_apply_univ _
  rw [hm,ite_eq_left hz]
  change ((futureSliceKernel κ hT hQ hF z) univ)⁻¹ •
    (κ z.1).restrict (countableFutureFiber T Q F z) = _
  rw [hm,anchorNormalize,Measure.restrict_smul]

lemma futureFiberTimeKernel_apply_zero (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V)
    (hz : κ z.1 (countableFutureFiber T Q F z) = 0) :
    futureFiberTimeKernel κ hT hQ hF z = Measure.dirac z.2 := by
  change (if (futureSliceKernel κ hT hQ hF z) univ ≠ 0 then
    normalizedFutureSliceKernel κ hT hQ hF z else Measure.dirac z.2) = _
  have hm : (futureSliceKernel κ hT hQ hF z) univ =
      κ z.1 (countableFutureFiber T Q F z) := Measure.restrict_apply_univ _
  rw [hm,hz,ite_eq_right (not_ne_iff.mpr rfl)]

instance futureFiberTimeKernel_markov (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) :
    IsMarkovKernel (futureFiberTimeKernel κ hT hQ hF) := by
  refine ⟨fun z => ⟨?_⟩⟩
  by_cases hz : κ z.1 (countableFutureFiber T Q F z)=0
  · rw [futureFiberTimeKernel_apply_zero κ hT hQ hF z hz]
    simp
  · rw [futureFiberTimeKernel_apply_good κ hT hQ hF z hz]
    simp only [anchorNormalize,Measure.restrict_smul,Measure.smul_apply,
      Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hz (measure_ne_top _ _)

def futureFiberCoordinateKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) (S × V) :=
  (Kernel.deterministic Prod.fst measurable_fst).prod (futureFiberTimeKernel κ hT hQ hF)

instance futureFiberCoordinateKernel_markov (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) :
    IsMarkovKernel (futureFiberCoordinateKernel κ hT hQ hF) := by
  unfold futureFiberCoordinateKernel
  infer_instance

lemma futureFiberCoordinateKernel_apply (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V) :
    futureFiberCoordinateKernel κ hT hQ hF z =
      (futureFiberTimeKernel κ hT hQ hF z).map (Prod.mk z.1) := by
  rw [futureFiberCoordinateKernel,Kernel.prod_apply,Kernel.deterministic_apply,
    Measure.dirac_prod]

theorem futureFiberCoordinateKernel_self_constant [MeasurableSingletonClass S]
    [MeasurableSingletonClass V] (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V) :
    ∀ᵐ w ∂futureFiberCoordinateKernel κ hT hQ hF z,
      futureFiberCoordinateKernel κ hT hQ hF w =
        futureFiberCoordinateKernel κ hT hQ hF z := by
  rw [futureFiberCoordinateKernel_apply]
  by_cases hz : κ z.1 (countableFutureFiber T Q F z)=0
  · rw [futureFiberTimeKernel_apply_zero κ hT hQ hF z hz,
      Measure.map_dirac]
    rw [ae_dirac_eq]
    change futureFiberCoordinateKernel κ hT hQ hF (z.1,z.2)=Measure.dirac (z.1,z.2)
    exact futureFiberCoordinateKernel_apply κ hT hQ hF z |>.trans (by
      rw [futureFiberTimeKernel_apply_zero κ hT hQ hF z hz,Measure.map_dirac])
  · have hfiber : MeasurableSet (countableFutureFiber T Q F z) := by
      simp only [countableFutureFiber,Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_eq_fun
        (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
    have hmem : ∀ᵐ w ∂(futureFiberTimeKernel κ hT hQ hF z).map (Prod.mk z.1),
        w.1=z.1 ∧ w.2 ∈ countableFutureFiber T Q F z := by
      apply (ae_map_iff measurable_prodMk_left.aemeasurable
        (((measurableSet_singleton z.1).preimage measurable_fst).inter
          (hfiber.preimage measurable_snd))).mpr
      rw [futureFiberTimeKernel_apply_good κ hT hQ hF z hz]
      filter_upwards [ae_restrict_mem hfiber] with v hv
      exact ⟨rfl,hv⟩
    filter_upwards [hmem] with w hw
    obtain ⟨s,v⟩ := w
    dsimp only at hw
    rcases hw with ⟨hs,hv⟩
    subst s
    have he := countableFutureFiber_eq_of_mem T Q F z hv
    have hm : κ z.1 (countableFutureFiber T Q F (z.1,v)) ≠ 0 := by rwa [he]
    rw [futureFiberCoordinateKernel_apply,
      futureFiberTimeKernel_apply_good κ hT hQ hF _ hm,
      futureFiberTimeKernel_apply_good κ hT hQ hF _ hz,he]

theorem futureFiberCoordinateKernel_stationary [StandardBorelSpace V] [Nonempty V]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0) :
    ρ.bind (futureFiberCoordinateKernel ρ.condKernel hT hQ hF) = ρ := by
  apply bind_eq_of_real_integrals
  intro A hA
  have H := integral_countableFuture_conditional_probability ρ hQ hT hF hpos A hA
  refine (integral_congr_ae ?_).trans H.2
  filter_upwards [hpos] with z hz
  rw [futureFiberCoordinateKernel_apply,
    futureFiberTimeKernel_apply_good ρ.condKernel hT hQ hF z hz]
  exact congrArg ENNReal.toReal (Measure.map_apply measurable_prodMk_left hA)

theorem futureFiberCoordinateKernel_stationary_restrict
    [StandardBorelSpace V] [Nonempty V]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0)
    (E : Set (S × V)) (hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E) :
    (ρ.restrict E).bind (futureFiberCoordinateKernel ρ.condKernel hT hQ hF) =
      ρ.restrict E := by
  apply bind_eq_of_real_integrals
  intro A hA
  have H := setIntegral_countableFuture_conditional_probability ρ hQ hT hF hpos A hA E hE
  have he : (∫ z in E, (futureFiberCoordinateKernel ρ.condKernel hT hQ hF z).real A ∂ρ) =
      ∫ z in E,
        ((anchorNormalize (ρ.condKernel z.1) (countableFutureFiber T Q F z)).restrict
          (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A} ∂ρ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hpos] with z hz
    rw [futureFiberCoordinateKernel_apply,
      futureFiberTimeKernel_apply_good ρ.condKernel hT hQ hF z hz]
    exact congrArg ENNReal.toReal (Measure.map_apply measurable_prodMk_left hA)
  rw [he,H]
  simp only [Measure.real,Measure.restrict_apply hA]

end DukePrimeDegree

end

end OAI
