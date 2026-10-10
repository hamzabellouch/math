import OAI.Probability.FreeIsing.Conditioning.FactorRecovery
import OAI.Probability.FreeIsing.Estimates.UniformSampler
import OAI.Probability.FreeIsing.Factors.ContinuousRecovery
import OAI.Probability.FreeIsing.Spins.Recovery

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem ae_eq_array_of_coordinate_integral_sq_sub_eq_zero
    {O I J : Type*} [MeasurableSpace O] [Countable I] [Countable J]
    {mu : Measure O} {f g : O → I → J → ℝ}
    (hInt : ∀ i j, Integrable (fun z => (f z i j - g z i j) ^ 2) mu)
    (hzero : ∀ i j, (∫ z, (f z i j - g z i j) ^ 2 ∂mu) = 0) :
    f =ᵐ[mu] g := by
  have hcoord : ∀ i j, ∀ᵐ z ∂mu, f z i j = g z i j :=
    fun i j => ae_eq_of_integral_sq_sub_eq_zero (hInt i j) (hzero i j)
  have hall : ∀ᵐ z ∂mu, ∀ i j, f z i j = g z i j :=
    ae_all_iff.2 (fun i => ae_all_iff.2 (hcoord i))
  filter_upwards [hall] with z hz
  exact funext (fun i => funext (hz i))

theorem isFactorOfIID_of_equal_observation_conditionalCopies
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) (TreeVertex d → ℕ → ℝ))
    [IsMarkovKernel kappa]
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d, Measure.QuasiMeasurePreserving
      (fun p : (TreeVertex d → A) × (TreeVertex d → ℕ → ℝ) =>
        (relabel g p.1, relabel g p.2))
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa))
    (hcopies : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
        (kappa ×ₖ kappa), p.2.1 = p.2.2) :
    IsFactorOfIID d theta := by
  obtain ⟨F, hF, _, hmap, heq⟩ :=
    exists_ae_equivariant_recovery_of_conditionalCopies
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa
      (fun g : TreeAut d => relabel g) (fun g : TreeAut d => relabel g)
      measurable_relabel measurable_relabel hjoint hcopies
  obtain ⟨sample, hsample, hsampleLaw⟩ := exists_uniform01_sampler nu
  apply isFactorOfIID_of_product_sampler nu sample hsample hsampleLaw
    (SpinRecovery.decodeArray ∘ F) (SpinRecovery.measurable_decodeArray.comp hF)
  · rw [← Measure.map_map SpinRecovery.measurable_decodeArray hF, hmap,
      Measure.map_map SpinRecovery.measurable_decodeArray measurable_snd]
    exact hLaw
  · intro g
    filter_upwards [heq g] with w hw
    change SpinRecovery.decodeArray (F (relabel g w)) =
      relabel g (SpinRecovery.decodeArray (F w))
    rw [hw, SpinRecovery.decodeArray_relabel]

theorem isFactorOfIID_of_observation_conditionalCopies_zero
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) (TreeVertex d → ℕ → ℝ))
    [IsMarkovKernel kappa]
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d, Measure.QuasiMeasurePreserving
      (fun p : (TreeVertex d → A) × (TreeVertex d → ℕ → ℝ) =>
        (relabel g p.1, relabel g p.2))
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa))
    (hInt : ∀ v n, Integrable (fun p => (p.2.1 v n - p.2.2 v n) ^ 2)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)))
    (hzero : ∀ v n, (∫ p, (p.2.1 v n - p.2.2 v n) ^ 2
      ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) = 0) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_equal_observation_conditionalCopies nu kappa hLaw hjoint
  exact ae_eq_array_of_coordinate_integral_sq_sub_eq_zero hInt hzero

theorem isFactorOfIID_of_joint_observation_conditionalCopies_zero
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (rho : Measure ((TreeVertex d → A) × (TreeVertex d → ℕ → ℝ)))
    [IsProbabilityMeasure rho]
    (hfirst : rho.fst = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2) rho))
    (hjoint : ∀ g : TreeAut d, Measure.QuasiMeasurePreserving
      (fun p : (TreeVertex d → A) × (TreeVertex d → ℕ → ℝ) =>
        (relabel g p.1, relabel g p.2)) rho rho)
    (hInt : ∀ v n, Integrable (fun p => (p.2.1 v n - p.2.2 v n) ^ 2)
      (rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)))
    (hzero : ∀ v n, (∫ p, (p.2.1 v n - p.2.2 v n) ^ 2
      ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)) = 0) :
    IsFactorOfIID d theta := by
  have hdis : (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
      rho.condKernel = rho := by
    rw [← hfirst]
    exact Measure.disintegrate rho rho.condKernel
  apply isFactorOfIID_of_observation_conditionalCopies_zero nu rho.condKernel
  · simpa only [hdis] using hLaw
  · simpa only [hdis] using hjoint
  · simpa only [hfirst] using hInt
  · simpa only [hfirst] using hzero

end Problem367

end

end OAI
