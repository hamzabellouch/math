import OAI.Probability.FreeIsing.Conditioning.CopyInvariance
import OAI.Probability.FreeIsing.Posterior.ObservationFactorRecovery
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ObservationCopyStationarity

def arrayRelabelEquiv {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) : (TreeVertex d → A) ≃ᵐ (TreeVertex d → A) where
  toFun := relabel g
  invFun := fun x v => x (g.toEquiv v)
  left_inv := by intro x; funext v; simp [relabel]
  right_inv := by intro x; funext v; simp [relabel]
  measurable_toFun := measurable_relabel g
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem canonical_conditionalCopies_invariant
    {d : ℕ} {A : Type*} [MeasurableSpace A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (rho : Measure ((TreeVertex d → A) × (TreeVertex d → ℕ → ℝ)))
    [IsProbabilityMeasure rho]
    (hfirst : rho.fst = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (g : TreeAut d)
    (hjoint : rho.map (Prod.map (relabel g) (relabel g)) = rho) :
    (rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)).map
      (Prod.map (relabel g) (Prod.map (relabel g) (relabel g))) =
      rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel) := by
  have hT : MeasurePreserving (arrayRelabelEquiv (A := A) g) rho.fst rho.fst := by
    refine ⟨measurable_relabel g, ?_⟩
    rw [hfirst]
    exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective
  have hdis : rho.fst ⊗ₘ rho.condKernel = rho :=
    Measure.disintegrate rho rho.condKernel
  apply conditionalCopies_invariant rho.fst rho.condKernel (arrayRelabelEquiv g)
    (measurable_relabel g) hT
  simpa [hdis, arrayRelabelEquiv] using hjoint

theorem ae_eq_arrays_of_reference_vertex
    {d : ℕ} {A : Type*} [MeasurableSpace A]
    (mu : Measure ((TreeVertex d → A) ×
      ((TreeVertex d → ℕ → ℝ) × (TreeVertex d → ℕ → ℝ))))
    (o : TreeVertex d)
    (hinvariant : ∀ g : TreeAut d,
      mu.map (Prod.map (relabel g) (Prod.map (relabel g) (relabel g))) = mu)
    (hroot : ∀ n, ∀ᵐ p ∂mu, p.2.1 o n = p.2.2 o n) :
    ∀ᵐ p ∂mu, p.2.1 = p.2.2 := by
  have hcoord : ∀ v n, ∀ᵐ p ∂mu, p.2.1 v n = p.2.2 v n := by
    intro v n
    obtain ⟨g, hg⟩ := exists_treeAut_map v o
    have hgo : g.toEquiv.symm o = v := by
      rw [← hg, Equiv.symm_apply_apply]
    have hpres : MeasurePreserving
        (Prod.map (relabel g) (Prod.map (relabel g) (relabel g))) mu mu :=
      ⟨(measurable_relabel g).prodMap
        ((measurable_relabel g).prodMap (measurable_relabel g)), hinvariant g⟩
    filter_upwards [hpres.quasiMeasurePreserving.ae (hroot n)] with p hp
    change p.2.1 (g.toEquiv.symm o) n = p.2.2 (g.toEquiv.symm o) n at hp
    simpa only [hgo] using hp
  have hall : ∀ᵐ p ∂mu, ∀ v n, p.2.1 v n = p.2.2 v n :=
    ae_all_iff.2 (fun v => ae_all_iff.2 (hcoord v))
  filter_upwards [hall] with p hp
  exact funext (fun v => funext (hp v))

theorem isFactorOfIID_of_joint_observation_reference_collapse
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (rho : Measure ((TreeVertex d → A) × (TreeVertex d → ℕ → ℝ)))
    [IsProbabilityMeasure rho] (o : TreeVertex d)
    (hfirst : rho.fst = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2) rho))
    (hjoint : ∀ g : TreeAut d, rho.map (Prod.map (relabel g) (relabel g)) = rho)
    (hroot : ∀ n, ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      p.2.1 o n = p.2.2 o n) :
    IsFactorOfIID d theta := by
  have hcopies := ae_eq_arrays_of_reference_vertex
    (rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)) o
    (fun g => canonical_conditionalCopies_invariant nu rho hfirst g (hjoint g)) hroot
  have hdis : (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
      rho.condKernel = rho := by
    rw [← hfirst]
    exact Measure.disintegrate rho rho.condKernel
  apply isFactorOfIID_of_equal_observation_conditionalCopies nu rho.condKernel
  · simpa only [hdis] using hLaw
  · intro g
    rw [hdis]
    exact (show MeasurePreserving (Prod.map (relabel g) (relabel g)) rho rho from
      ⟨(measurable_relabel g).prodMap (measurable_relabel g), hjoint g⟩).quasiMeasurePreserving
  · simpa only [hfirst] using hcopies

theorem isFactorOfIID_of_joint_observation_reference_zero
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (rho : Measure ((TreeVertex d → A) × (TreeVertex d → ℕ → ℝ)))
    [IsProbabilityMeasure rho] (o : TreeVertex d)
    (hfirst : rho.fst = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2) rho))
    (hjoint : ∀ g : TreeAut d, rho.map (Prod.map (relabel g) (relabel g)) = rho)
    (hInt : ∀ n, Integrable (fun p => (p.2.1 o n - p.2.2 o n) ^ 2)
      (rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)))
    (hzero : ∀ n, (∫ p, (p.2.1 o n - p.2.2 o n) ^ 2
      ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)) = 0) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_joint_observation_reference_collapse nu rho o hfirst hLaw hjoint
  exact fun n => ae_eq_of_integral_sq_sub_eq_zero (hInt n) (hzero n)

end Problem367.ObservationCopyStationarity

end

end OAI
