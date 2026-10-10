import OAI.Probability.FreeIsing.Conditioning.Copies
import OAI.Probability.FreeIsing.Factors.InnovationFactorRecovery
import OAI.Probability.FreeIsing.Factors.Transport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

private theorem measurable_time_copy_fst
    {T W X Y : Type*} [MeasurableSpace T] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] {F : T × (W × X) → Y}
    (hF : Measurable F) :
    Measurable (fun q : T × (W × (X × X)) => F (q.1, (q.2.1, q.2.2.1))) :=
  hF.comp (by fun_prop)

private theorem measurable_time_copy_snd
    {T W X Y : Type*} [MeasurableSpace T] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace Y] {F : T × (W × X) → Y}
    (hF : Measurable F) :
    Measurable (fun q : T × (W × (X × X)) => F (q.1, (q.2.1, q.2.2.2))) :=
  hF.comp (by fun_prop)

theorem conditionalCopies_ae_eq_projected
    {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableEq Y]
    (mu : Measure W) [SFinite mu] (kappa : Kernel W X) [IsSFiniteKernel kappa]
    (E : X → Y) (hE : Measurable E)
    (hcopy : ∀ᵐ p ∂mu ⊗ₘ (kappa ×ₖ kappa), E p.2.1 = E p.2.2) :
    ∀ᵐ p ∂mu ⊗ₘ ((kappa.map E) ×ₖ (kappa.map E)), p.2.1 = p.2.2 := by
  rw [Kernel.map_prod_map kappa kappa hE hE, Measure.compProd_map (hE.prodMap hE)]
  apply (ae_map_iff (measurable_id.prodMap (hE.prodMap hE)).aemeasurable
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd))).2
  exact hcopy

theorem isFactorOfIID_of_projected_observation_conditionalCopies
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (hcopies : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
        (kappa ×ₖ kappa), E p.2.1 = E p.2.2) :
    IsFactorOfIID d theta := by
  let : IsMarkovKernel (kappa.map E) := Kernel.IsMarkovKernel.map kappa hE
  have hproject : (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa.map E =
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map id E) := Measure.compProd_map hE
  apply isFactorOfIID_of_equal_observation_conditionalCopies nu (kappa.map E)
  · have hdecode : Measurable (fun p : (TreeVertex d → A) × (TreeVertex d → ℕ → ℝ) =>
        SpinRecovery.decodeArray p.2) :=
      SpinRecovery.measurable_decodeArray.comp measurable_snd
    rw [hproject, Measure.map_map hdecode (measurable_id.prodMap hE)]
    exact hLaw
  · intro g
    have hpres : MeasurePreserving (Prod.map (relabel g) (S g))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa) :=
      ⟨(measurable_relabel g).prodMap (hS g), hjoint g⟩
    have heq : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa,
        (Prod.map id E) ((Prod.map (relabel g) (S g)) p) =
          (Prod.map (relabel g) (relabel g)) ((Prod.map id E) p) :=
      Filter.Eventually.of_forall (fun p => Prod.ext rfl (hEquiv g p.2))
    have hp := FactorTransport.map_invariant_of_ae_equivariant hpres
      ((measurable_relabel g).prodMap (measurable_relabel g))
      (measurable_id.prodMap hE) heq
    rw [← hproject] at hp
    exact (show MeasurePreserving (Prod.map (relabel g) (relabel g))
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa.map E)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa.map E) from
      ⟨(measurable_relabel g).prodMap (measurable_relabel g), hp⟩).quasiMeasurePreserving
  · exact conditionalCopies_ae_eq_projected _ kappa E hE hcopies

theorem isFactorOfIID_of_projected_observation_reference_collapse
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (hroot : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
        (kappa ×ₖ kappa), E p.2.1 o n = E p.2.2 o n) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_projected_observation_conditionalCopies
    nu kappa E hE S hS hEquiv hLaw hjoint
  have hcoord : ∀ v n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
      (kappa ×ₖ kappa), E p.2.1 v n = E p.2.2 v n := by
    intro v n
    obtain ⟨g, hg⟩ := exists_treeAut_map v o
    have hgo : g.toEquiv.symm o = v := by rw [← hg, Equiv.symm_apply_apply]
    have hT : MeasurePreserving (ObservationCopyStationarity.arrayRelabelEquiv (A := A) g)
        (Measure.infinitePi (fun _ : TreeVertex d => nu))
        (Measure.infinitePi (fun _ : TreeVertex d => nu)) :=
      ⟨measurable_relabel g, Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩
    have hi := conditionalCopies_invariant
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa
      (ObservationCopyStationarity.arrayRelabelEquiv g) (hS g) hT
      (by simpa [ObservationCopyStationarity.arrayRelabelEquiv] using hjoint g)
    have hpres : MeasurePreserving (Prod.map (relabel g) (Prod.map (S g) (S g)))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) :=
      ⟨(measurable_relabel g).prodMap ((hS g).prodMap (hS g)), hi⟩
    filter_upwards [hpres.quasiMeasurePreserving.ae (hroot n)] with p hp
    change E (S g p.2.1) o n = E (S g p.2.2) o n at hp
    rw [hEquiv, hEquiv] at hp
    simpa only [relabel, hgo] using hp
  have hall : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ
      (kappa ×ₖ kappa), ∀ v n, E p.2.1 v n = E p.2.2 v n :=
    ae_all_iff.2 (fun v => ae_all_iff.2 (hcoord v))
  filter_upwards [hall] with p hp
  exact funext (fun v => funext (hp v))

theorem isFactorOfIID_of_projected_innovation_field_zero
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (h h' : ℝ≥0 → ((TreeVertex d → A) × (X × X)) → ℝ)
    (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (h t.toNNReal p))))
    (hm' : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (h' t.toNNReal p))))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)))
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2
      ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) = 0)
    (hX : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa),
      E p.2.1 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa),
      E p.2.2 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_projected_observation_reference_collapse
    nu kappa E hE S hS hEquiv o hLaw hjoint
  exact observations_ae_eq_of_common_innovation_and_measurable_field_zero
    hm hm' hInt hzero hX hY

theorem isFactorOfIID_of_innovation_comparison
    {d : ℕ} {theta : ℝ} {A X : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    [StandardBorelSpace X]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (kappa : Kernel (TreeVertex d → A) X) [IsMarkovKernel kappa]
    (E : X → TreeVertex d → ℕ → ℝ) (hE : Measurable E)
    (S : TreeAut d → X → X) (hS : ∀ g, Measurable (S g))
    (hEquiv : ∀ g x, E (S g x) = relabel g (E x))
    (o : TreeVertex d)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray (E p.2))
        ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)))
    (hjoint : ∀ g : TreeAut d,
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa).map
        (Prod.map (relabel g) (S g)) =
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa)
    (H : ℝ≥0 → ((TreeVertex d → A) × X) → ℝ)
    (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (H t.toNNReal p))))
    (hInt : ∀ t, Integrable (fun p => (H t (p.1, p.2.1) - H t (p.1, p.2.2)) ^ 2)
      ((Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)))
    (hzero : ∀ t, (∫ p, (H t (p.1, p.2.1) - H t (p.1, p.2.2)) ^ 2
      ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ (kappa ×ₖ kappa)) = 0)
    (hInnovation : ∀ n, ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => nu)) ⊗ₘ kappa,
      E p.2 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (H t p)) n p) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_projected_innovation_field_zero nu kappa E hE S hS hEquiv
    o hLaw hjoint (fun t p => H t (p.1, p.2.1))
    (fun t p => H t (p.1, p.2.2)) W
  · exact measurable_time_copy_fst hm
  · exact measurable_time_copy_snd hm
  · exact hInt
  · exact hzero
  · intro n
    exact (measurePreserving_conditionalCopy_fst
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa).quasiMeasurePreserving.ae
        (hInnovation n)
  · intro n
    exact (measurePreserving_conditionalCopy_snd
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) kappa).quasiMeasurePreserving.ae
        (hInnovation n)

end Problem367

end

end OAI
