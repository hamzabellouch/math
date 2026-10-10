import OAI.Probability.RadialTransition.PressureContinuity

namespace OAI

universe uX uIndex uY uZ

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MeasurableFock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

lemma measurable_borel_sigma {ι : Type uIndex} [Countable ι] {Y : ι → Type uY}
    [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)] [∀ i, BorelSpace (Y i)]
    {Z : Type uZ} [MeasurableSpace Z] {f : (Σ i, Y i) → Z}
    (hf : ∀ i, Measurable (fun y : Y i => f ⟨i,y⟩)) :
    @Measurable _ _ (borel (Σ i, Y i)) _ f := by
  let : MeasurableSpace (Σ i, Y i) := borel (Σ i, Y i)
  let : BorelSpace (Σ i, Y i) := ⟨rfl⟩
  intro s hs
  have he : f ⁻¹' s = ⋃ i : ι, Sigma.mk i '' ((fun x : Y i => f ⟨i,x⟩) ⁻¹' s) :=
    (iUnion_image_preimage_sigma_mk_eq_self (f ⁻¹' s)).symm
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image.mpr (hf i hs))

lemma measurable_particle_prod {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Z]
    {f : ParticleState X → ParticleState Y → Z}
    (hf : ∀ m n, Measurable (fun p : (Fin m → X) × (Fin n → Y) => f ⟨m,p.1⟩ ⟨n,p.2⟩)) :
    Measurable (Function.uncurry f) := by
  let : MeasurableSpace (Σ m : ℕ, (Fin m → X) × ParticleState Y) := borel _
  let : BorelSpace (Σ m : ℕ, (Fin m → X) × ParticleState Y) := ⟨rfl⟩
  let e := Homeomorph.sigmaProdDistrib (X := fun m : ℕ => Fin m → X) (Y := ParticleState Y)
  have h : Measurable (fun q : Σ m : ℕ, (Fin m → X) × ParticleState Y =>
      f ⟨q.1,q.2.1⟩ q.2.2) := by
    apply measurable_borel_sigma
    intro m
    let : MeasurableSpace (Σ n : ℕ, (Fin n → Y) × (Fin m → X)) := borel _
    let : BorelSpace (Σ n : ℕ, (Fin n → Y) × (Fin m → X)) := ⟨rfl⟩
    let e' := Homeomorph.sigmaProdDistrib (X := fun n : ℕ => Fin n → Y) (Y := Fin m → X)
    have h' : Measurable (fun q : Σ n : ℕ, (Fin n → Y) × (Fin m → X) =>
        f ⟨m,q.2.2⟩ ⟨q.1,q.2.1⟩) := by
      apply measurable_borel_sigma
      intro n
      exact (hf m n).comp measurable_swap
    exact (h'.comp e'.continuous.measurable).comp measurable_swap
  exact h.comp e.continuous.measurable

variable (F : Multiset X → ℝ≥0∞)
def MeasurableConfiguration : Prop :=
  ∀ (s : Multiset X) (ι : Type) [Fintype ι], Measurable (fun x : ι → X => F (s+configurationMultiset x))

lemma measurable_particleObservable (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun x : ParticleState X => F (s+particleMultiset x)) := by
  apply measurable_borel_sigma
  intro n
  exact hF s (Fin n)

lemma measurable_particlePairObservable (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun p : ParticleState X × ParticleState X => F (s+particleMultiset p.1+particleMultiset p.2)) := by
  apply measurable_particle_prod (f := fun x y => F (s+particleMultiset x+particleMultiset y))
  intro m n
  have hh := (hF s (Fin m ⊕ Fin n)).comp
    (show Measurable (fun p : (Fin m → X) × (Fin n → X) => Sum.elim p.1 p.2) from by
      apply measurable_pi_iff.mpr
      intro i
      cases i with
      | inl i => exact (measurable_pi_apply i).comp measurable_fst
      | inr i => exact (measurable_pi_apply i).comp measurable_snd)
  change Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) at hh
  simpa only [configurationMultiset_sum, add_assoc, particleMultiset] using hh

lemma fockIntegral_eq_lintegral_meas (hF : MeasurableConfiguration F) (μ : Measure X) (z : ℝ) (s : Multiset X) :
    fockIntegral (fun _ι _ x => F (s+configurationMultiset x)) μ z =
      ∫⁻ x, F (s+particleMultiset x) ∂particleBase μ z := by
  rw [lintegral_particleBase μ z (measurable_particleObservable F hF s)]
  rfl

lemma particleBase_add_observable_meas (hF : MeasurableConfiguration F)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (μ+ν) z) =
      ∫⁻ x, ∫⁻ y, F (s+particleMultiset x+particleMultiset y) ∂particleBase ν z ∂particleBase μ z := by
  let G (ι : Type) [Fintype ι] (x : ι → X) := F (s+configurationMultiset x)
  have hG : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X), G ι (x ∘ e) = G κ x := by
    intros
    dsimp [G]
    rw [configurationMultiset_equiv]
  rw [← fockIntegral_eq_lintegral_meas F hF, fockIntegral_add G hG μ ν z]
  have hpair := (measurable_particlePairObservable F hF s)
  rw [lintegral_particleBase μ z hpair.lintegral_prod_right]
  apply tsum_congr
  intro m
  simp only [particleMultiset]
  have hinner (x : Fin m → X) :
      (∫⁻ y : ParticleState X, F (s+configurationMultiset x+configurationMultiset y.2) ∂particleBase ν z) =
      ∑' n : ℕ, fockCoeff z n * ∫⁻ y : Fin n → X, F (s+configurationMultiset x+configurationMultiset y)
        ∂Measure.pi (fun _ => ν) :=
    lintegral_particleBase ν z (measurable_particleObservable F hF (s+configurationMultiset x))
  simp_rw [hinner]
  rw [lintegral_tsum]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    rw [lintegral_const_mul' _ _ (by exact ENNReal.ofReal_ne_top)]
    rw [← mul_assoc]
    congr 1
    let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => X)
    have hs : ∀ i : Fin m ⊕ Fin n, SigmaFinite (Sum.elim (fun _ => μ) (fun _ => ν) i) := by
      intro i
      cases i
      · change SigmaFinite μ; infer_instance
      · change SigmaFinite ν; infer_instance
    have hp := measurePreserving_sumPiEquivProdPi_symm (Sum.elim (fun _ : Fin m => μ) (fun _ : Fin n => ν))
    rw [← hp.lintegral_comp (hF s (Fin m ⊕ Fin n))]
    change (∫⁻ p : (Fin m → X) × (Fin n → X), F (s+configurationMultiset (Sum.elim p.1 p.2))
      ∂(Measure.pi (fun _ => μ)).prod (Measure.pi (fun _ => ν))) = _
    have hmeas : Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) :=
      (hF s (Fin m ⊕ Fin n)).comp e.symm.measurable
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    dsimp [G]
    rw [configurationMultiset_sum, add_assoc]
  · intro n
    apply Measurable.aemeasurable
    apply Measurable.const_mul
    have hh := (hF s (Fin m ⊕ Fin n)).comp
      (show Measurable (fun p : (Fin m → X) × (Fin n → X) => Sum.elim p.1 p.2) from by
        apply measurable_pi_iff.mpr
        intro i
        cases i with
        | inl i => exact (measurable_pi_apply i).comp measurable_fst
        | inr i => exact (measurable_pi_apply i).comp measurable_snd)
    change Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) at hh
    simp only [configurationMultiset_sum, ← add_assoc] at hh
    exact hh.lintegral_prod_right

end MeasurableFock
section MeasurableMultiObservable
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]
omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma measurable_multiParticle_fixed (F : Multiset X → ℝ≥0∞)
    (hF : MeasurableConfiguration F) (s : Multiset X) (n : I → ℕ) :
    Measurable (fun x : ∀ i, Fin (n i) → X => F (s+∑ i, configurationMultiset (x i))) := by
  have hh := (hF s (Σ i, Fin (n i))).comp
    (show Measurable (fun x : ∀ i, Fin (n i) → X => fun p : Σ i, Fin (n i) => x p.1 p.2) from
      measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)))
  simpa only [Function.comp_def, configurationMultiset, Fintype.sum_sigma] using hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma measurable_configurationsInverse :
    @Measurable (I → ParticleState X) (Σ n : I → ℕ, ∀ i, Fin (n i) → X)
      _ (borel _) (configurationsEquiv (fun _ : I => X)).symm := by
  let : MeasurableSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := borel _
  let : BorelSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := ⟨rfl⟩
  exact (configurationsHomeomorph (fun _ : I => X)).symm.continuous.measurable

lemma measurable_multiParticleObservable (F : Multiset X → ℝ≥0∞)
    (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun x : I → ParticleState X => F (s+multiParticleMultiset x)) := by
  let : MeasurableSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := borel _
  let : BorelSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := ⟨rfl⟩
  have hc : Measurable (fun x : Σ n : I → ℕ, ∀ i, Fin (n i) → X =>
      F (s+∑ i, configurationMultiset (x.2 i))) :=
    measurable_borel_sigma (fun n => measurable_multiParticle_fixed F hF s n)
  change Measurable ((fun x : Σ n : I → ℕ, ∀ i, Fin (n i) → X =>
    F (s+∑ i, configurationMultiset (x.2 i))) ∘ (configurationsEquiv (fun _ : I => X)).symm)
  exact hc.comp (measurable_configurationsInverse (I := I) (X := X))

end MeasurableMultiObservable
section FiniteFock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (F : Multiset X → ℝ≥0∞) (hF : MeasurableConfiguration F)
include hF

lemma particleBase_zero_observable_meas (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (0 : Measure X) z) = F s := by
  rw [lintegral_particleBase _ _ (measurable_particleObservable F hF s)]
  rw [tsum_eq_single 0]
  · simp [particleMultiset, configurationMultiset]
  · intro n hn
    have hμ : Measure.pi (fun _ : Fin n => (0 : Measure X)) = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [Measure.pi_univ]
      simp [hn]
    rw [hμ, lintegral_zero_measure, mul_zero]

lemma particleBase_fin_sum_observable_meas (n : ℕ) (μ : Fin n → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, μ i) z) =
      ∫⁻ x, F (s+multiParticleMultiset x) ∂Measure.pi (fun i => particleBase (μ i) z) := by
  induction n generalizing s with
  | zero =>
    simp only [Fin.sum_univ_zero]
    rw [particleBase_zero_observable_meas F hF]
    simp [multiParticleMultiset]
  | succ n ih =>
    rw [Fin.sum_univ_succ, particleBase_add_observable_meas F hF]
    simp_rw [ih]
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ParticleState X) 0
    have hp := MeasurePreserving.symm e
      (measurePreserving_piFinSuccAbove (fun i => particleBase (μ i) z) 0)
    have hc := (measurable_multiParticleObservable F hF s (I := Fin (n+1)))
    rw [← hp.lintegral_comp hc]
    change _ = ∫⁻ p : ParticleState X × (Fin n → ParticleState X),
      F (s+multiParticleMultiset (e.symm p))
        ∂(particleBase (μ 0) z).prod (Measure.pi (fun i => particleBase (μ i.succ) z))
    have hpmeas : Measurable (fun p : ParticleState X × (Fin n → ParticleState X) =>
      F (s+multiParticleMultiset (e.symm p))) := hc.comp e.symm.measurable
    rw [lintegral_prod _ hpmeas.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    congr 1
    simp [multiParticleMultiset, Fin.sum_univ_succ, e,
      MeasurableEquiv.piFinSuccAbove_symm_apply, add_assoc]

end FiniteFock
end RadialTransition

end

end OAI
