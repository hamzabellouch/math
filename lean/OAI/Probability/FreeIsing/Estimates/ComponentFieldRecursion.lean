import OAI.Probability.FreeIsing.Estimates.ComponentFusionRecurrence
import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Gaussian.FiniteSignalFieldRecursion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

theorem HasFreeIsingLaw.gaussian_component_field_recursion
    {d : ℕ} (hd : 2 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
    ∀ᵐ z ∂ρ,
      Real.artanh (selectedPosterior ρ F (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) z) =
      PlantedSymmetry.observation t z (RootedBroadcast.branchRoot c) +
        ∑ a : {a : Fin d // c ≠ a}, cavityMessage (Real.tanh beta)
          (Real.artanh (selectedPosterior ρ F (childComponentIndexVertex c a.1)
            (prefixFlip c (RootedBroadcast.branchRoot a.1)) z)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
  let r := RootedBroadcast.branchRoot c
  let I := {a : Fin d // c ≠ a}
  let X (a : I) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun u : ComponentIndex a.1 => F (z.1 (childComponentIndexVertex c a.1 u))
      (z.2 (childComponentIndexVertex c a.1 u))
  let Y (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun _ : Unit => F (z.1 r) (z.2 r)
  let S (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := z.1 r
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  have hS : Measurable S := (measurable_pi_apply r).comp measurable_fst
  have hX (a : I) : Measurable (X a) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      (z.1 (childComponentIndexVertex c a.1 u), z.2 (childComponentIndexVertex c a.1 u))) by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => (z.1 r, z.2 r)) by fun_prop)
  have hθ0 := tanh_nonneg_of_beta_nonneg hb
  have hθ1 := Real.tanh_lt_one beta
  have hθlo : -1 ≤ Real.tanh beta := by linarith
  have hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X ρ :=
    hμ.iCondIndepFun_forward_child_observations hθlo hθ1.le (gaussianReal 0 t) hF c
  have hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
      Y (fun z a => X a z) ρ :=
    (hμ.condIndepFun_own_forward_child_observations hθlo hθ1.le
      (gaussianReal 0 t) hF c).comp
        (show Measurable (fun x : ℝ => fun _ : Unit => x) by fun_prop) measurable_id
  have hfair (s : IsingSpin) : ρ {z | S z = s} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r s
  have hstrict (a : I) : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance] z| < 1 :=
    (hμ.selected_child_parent_abs_le hθ0 hθ1.le (gaussianReal 0 t) hF c a.1).mono
      (fun _ hz => hz.trans_lt hθ1)
  have hOwnPost := hμ.selected_singleton_gaussian_posterior hb t r
  have hOwnStrict : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap Y inferInstance] z| < 1 := by
    filter_upwards [hOwnPost] with z hz
    change |selectedPosterior ρ F (fun _ : Unit => r) r z| < 1
    rw [hz]
    exact Real.abs_tanh_lt_one _
  let mAll := MeasurableSpace.comap (fun z a => X a z) inferInstance
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    Prod.instMeasurableSpace
  have hAll : Measurable (fun z a => X a z) := Measurable.of_eval hX
  have hf : finiteSignalField (fun a => MeasurableSpace.comap (X a) inferInstance)
      Finset.univ = mAll := by
    simp [mAll, finiteSignalField, MeasurableSpace.comap_process_pi]
  have hcard : Fintype.card I = d - 1 := by
    dsimp [I]
    simp [Fintype.card_subtype_compl]
  have hne : (Finset.univ : Finset I).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ, hcard]
    omega
  have hFields := iIndep_observationFields_cond_spin hS hX hCI hfair
  have hAllStrict : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | mAll] z| < 1 := by
    rw [← hf]
    exact abs_condExp_spin_finiteSignalField_lt_one (fun a => (hX a).comap_le)
      hS hstrict hfair hFields Finset.univ hne
  have hPairInd (s : IsingSpin) :
      Indep (MeasurableSpace.comap Y inferInstance) mAll (cond ρ {z | S z = s}) :=
    indepFun_cond_fiber_of_condIndepFun hS hY hAll hOwn s
  have hfield : MeasurableSpace.comap Y inferInstance ⊔ mAll =
      selectedObservationField F (componentIndexVertex (c := c)) := by
    simpa only [Y, X, r, RootedBroadcast.branchRoot, mAll, selectedObservationField,
      MeasurableSpace.comap_process_pi, iSup_const] using
      (componentObservationField_eq_own_sup_children F c).symm
  have hFullStrict : ∀ᵐ z ∂ρ,
      |selectedPosterior ρ F (componentIndexVertex (c := c)) r z| < 1 := by
    have h := abs_condExp_spin_sup_lt_one hY.comap_le hAll.comap_le hS
      hOwnStrict hAllStrict hfair hPairInd
    rw [hfield] at h
    exact h
  have hChildStrict (a : I) : ∀ᵐ z ∂ρ,
      |selectedPosterior ρ F (childComponentIndexVertex c a.1)
        (prefixFlip c (RootedBroadcast.branchRoot a.1)) z| < 1 := by
    exact (childComponentPosterior_identDistrib hμ (gaussianReal 0 t) hF c a.1).symm.ae_snd
      (measurableSet_lt measurable_abs measurable_const) hFullStrict
  have hChild (a : I) : ∀ᵐ z ∂ρ,
      Real.artanh (ρ[fun z => spinSign (S z) |
        MeasurableSpace.comap (X a) inferInstance] z) =
      cavityMessage (Real.tanh beta) (Real.artanh (selectedPosterior ρ F
        (childComponentIndexVertex c a.1) (prefixFlip c (RootedBroadcast.branchRoot a.1)) z)) := by
    filter_upwards [hμ.selectedPosterior_parent_childComponent hθlo hθ1.le
      (gaussianReal 0 t) hF c a.1, hChildStrict a] with z hz hi
    change selectedPosterior ρ F (childComponentIndexVertex c a.1) r z =
      Real.tanh beta * selectedPosterior ρ F (childComponentIndexVertex c a.1)
        (prefixFlip c (RootedBroadcast.branchRoot a.1)) z at hz
    change Real.artanh (selectedPosterior ρ F (childComponentIndexVertex c a.1) r z) = _
    rw [hz, cavityMessage, Real.tanh_artanh (abs_lt.mp hi)]
  have hSum := artanh_condExp_spin_finiteSignalField (fun a => (hX a).comap_le)
    hS hstrict hfair hFields Finset.univ hne
  rw [hf] at hSum
  have hPair := artanh_condExp_spin_sup hY.comap_le hAll.comap_le hS
    hOwnStrict hAllStrict hfair hPairInd
  rw [hfield] at hPair
  filter_upwards [hPair, hSum, hOwnPost, ae_all_iff.2 hChild] with z hp hs ho hc
  change Real.artanh (selectedPosterior ρ F (componentIndexVertex (c := c)) r z) = _ at hp ⊢
  rw [hp]
  change Real.artanh (selectedPosterior ρ F (fun _ : Unit => r) r z) + _ = _
  rw [ho, Real.artanh_tanh, hs]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => hc a)

end Problem367

end

end OAI
