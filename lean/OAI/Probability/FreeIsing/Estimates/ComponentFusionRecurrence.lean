import OAI.Probability.FreeIsing.Conditioning.ComponentInformationUpper
import OAI.Probability.FreeIsing.Conditioning.FiniteObservationInformation
import OAI.Probability.FreeIsing.Conditioning.NoisyBranchConditionalLaw
import OAI.Probability.FreeIsing.Critical.Information
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Posterior.ComponentObservationDecomposition
import OAI.Probability.FreeIsing.Posterior.ComponentObservationIndependence
import OAI.Probability.FreeIsing.Posterior.ComponentObservationRegression

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

theorem HasFreeIsingLaw.selected_child_parent_abs_le
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    ∀ᵐ z ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      |selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (childComponentIndexVertex c a) (RootedBroadcast.branchRoot c) z| ≤ theta := by
  filter_upwards [hμ.selectedPosterior_parent_childComponent (by linarith) h1 ν hF c a,
    selectedPosterior_abs_le_one (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      F (childComponentIndexVertex c a) (prefixFlip c (RootedBroadcast.branchRoot a))] with z hz hb
  rw [hz, abs_mul, abs_of_nonneg h0]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb h0

theorem HasFreeIsingLaw.selected_child_parent_secondMoment
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    (∫ z, (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      F (childComponentIndexVertex c a) (RootedBroadcast.branchRoot c) z) ^ 2
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) =
      theta ^ 2 * ∫ z, (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) z) ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)) := by
  have h := hμ.selectedPosterior_parent_childComponent h0 h1 ν hF c a
  have heq := integral_congr_ae (h.fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at heq
  rw [heq]
  simp only [mul_pow]
  rw [integral_const_mul]
  congr 1
  exact ((childComponentPosterior_identDistrib hμ ν hF c a).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)).integral_eq

def gaussianComponentInformation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (c : Fin d) : ℝ :=
  ∫ z, (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x) (componentIndexVertex (c := c))
    (RootedBroadcast.branchRoot c) z) ^ 2
    ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)

theorem HasFreeIsingLaw.gaussian_component_information_fusion
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    gaussianComponentInformation μ t c ≤
      ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 * gaussianComponentInformation μ t c -
        2 * (1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4 *
          (gaussianComponentInformation μ t c) ^ 2 + ((t : ℝ) + (t : ℝ) ^ 2) := by
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
  have hbound (a : I) : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance] z| ≤
        Real.tanh beta :=
    hμ.selected_child_parent_abs_le hθ0 hθ1.le (gaussianReal 0 t) hF c a.1
  have hstrict (a : I) : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance] z| < 1 :=
    (hbound a).mono (fun _ hz => hz.trans_lt hθ1)
  have hsym (a : I) : (ρ.map (ρ[fun z => spinSign (S z) |
      MeasurableSpace.comap (X a) inferInstance])).map (fun x : ℝ => -x) =
      ρ.map (ρ[fun z => spinSign (S z) | MeasurableSpace.comap (X a) inferInstance]) :=
    hμ.selected_gaussian_posteriorLaw_neg_invariant t t (childComponentIndexVertex c a.1) r
  have hOwnStrict : ∀ᵐ z ∂ρ,
      |ρ[fun z => spinSign (S z) | MeasurableSpace.comap Y inferInstance] z| < 1 := by
    filter_upwards [hμ.selected_singleton_gaussian_posterior hb t r] with z hz
    change |selectedPosterior ρ F (fun _ : Unit => r) r z| < 1
    rw [hz]
    exact Real.abs_tanh_lt_one _
  have hOwnSym : (ρ.map (ρ[fun z => spinSign (S z) |
      MeasurableSpace.comap Y inferInstance])).map (fun x : ℝ => -x) =
      ρ.map (ρ[fun z => spinSign (S z) | MeasurableSpace.comap Y inferInstance]) :=
    hμ.selected_gaussian_posteriorLaw_neg_invariant t t (fun _ : Unit => r) r
  have hcard : Fintype.card I = d - 1 := by
    dsimp [I]
    simp [Fintype.card_subtype_compl]
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card I by rw [hcard]; omega)
  have hfamily := condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
    hS hX hCI hfair hstrict hsym hY hOwn hOwnStrict hOwnSym hab (hbound a) (hbound b) hθ1
  have hfield : MeasurableSpace.comap (fun z => (Y z, fun a => X a z)) inferInstance =
      selectedObservationField F (componentIndexVertex (c := c)) := by
    simpa only [Y, X, r, RootedBroadcast.branchRoot, selectedObservationField,
      Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
      MeasurableSpace.comap_process_pi, iSup_const] using
      (componentObservationField_eq_own_sup_children F c).symm
  rw [hfield] at hfamily
  have hchild (a : I) : (∫ z, (ρ[fun z => spinSign (S z) |
      MeasurableSpace.comap (X a) inferInstance] z) ^ 2 ∂ρ) =
      (Real.tanh beta) ^ 2 * gaussianComponentInformation μ t c :=
    hμ.selected_child_parent_secondMoment hθlo hθ1.le (gaussianReal 0 t) hF c a.1
  simp_rw [hchild] at hfamily
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hfamily
  have hown := hμ.selected_singleton_information_le hb t r
  change (∫ z, (ρ[fun z => spinSign (S z) |
    MeasurableSpace.comap Y inferInstance] z) ^ 2 ∂ρ) ≤ (t : ℝ) + (t : ℝ) ^ 2 at hown
  change gaussianComponentInformation μ t c ≤ _ at hfamily
  nlinarith [hfamily, hown]

theorem HasFreeIsingLaw.gaussian_component_critical_information_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d) :
    gaussianComponentInformation μ t c ≤
      Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4)) *
        Real.sqrt (t : ℝ) := by
  have hθ0 := tanh_nonneg_of_beta_nonneg hb
  have hθpos : 0 < Real.tanh beta := by
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (le_of_not_gt h) hθ0
    simp [hz] at hcritical
  exact critical_information_upper_of_fusion hθpos (Real.tanh_lt_one beta)
    hcritical t.coe_nonneg ht (hμ.gaussian_component_information_fusion hd hb t c)

end Problem367

end

end OAI
