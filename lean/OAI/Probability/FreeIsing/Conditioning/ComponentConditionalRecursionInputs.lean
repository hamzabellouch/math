import OAI.Probability.FreeIsing.Conditioning.NoisyBranchConditionalLaw
import OAI.Probability.FreeIsing.Estimates.IndependentOwnFamily
import OAI.Probability.FreeIsing.Posterior.ComponentObservationIndependence
import OAI.Probability.FreeIsing.Trees.BranchFlipGeometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def componentOwnChildFields {d : ℕ} {A : Type*} [MeasurableSpace A]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → ℝ) (c : Fin d) :
    Option {a : Fin d // c ≠ a} → ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ
  | none => fun p => F (p.1 (RootedBroadcast.branchRoot c))
      (p.2 (RootedBroadcast.branchRoot c))
  | some a => fun p => Real.artanh (selectedPosterior ρ F
      (childComponentIndexVertex c a.1)
      (prefixFlip c (RootedBroadcast.branchRoot a.1)) p)

private theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem measurable_componentOwnChildFields {d : ℕ} {A : Type*} [MeasurableSpace A]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → ℝ} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (i : Option {a : Fin d // c ≠ a}) :
    Measurable (componentOwnChildFields ρ F c i) := by
  cases i with
  | none =>
    exact hF.comp (show Measurable (fun p :
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (p.1 (RootedBroadcast.branchRoot c), p.2 (RootedBroadcast.branchRoot c))) by fun_prop)
  | some a => exact measurable_artanh.comp (measurable_selectedPosterior ρ hF _ _)

theorem HasFreeIsingLaw.iIndepFun_component_fields_cond_spin
    {d : ℕ} {θ : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (h0 : -1 ≤ θ) (h1 : θ ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → ℝ} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (s : IsingSpin) :
    let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    iIndepFun (componentOwnChildFields ρ F c)
      ρ[|{p | p.1 (RootedBroadcast.branchRoot c) = s}] := by
  let := hμ.isProbabilityMeasure
  let Ω := (TreeVertex d → IsingSpin) × (TreeVertex d → A)
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let I := {a : Fin d // c ≠ a}
  let S : Ω → IsingSpin := fun p => p.1 (RootedBroadcast.branchRoot c)
  let X (a : I) (p : Ω) : ComponentIndex a.1 → ℝ :=
    fun u => F (p.1 (childComponentIndexVertex c a.1 u))
      (p.2 (childComponentIndexVertex c a.1 u))
  let Y : Ω → ℝ := componentOwnChildFields ρ F c none
  let Z (a : I) : Ω → ℝ := componentOwnChildFields ρ F c (some a)
  have hS : Measurable S := (measurable_pi_apply _).comp measurable_fst
  have hX (a : I) : Measurable (X a) :=
    Measurable.of_eval fun u => hF.comp (show Measurable (fun p : Ω =>
      (p.1 (childComponentIndexVertex c a.1 u),
       p.2 (childComponentIndexVertex c a.1 u))) from
      ((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_snd))
  have hY : Measurable Y := measurable_componentOwnChildFields ρ hF c none
  have hZ (a : I) : Measurable (Z a) :=
    measurable_componentOwnChildFields ρ hF c (some a)
  have hmass : ρ (S ⁻¹' {s}) ≠ 0 := by
    change ρ {p | p.1 (RootedBroadcast.branchRoot c) = s} ≠ 0
    rw [hμ.planted_spin_event_mass]
    norm_num
  let : IsProbabilityMeasure ρ[|S ⁻¹' {s}] := cond_isProbabilityMeasure hmass
  have hchildren : iIndepFun X ρ[|S ⁻¹' {s}] :=
    iIndepFun_cond_fiber_of_iCondIndepFun hS hX
      (hμ.iCondIndepFun_forward_child_observations h0 h1 ν hF c) s hmass
  have hown : IndepFun Y (fun p a => X a p) ρ[|S ⁻¹' {s}] :=
    indepFun_cond_fiber_of_condIndepFun hS hY (Measurable.of_eval hX)
      (hμ.condIndepFun_own_forward_child_observations h0 h1 ν hF c) s
  have hsmall (a : I) :
      Measurable[MeasurableSpace.comap (X a) inferInstance, inferInstance] (Z a) :=
    measurable_artanh.comp stronglyMeasurable_condExp.measurable
  have hZchildren : iIndepFun Z ρ[|S ⁻¹' {s}] :=
    iIndep_of_iIndep_of_le hchildren (fun a => (hsmall a).comap_le)
  have hZown : IndepFun Y (fun p a => Z a p) ρ[|S ⁻¹' {s}] := by
    apply indep_of_indep_of_le hown le_rfl
    rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
    exact iSup_mono fun a => (hsmall a).comap_le
  change iIndepFun (componentOwnChildFields ρ F c) ρ[|S ⁻¹' {s}]
  exact iIndepFun_option_of_indep_tuple (μ := ρ[|S ⁻¹' {s}])
    (measurable_componentOwnChildFields ρ hF c) hZchildren hZown

end Problem367

end

end OAI
