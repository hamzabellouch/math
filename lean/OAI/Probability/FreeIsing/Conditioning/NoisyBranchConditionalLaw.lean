import OAI.Probability.FreeIsing.Conditioning.DiscreteConditioning
import OAI.Probability.FreeIsing.Trees.NoisyBranchIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance noisyBranchConditionalLawMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.planted_spin_event_mass
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (v : TreeVertex d) (s : IsingSpin) :
    (μ.prod (Measure.infinitePi ν))
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} = 1 / 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hset :
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} =
        {x : TreeVertex d → IsingSpin | x v = s} ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one, hμ.marginal]
  norm_num [ENNReal.ofReal_div_of_pos]

def plantedBranchObservations {d : ℕ} {A T : Type*}
    (a : T → ℝ) (B : TreeVertex d → T → A → ℝ) (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A))
    (v : RootedBroadcast.BranchVertex c) (t : T) : ℝ :=
  a t * (z.1 v.val).toReal + B v.val t (z.2 v.val)

theorem measurable_plantedBranchObservations {d : ℕ} {A T : Type*}
    [MeasurableSpace A] (a : T → ℝ) (B : TreeVertex d → T → A → ℝ)
    (hB : ∀ v t, Measurable (B v t)) (c : Fin d) :
    Measurable (plantedBranchObservations a B c) := by
  apply Measurable.of_eval
  intro v
  apply Measurable.of_eval
  intro t
  exact ((measurable_spinToReal.comp ((measurable_pi_apply v.val).comp
    measurable_fst)).const_mul (a t)).add
      ((hB v.val t).comp ((measurable_pi_apply v.val).comp measurable_snd))

theorem HasFreeIsingLaw.iIndepFun_planted_branches_cond_root
    {d : ℕ} {theta : ℝ} {A T : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (a : T → ℝ) (B : TreeVertex d → T → A → ℝ)
    (hB : ∀ v t, Measurable (B v t)) (s : IsingSpin) :
    iIndepFun (plantedBranchObservations a B)
      (μ.prod (Measure.infinitePi ν))[|
        {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) |
          z.1 (RootedBroadcast.root d) = s}] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hroot : Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      z.1 (RootedBroadcast.root d)) :=
    (measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst
  apply iIndepFun_cond_fiber_of_iCondIndepFun hroot
    (measurable_plantedBranchObservations a B hB)
    (hμ.iCondIndepFun_planted_branch_observations h0 h1 ν a B hB) s
  change (μ.prod (Measure.infinitePi ν))
    {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) |
      z.1 (RootedBroadcast.root d) = s} ≠ 0
  rw [hμ.planted_spin_event_mass ν]
  norm_num

theorem HasFreeIsingLaw.map_planted_branches_cond_root
    {d : ℕ} {theta : ℝ} {A T : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (a : T → ℝ) (B : TreeVertex d → T → A → ℝ)
    (hB : ∀ v t, Measurable (B v t)) (s : IsingSpin) :
    ((μ.prod (Measure.infinitePi ν))[|
        {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) |
          z.1 (RootedBroadcast.root d) = s}]).map
      (fun z c => plantedBranchObservations a B c z) =
    Measure.infinitePi (fun c : Fin d =>
      ((μ.prod (Measure.infinitePi ν))[|
        {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) |
          z.1 (RootedBroadcast.root d) = s}]).map (plantedBranchObservations a B c)) := by
  exact (hμ.iIndepFun_planted_branches_cond_root h0 h1 ν a B hB s).map_fun_eq_infinitePi_map
    (measurable_plantedBranchObservations a B hB)

end Problem367

end

end OAI
