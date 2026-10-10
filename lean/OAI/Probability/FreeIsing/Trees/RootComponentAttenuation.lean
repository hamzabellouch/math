import Mathlib.MeasureTheory.Function.FactorsThrough
import OAI.Probability.FreeIsing.Conditioning.StatisticLoss
import OAI.Probability.FreeIsing.Posterior.ComponentPosteriorTilt

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

local instance rootComponentAttenuationMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance rootComponentAttenuationNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.condIndepFun_root_others_componentPosterior
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let q := selectedPosterior P F (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)
    noisyRootOtherArray c ⟂ᵢ[fun z => z.1 (RootedBroadcast.root d),
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst); P] q := by
  dsimp only
  let v (u : ComponentIndex c) : RootedBroadcast.BranchVertex c :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) → (ComponentIndex c → B) :=
    fun p u => F (p.1 (v u)) (p.2 (v u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A) => (p.1 (v u), p.2 (v u))) from by fun_prop)
  have hObs : Measurable[(inferInstance : MeasurableSpace
      ((RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A))).comap (noisyBranchArray c)]
      (fun p i => F (p.1 (componentIndexVertex (c := c) i))
        (p.2 (componentIndexVertex i))) :=
    hG.comp (comap_measurable (noisyBranchArray c))
  have hq : Measurable[(inferInstance : MeasurableSpace
      ((RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A))).comap (noisyBranchArray c)]
      (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c)) :=
    stronglyMeasurable_condExp.measurable.mono hObs.comap_le le_rfl
  obtain ⟨Q, hQ, hqQ⟩ := hq.exists_eq_measurable_comp
  rw [hqQ]
  exact (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c).comp
    measurable_id hQ

namespace ComponentSignalAttenuation

open PlantedSymmetry

theorem condDistrib_posteriorMean_root
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (c : Fin d) (t : ℝ≥0) (a : IsingSpin) :
    condDistrib (posteriorMean μ c t) (fun z => z.1 (RootedBroadcast.root d))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) a =
        linearSignalTilt (posteriorLaw μ c t) id (spinSign a * theta) := by
  exact hμ.condDistrib_componentPosterior_root h0 h1 (gaussianReal 0 t)
    (F := fun s z => (t : ℝ) * spinSign s + z)
    (((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd) c a

theorem condExp_attenuation_le_critical_root_others
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (G : NoisyRootOtherData ℝ c → B) (hG : Measurable G)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let X := G ∘ noisyRootOtherArray c
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (posteriorMean μ c t v)) ^ 2 |
          mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := hμ.isProbabilityMeasure
  dsimp only
  have hchannel : Measurable (Function.uncurry
      (fun s z => (t : ℝ) * spinSign s + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hind := (hμ.condIndepFun_root_others_componentPosterior
    (by linarith) hθ1.le (gaussianReal 0 t) hchannel c).comp hG measurable_id
  apply condExp_attenuation_le_critical_of_condIndep (eta := spinSign) hμ hθ0 hθ1 c hcritical ht
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    (hG.comp (measurable_noisyRootOtherArray c)) (measurable_posteriorMean μ c t)
    hs hind
  · exact Filter.Eventually.of_forall (fun w => by
      cases h : w.1 (RootedBroadcast.root d) <;> norm_num [spinSign, h])
  · exact Filter.Eventually.of_forall (fun w =>
      condDistrib_posteriorMean_root hμ (by linarith) hθ1.le c t _)

end ComponentSignalAttenuation

end Problem367

end

end OAI
