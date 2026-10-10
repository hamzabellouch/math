import OAI.Probability.DilutedSpin.RootProductLaw
import OAI.Probability.DilutedSpin.UpperRealEndpoint

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_old_new_compare
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) (liftOldEnergy E+v)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)|≤2*D*s/(N+1) := by
  apply cavity_old_average_error μ ξ ρ hρ theta field hθm hhm hC hH hθ hh
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous
    (B := H*N+D*s) _
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous r
  · intro E
    simpa only [cavityPoissonValue,liftOldEnergy,ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk,AddHom.coe_mk,Pi.add_def] using
      averagedEnergyRoot_newSpin_poisson μ ξ ν r s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf E
  · intro E
    simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
      (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i y a => hf i.1 _ a) E

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
namespace FiniteLaw
variable {R : Type} [Fintype R]
lemma expect_rect_castSucc (Q : FiniteLaw R) (k q : ℕ) (F : (Fin k×Fin q → R) → ℝ) :
    (pi (fun _ : Fin k => pi (fun _ : Fin (q+1) => Q))).expect
      (fun x => F (fun c => x c.1 c.2.castSucc))=
      (pi (fun _ : Fin k×Fin q => Q)).expect F := by
  apply (expect_pi_curry (fun (_ : Fin k) (_ : Fin (q+1)) => Q)
    (fun y : Fin k×Fin (q+1) → R => F (fun c => y (c.1,c.2.castSucc)))).trans
  exact expect_pi_injective (fun _ : Fin k×Fin (q+1) => Q)
    (fun z : Fin k×Fin q => (z.1,z.2.castSucc)) (by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun z : Fin k×Fin (q+1) => z.1) h
      · exact (Fin.castSucc_injective q) (congrArg (fun z : Fin k×Fin (q+1) => z.2) h)) F
end FiniteLaw
namespace PrescribedTree
open KernelTower
variable {Λ R : Type} [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
lemma activeRoot_site_mean (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)=1)
    (q k : ℕ) (z : RootPath (InteractionSample (q+1)) k) (h : ℝ) :
    (∫ b : RootPath (Fin (q+1) → R) k,backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k b) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k b z
        (fun y => h*spin (terminalState r y)))
      ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) := by
  simp_rw [activeRoot_site a r U x m hend q k]
  let F := fun b : Fin k → Fin (q+1) → R =>
    backwardLog r (piTower r (fun c : Fin k×Fin q => U (b c.1 c.2.castSucc)))
      (fun d => m d.castSucc) (fun y => siteLog (rootArray k z) h
        (fun c => x (b c.1 c.2.castSucc) (pathMap (fun w : Fin k×Fin q → Λ => w c) r y)))
  change (∫ b,F (rootArray k b) ∂rootLaw k (fun _ =>
    ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=_
  rw [integral_rootArray_eq_pi _ k F]
  rw [FiniteLaw.integral_pi_asProbability]
  rw [finite_trialLog]
  exact FiniteLaw.expect_rect_castSucc Q k q (fun b =>
    backwardLog r (piTower r (fun c => U (b c))) (fun d => m d.castSucc)
      (fun y => siteLog (rootArray k z) h (fun c => x (b c) (pathMap (fun w : Fin k×Fin q → Λ => w c) r y))))
end PrescribedTree
end DilutedSpinGlass

end

end OAI
