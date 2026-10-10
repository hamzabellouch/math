import OAI.Probability.InvariantIsing.Cavity.CavityReplicaProbabilityLaw
import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw

namespace OAI

/-! Replica observables retain their external disorder when a Gaussian
Gibbs-probability law is replaced or the external disorder is transported. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

theorem cavity_observed_replica_law_congr {Ω Z X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Measure Z) [IsProbabilityMeasure R]
    (ν η : Ω × Z → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ p, IsProbabilityMeasure (ν p)] [∀ p, IsProbabilityMeasure (η p)]
    (he : ∀ ω, R.map (fun z => ν (ω,z)) = R.map (fun z => η (ω,z)))
    (A : Ω → (ℕ → X) → Y) (hA : Measurable (Function.uncurry A)) :
    (disorderReplicaLaw (P.prod R) ν hν).map (fun p => A p.1.1 p.2) =
      (disorderReplicaLaw (P.prod R) η hη).map (fun p => A p.1.1 p.2) := by
  have hm : Measurable (fun p : (Ω × Z) × (ℕ → X) => A p.1.1 p.2) :=
    hA.comp (measurable_fst.fst.prodMk measurable_snd)
  apply Measure.ext_of_lintegral
  intro F hF
  have hFm : Measurable (fun p : (Ω × Z) × (ℕ → X) => F (A p.1.1 p.2)) := hF.comp hm
  rw [lintegral_map hF hm, lintegral_map hF hm]
  unfold disorderReplicaLaw
  rw [Measure.lintegral_compProd hFm, Measure.lintegral_compProd hFm]
  have hGν := hFm.lintegral_kernel_prod_right' (κ := replicaKernel ν hν)
  have hGη := hFm.lintegral_kernel_prod_right' (κ := replicaKernel η hη)
  rw [lintegral_prod _ hGν.aemeasurable, lintegral_prod _ hGη.aemeasurable]
  apply lintegral_congr
  intro ω
  exact cavity_replica_lintegral_same_probability_law R
    (fun z => ν (ω,z)) (fun z => η (ω,z))
    (hν.comp measurable_prodMk_left) (hη.comp measurable_prodMk_left) (he ω)
    (fun σ => F (A ω σ)) (hF.comp (hA.comp measurable_prodMk_left))

theorem cavity_observed_replica_law_transport {Ω Ξ Z X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (R : Measure Z) [IsProbabilityMeasure R] (φ : Ω → Ξ) (hφ : MeasurePreserving φ P Q)
    (η : Ξ × Z → Measure X) (hη : Measurable η) [∀ p, IsProbabilityMeasure (η p)]
    (A : Ξ → (ℕ → X) → Y) (hA : Measurable (Function.uncurry A)) :
    (disorderReplicaLaw (P.prod R) (fun p => η (φ p.1,p.2))
      (hη.comp ((hφ.measurable.comp measurable_fst).prodMk measurable_snd))).map
      (fun p => A (φ p.1.1) p.2) =
    (disorderReplicaLaw (Q.prod R) η hη).map (fun p => A p.1.1 p.2) := by
  let ν : Ω × Z → Measure X := fun p => η (φ p.1,p.2)
  have hν : Measurable ν := hη.comp ((hφ.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : (Ξ × Z) × (ℕ → X) => A p.1.1 p.2) :=
    hA.comp (measurable_fst.fst.prodMk measurable_snd)
  have hm' : Measurable (fun p : (Ω × Z) × (ℕ → X) => A (φ p.1.1) p.2) :=
    hA.comp ((hφ.measurable.comp measurable_fst.fst).prodMk measurable_snd)
  apply Measure.ext_of_lintegral
  intro F hF
  have hFm : Measurable (fun p : (Ξ × Z) × (ℕ → X) => F (A p.1.1 p.2)) := hF.comp hm
  have hFm' : Measurable (fun p : (Ω × Z) × (ℕ → X) => F (A (φ p.1.1) p.2)) := hF.comp hm'
  rw [lintegral_map hF hm', lintegral_map hF hm]
  unfold disorderReplicaLaw
  rw [Measure.lintegral_compProd hFm', Measure.lintegral_compProd hFm]
  have hGν := hFm'.lintegral_kernel_prod_right' (κ := replicaKernel ν hν)
  have hGη := hFm.lintegral_kernel_prod_right' (κ := replicaKernel η hη)
  rw [lintegral_prod _ hGν.aemeasurable, lintegral_prod _ hGη.aemeasurable]
  exact hφ.lintegral_comp hGη.lintegral_prod_right'

end InvariantIsing

end

end OAI
