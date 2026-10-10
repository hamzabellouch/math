import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedRestrictionLimit

namespace OAI

/-! # Infinite future conditioning on positive-mass leaf atoms

Finite conditioned kernels converge to restriction to the whole itinerary
atom. Martingale convergence identifies this limit with conditioning on
the increasing union of the actual transverse-and-label sigma algebras.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

def labelFiber {N : ℕ} (Q : S × T → Fin N) (z : S × T) : Set T :=
  {t | Q (z.1,t)=Q z}

@[instance_reducible] def transverseLabelSigma {N : ℕ} (Q : S × T → Fin N) : MeasurableSpace (S × T) :=
  MeasurableSpace.comap (fun z => (z.1,Q z)) inferInstance

theorem conditionalEntropy_infinite_label_restriction
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {M : ℕ} {P : S × T → Fin M} (hP : Measurable P)
    {k : ℕ → ℕ} (Q : ∀ n, S × T → Fin (k n)) (hQ : ∀ n, Measurable (Q n))
    (hmono : Monotone (fun n => transverseLabelSigma (Q n)))
    (hdec : ∀ z, Antitone (fun n => labelFiber (Q n) z))
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (⋂ n, labelFiber (Q n) z) ≠ 0) :
    conditionalSigmaEntropy ρ P (⨆ n, transverseLabelSigma (Q n)) =
      ∫ z, observationEntropy
        ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
          (⋂ n, labelFiber (Q n) z)) (fun t => P (z.1,t)) ∂ρ := by
  let F : ℕ → S × T → ℝ := fun n z => observationEntropy
    ((anchorNormalize (ρ.condKernel z.1) (labelFiber (Q n) z)).restrict (labelFiber (Q n) z))
    (fun t => P (z.1,t))
  let G : S × T → ℝ := fun z => observationEntropy
    ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
      (⋂ n, labelFiber (Q n) z)) (fun t => P (z.1,t))
  let K n := (ρ.map (finiteLabelLift (Q n))).condKernel
  let L (n : ℕ) (z : S × T) := observationEntropy (K n (z.1,Q n z)) (fun t => P (z.1,t))
  have hFL n : F n =ᵐ[ρ] L n := by
    filter_upwards [finiteLabelLift_condKernel ρ (hQ n)] with z hz
    exact congrArg (fun ν => observationEntropy ν (fun t => P (z.1,t))) hz.2.symm
  have hLm n : Measurable (L n) := by
    let R : (S × Fin (k n)) × T → Fin M := fun z => P (z.1.1,z.2)
    have hR : ∀ a, MeasurableSet {z | R z=a} := by
      intro a
      exact (hP.comp (measurable_fst.fst.prodMk measurable_snd)) (measurableSet_singleton a)
    exact (measurable_fiber_observationEntropy (K n) R hR).comp (measurable_fst.prodMk (hQ n))
  have hFm n : AEStronglyMeasurable (F n) ρ :=
    (hLm n).aestronglyMeasurable.congr (hFL n).symm
  have hbound n : ∀ᵐ z ∂ρ, ‖F n z‖ ≤ (M:ℝ) := by
    filter_upwards [hFL n] with z hz
    rw [hz]
    change ‖finiteShannon (fun a => (K n (z.1,Q n z)).real {t | P (z.1,t)=a})‖ ≤ _
    simpa only [Fintype.card_fin] using finiteShannon_norm_le_card_of_unit_bounds
      (fun a => (K n (z.1,Q n z)).real {t | P (z.1,t)=a})
      (fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩)
  have hlim : ∀ᵐ z ∂ρ, Tendsto (fun n => F n z) atTop (𝓝 (G z)) := by
    filter_upwards [hpos] with z hz
    exact normalized_restriction_entropy_tendsto (ρ.condKernel z.1)
      (fun n => labelFiber (Q n) z)
      (fun n => measurableSet_eq_fun ((hQ n).comp measurable_prodMk_left) measurable_const)
      (hdec z) hz (fun t => P (z.1,t))
      (fun a => (hP.comp measurable_prodMk_left) (measurableSet_singleton a))
  have hlimI := tendsto_integral_of_dominated_convergence (fun _ : S × T => (M:ℝ))
    hFm (integrable_const _) hbound hlim
  have hle n : transverseLabelSigma (Q n) ≤ (inferInstance : MeasurableSpace (S × T)) :=
    (measurable_fst.prodMk (hQ n)).comap_le
  have hlimE := conditionalSigmaEntropy_tendsto_iSup ρ P
    (fun n => transverseLabelSigma (Q n)) hmono hle
  have hEq n : conditionalSigmaEntropy ρ P (transverseLabelSigma (Q n)) = ∫ z, F n z ∂ρ :=
    conditionalEntropy_transverse_label_restriction ρ hP (hQ n)
  have hlimI' : Tendsto (fun n => conditionalSigmaEntropy ρ P (transverseLabelSigma (Q n)))
      atTop (𝓝 (∫ z, G z ∂ρ)) := by
    simpa only [hEq] using hlimI
  exact tendsto_nhds_unique hlimE hlimI'

end DukePrimeDegree

end

end OAI
