import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientIdentity

namespace OAI

/-! Positive smoothing on an open plane domain with a prescribed sum of
local gradient errors. All approximants and partition weights are constructed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_positive_partition_smoothing
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ (∀x ∈ Ω, v x ∈ Icc 0 1) ∧
      (∀x ∈ Ω, ∀a b : ℝ,
        (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, u y ∈ Icc a b) → v x ∈ Icc a b) ∧
      ∀i : Fin 2, eLpNorm (fun x =>
        (fderiv ℝ v x) (EuclideanSpace.single i 1) -
          ∑ᶠ j, ρ.weight j x * (hu j).weakGrad x i) 2 (volume.restrict Ω) ≤ ∑' j, ε j := by
  obtain ⟨v, hv, he⟩ := exists_partition_approximation_with_summed_error
    ρ W hW hsub u hu hunit ε hε
  have hsmooth (j : ι) := (hv j).1.1
  refine ⟨ρ.mix v, ρ.mix_contDiffOn v hsmooth, ?_, ?_, ?_⟩
  · intro x hx
    exact ρ.mix_mem_Icc v hx (fun j _ => (hv j).1.2.2 x)
  · intro x hx a b hab
    exact ρ.mix_mem_Icc v hx (fun j hj =>
      (hv j).2 a b (hab j hj) x (subset_tsupport (ρ.weight j) hj))
  · intro i
    calc
      _ = eLpNorm (fun x => ∑ᶠ j,
          partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x)
          2 (volume.restrict Ω) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
        exact ρ.mix_gradient_error_identity u _ v hsmooth hx i
      _ ≤ eLpNorm (fun x => ∑ᶠ j,
          partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ _ := he i

end CircleDomainRigidity

end

end OAI
