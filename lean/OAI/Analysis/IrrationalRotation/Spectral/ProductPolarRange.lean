import OAI.Analysis.IrrationalRotation.Product.ProductWeightBridge
import OAI.Analysis.IrrationalRotation.Spectral.PolarStructure

namespace OAI

open MeasureTheory Set

namespace Invariant233.ProductModel

theorem measurePreserving_rotationIterate_via_cocycle (θ : ℕ → ℝ) (k : ℤ) :
    MeasurePreserving (rotationIterate θ k) baseMeasure baseMeasure := by
  exact ProductCocycle.measurePreserving_rotate θ k

theorem ae_weight_mem_countable (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    ∃ S : Set ℝ, S.Countable ∧ S ⊆ Ioc (0 : ℝ) 1 ∧
      ∀ᵐ x ∂baseMeasure, weight θ c x ∈ S := by
  obtain ⟨S, hS, hrange⟩ :=
    InvariantProjection.PolarStructure.ae_countable_range_of_finite_drops c
      (weight θ c) (ae_exists_finset_weight θ c hθ01 hc hθ)
  refine ⟨S ∩ Ioc (0 : ℝ) 1, hS.mono inter_subset_left,
    inter_subset_right, ?_⟩
  filter_upwards [hrange, ae_weight_pos θ c (fun i ↦ (hθ01 i).1) hc hθ]
    with x hx hpos
  exact ⟨hx, hpos, (weight_mem_Icc θ c x).2⟩

theorem ae_weight_orbit_mem_countable (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    ∃ S : Set ℝ, S.Countable ∧ S ⊆ Ioc (0 : ℝ) 1 ∧
      ∀ᵐ x ∂baseMeasure, ∀ k : ℤ, weight θ c (rotationIterate θ k x) ∈ S := by
  obtain ⟨S, hS, hsub, hrange⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  refine ⟨S, hS, hsub, ae_all_iff.mpr ?_⟩
  intro k
  exact (measurePreserving_rotationIterate_via_cocycle θ k).quasiMeasurePreserving.ae hrange

theorem weight_distribution_eq_sum_dirac (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    ∃ S : Set ℝ, S.Countable ∧ S ⊆ Ioc (0 : ℝ) 1 ∧
      baseMeasure.map (weight θ c) = Measure.sum (fun y : S ↦
        baseMeasure ((weight θ c) ⁻¹' {(y : ℝ)}) • Measure.dirac (y : ℝ)) := by
  obtain ⟨S, hS, hsub, hrange⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  exact ⟨S, hS, hsub,
    InvariantProjection.PolarStructure.map_eq_sum_dirac_of_ae_countable_range
      (measurable_weight θ c).aemeasurable hS hrange⟩

theorem ae_countable_rotation_joint_range {I : Type*} [Finite I]
    (θ c : ℕ → ℝ) (k : I → ℤ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    ∃ R : Set (I → ℝ), R.Countable ∧
      ∀ᵐ x ∂baseMeasure, (fun i ↦ weight θ c (rotationIterate θ (k i) x)) ∈ R := by
  obtain ⟨S, hS, -, hrange⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  exact InvariantProjection.PolarStructure.ae_countable_joint_range_of_measurePreserving
    (fun i ↦ rotationIterate θ (k i))
    (fun i ↦ measurePreserving_rotationIterate_via_cocycle θ (k i)) (weight θ c)
    ⟨S, hS, hrange⟩

theorem finite_polar_orbit_atomic_fiber_partition (θ c : ℕ → ℝ) (F : Finset ℤ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    ∃ C : Set (F → ℝ), C.Countable ∧
      (∀ᵐ x ∂baseMeasure,
        (fun n : F ↦ weight θ c (rotationIterate θ (-(n : ℤ)) x)) ∈ C) ∧
      (∀ v ∈ C,
        MeasurableSet {x | (fun n : F ↦
          weight θ c (rotationIterate θ (-(n : ℤ)) x)) = v} ∧
        baseMeasure {x | (fun n : F ↦
          weight θ c (rotationIterate θ (-(n : ℤ)) x)) = v} ≠ 0 ∧
        ∀ t : Set Base,
          MeasurableSet[⨆ n : F, MeasurableSpace.comap
            (fun x ↦ weight θ c (rotationIterate θ (-(n : ℤ)) x)) inferInstance] t →
          t ⊆ {x | (fun n : F ↦
            weight θ c (rotationIterate θ (-(n : ℤ)) x)) = v} →
          t = ∅ ∨ t = {x | (fun n : F ↦
            weight θ c (rotationIterate θ (-(n : ℤ)) x)) = v}) := by
  apply InvariantProjection.PolarStructure.finite_family_atomic_fiber_partition
  · intro n
    exact (measurable_weight θ c).comp
      (measurePreserving_rotationIterate_via_cocycle θ (-(n : ℤ))).measurable
  · intro n
    obtain ⟨S, hS, -, hrange⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
    exact ⟨S, hS,
      (measurePreserving_rotationIterate_via_cocycle θ (-(n : ℤ))).quasiMeasurePreserving.ae hrange⟩

end Invariant233.ProductModel

end OAI
