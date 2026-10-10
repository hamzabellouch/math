import OAI.Analysis.KadisonKastler.ProductIntegralUniqueness
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace OAI

/-! # Density of finite-coordinate Hilbert functions

The random-walk proof needs approximants depending on a finite block. The
orthogonal complement is zero because its integrals over all cylinder sets
vanish, and cylinders generate the product sigma algebra.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {G K : Type*} [MeasurableSpace G]
  {μ : Measure (ℤ → G)} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def finiteCoordinateL2 (μ : Measure (ℤ → G)) : Submodule ℂ (Lp K 2 μ) where
  carrier := {f | ∃ I : Finset ℤ, AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)] f μ}
  zero_mem' := ⟨∅, aestronglyMeasurable_zero.congr (Lp.coeFn_zero K 2 μ).symm⟩
  add_mem' := by
    rintro f g ⟨I, hI⟩ ⟨J, hJ⟩
    refine ⟨I ∪ J, ?_⟩
    have hi := hI.mono (cylinderEvents_mono
      (show (I : Set ℤ) ⊆ ((I ∪ J : Finset ℤ) : Set ℤ) from fun _ h => Finset.mem_union_left J h))
    have hj := hJ.mono (cylinderEvents_mono
      (show (J : Set ℤ) ⊆ ((I ∪ J : Finset ℤ) : Set ℤ) from fun _ h => Finset.mem_union_right I h))
    exact (hi.add hj).congr (Lp.coeFn_add f g).symm
  smul_mem' := by
    rintro c f ⟨I, hI⟩
    exact ⟨I, (hI.const_smul c).congr (Lp.coeFn_smul c f).symm⟩

omit [CompleteSpace K] in
theorem finiteCoordinateL2_indicator (I : Finset ℤ) (A : Set (∀ _ : I, G))
    (hA : MeasurableSet A) (v : K) :
    indicatorConstLp 2 hA.cylinder (measure_ne_top μ _) v ∈ finiteCoordinateL2 μ := by
  refine ⟨I, ?_⟩
  have hm : @Measurable (ℤ → G) (∀ i : I, G)
      (cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)) _ (fun x i => x i) :=
    @Measurable.of_eval (ℤ → G) I (fun _ => G)
      (cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)) (fun _ => inferInstance)
      (fun x i => x i) (fun i => measurable_cylinderEvent_apply i.property)
  have hset : MeasurableSet[cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)] (cylinder I A) :=
    hm hA
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (mem_lpMeas_indicatorConstLp (𝕜 := ℂ) cylinderEvents_le_pi hset (measure_ne_top μ _))

theorem finiteCoordinateL2_orthogonal_eq_bot : (finiteCoordinateL2 (K := K) μ)ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  have hi : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  have hc (A : Set (ℤ → G)) (hA : A ∈ measurableCylinders (fun _ : ℤ => G)) :
      ∫ x in A, f x ∂μ = 0 := by
    obtain ⟨I, B, hB, rfl⟩ := (mem_measurableCylinders A).mp hA
    have hz (v : K) : inner ℂ v (∫ x in cylinder I B, f x ∂μ) = 0 := by
      rw [← L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hB.cylinder (measure_ne_top μ _) v f]
      exact hf _ (finiteCoordinateL2_indicator I B hB v)
    exact inner_self_eq_zero.mp (hz _)
  have hv : μ.withDensityᵥ (f : (ℤ → G) → K) = 0 := by
    apply VectorMeasure.ext_of_generateFrom (measurableCylinders (fun _ : ℤ => G))
    · intro A hA
      rw [withDensityᵥ_apply hi (MeasurableSet.of_mem_measurableCylinders hA), hc A hA]
      rfl
    · exact generateFrom_measurableCylinders.symm
    · exact isPiSystem_measurableCylinders
    · rw [withDensityᵥ_apply hi MeasurableSet.univ]
      apply hc
      exact (mem_measurableCylinders univ).mpr ⟨∅, univ, MeasurableSet.univ, (cylinder_univ ∅).symm⟩
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply hi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  simpa using hv

theorem finiteCoordinateL2_dense : Dense ((finiteCoordinateL2 (K := K) μ) : Set (Lp K 2 μ)) := by
  have h : (finiteCoordinateL2 (K := K) μ).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, finiteCoordinateL2_orthogonal_eq_bot]
    exact Submodule.bot_orthogonal_eq_top
  change ∀ f, f ∈ closure ((finiteCoordinateL2 (K := K) μ) : Set (Lp K 2 μ))
  intro f
  change f ∈ (finiteCoordinateL2 (K := K) μ).topologicalClosure
  rw [h]
  trivial

theorem exists_finiteCoordinate_L2_approximation (f : Lp K 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Finset ℤ) (g : Lp K 2 μ),
      AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)] g μ ∧ dist f g < ε := by
  obtain ⟨g, ⟨I, hI⟩, hg⟩ := Metric.mem_closure_iff.mp (finiteCoordinateL2_dense (μ := μ) f) ε hε
  exact ⟨I, g, hI, hg⟩

end

end KadisonKastler

end OAI
