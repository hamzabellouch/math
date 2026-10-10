import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.PiNat

namespace OAI

/-! # Measurable hulls of finite-prefix images

For a continuous Baire-space parametrization, measurable hulls permit
successive prefix choices outside one null set. This is the measure-specific
selection construction needed for the published unitary selector.
-/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

def bairePrefixCylinder (s : List ℕ) : Set (ℕ → ℕ) :=
  {a | PiNat.res a s.length = s}

@[simp] theorem bairePrefixCylinder_nil : bairePrefixCylinder [] = Set.univ := by
  ext a
  simp [bairePrefixCylinder]

theorem bairePrefixCylinder_children (s : List ℕ) :
    (⋃ n : ℕ, bairePrefixCylinder (n :: s)) = bairePrefixCylinder s := by
  ext a
  simp only [Set.mem_iUnion, bairePrefixCylinder, Set.mem_ofPred_eq, List.length_cons,
    PiNat.res_succ, List.cons.injEq]
  constructor
  · rintro ⟨n, _, h⟩
    exact h
  · intro h
    exact ⟨a s.length, rfl, h⟩

theorem bairePrefixCylinder_eq (s : List ℕ) {a : ℕ → ℕ} (ha : a ∈ bairePrefixCylinder s) :
    bairePrefixCylinder s = PiNat.cylinder a s.length := by
  rw [PiNat.cylinder_eq_res]
  change PiNat.res a s.length = s at ha
  simp only [bairePrefixCylinder, ha]

variable {X : Type*} [MeasurableSpace X]

/-- A measurable envelope is minimal modulo null sets among measurable supersets. -/
theorem measurableHull_subset_ae (μ : Measure X) [IsFiniteMeasure μ]
    {A B : Set X} (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ∀ᵐ x ∂μ, x ∈ toMeasurable μ A → x ∈ B := by
  have hi : toMeasurable μ A ∩ B =ᵐ[μ] toMeasurable μ A := by
    apply ae_eq_of_subset_of_measure_ge inter_subset_left
    · rw [μ.measure_toMeasurable_inter hB (measure_ne_top μ A), inter_eq_left.mpr hAB,
        measure_toMeasurable]
    · exact ((measurableSet_toMeasurable μ A).inter hB).nullMeasurableSet
    · exact measure_ne_top μ _
  filter_upwards [hi] with x hx hxA
  exact (hx.mpr hxA).2

variable [TopologicalSpace X] [BorelSpace X]

def baireImageHull (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) : Set X :=
  toMeasurable μ (F '' bairePrefixCylinder s) ∩ closure (F '' bairePrefixCylinder s)

theorem measurableSet_baireImageHull (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) :
    MeasurableSet (baireImageHull μ F s) :=
  (measurableSet_toMeasurable _ _).inter isClosed_closure.measurableSet

omit [BorelSpace X] in
theorem image_subset_baireImageHull (μ : Measure X) (F : (ℕ → ℕ) → X) (s : List ℕ) :
    F '' bairePrefixCylinder s ⊆ baireImageHull μ F s :=
  subset_inter (subset_toMeasurable _ _) subset_closure

theorem baireImageHull_children_ae (μ : Measure X) [IsFiniteMeasure μ]
    (F : (ℕ → ℕ) → X) (s : List ℕ) :
    ∀ᵐ x ∂μ, x ∈ baireImageHull μ F s → ∃ n, x ∈ baireImageHull μ F (n :: s) := by
  have hsub : F '' bairePrefixCylinder s ⊆ ⋃ n, baireImageHull μ F (n :: s) := by
    rw [← bairePrefixCylinder_children s, Set.image_iUnion]
    exact Set.iUnion_mono (fun n => image_subset_baireImageHull μ F (n :: s))
  have h := measurableHull_subset_ae μ
    (MeasurableSet.iUnion (fun n => measurableSet_baireImageHull μ F (n :: s))) hsub
  filter_upwards [h] with x hx hxs
  exact Set.mem_iUnion.mp (hx hxs.1)

theorem baireImageHull_all_children_ae (μ : Measure X) [IsFiniteMeasure μ]
    (F : (ℕ → ℕ) → X) :
    ∀ᵐ x ∂μ, ∀ s : List ℕ, x ∈ baireImageHull μ F s →
      ∃ n, x ∈ baireImageHull μ F (n :: s) :=
  ae_all_iff.mpr (baireImageHull_children_ae μ F)

end

end KadisonKastler

end OAI
