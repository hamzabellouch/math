import OAI.MeasureTheory.Falconer.Slicing.RectangularGramSchmidt
import OAI.MeasureTheory.Falconer.Geometry.PiCoordinateSections

namespace OAI

/-! # Affine-null laws give independent sampled differences -/
namespace Falconer
open Set Submodule MeasureTheory InnerProductSpace
open scoped ENNReal
variable {d n : ℕ}

theorem prefix_span_finrank_le (v : Fin (n+1) → Space d) (i : Fin (n+1)) :
    Module.finrank ℝ (span ℝ (v '' Iio i)) ≤ n := by
  classical
  have he : v '' Iio i = ((Finset.Iio i).image v : Set (Space d)) := by
    ext x
    simp
  rw [he]
  apply (finrank_span_finset_le_card (R := ℝ) _).trans
  apply Finset.card_image_le.trans
  simpa using Nat.le_of_lt_succ i.isLt

theorem affine_null_residual_mass (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) (p : Space d) (i : Fin (n+1)) :
    (Measure.pi (fun _ : Fin (n+1) => μ))
      {w | gramSchmidt ℝ (fun j => w j-p) i = 0} = 0 := by
  have hm : Measurable (fun w : Fin (n+1) → Space d => fun j => w j-p) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply j).sub measurable_const
  have hE : MeasurableSet {w : Fin (n+1) → Space d |
      gramSchmidt ℝ (fun j => w j-p) i = 0} :=
    measurableSet_eq_fun ((rectangular_gramSchmidt_measurable i).comp hm) measurable_const
  have hbound := pi_measure_le_of_coordinate_sections μ i _ hE (0:ℝ≥0∞)
  have hsections : ∀ y : Fin n → Space d,
      μ {x | gramSchmidt ℝ (fun j => (i.insertNth x y : Fin (n+1) → Space d) j-p) i = 0} ≤ 0 := by
    intro y
    let v : Fin (n+1) → Space d := fun j => (i.insertNth 0 y : Fin (n+1) → Space d) j-p
    let V := span ℝ (v '' Iio i)
    have hz := hnull p V (prefix_span_finrank_le v i)
    apply (measure_mono (t := {x | x-p ∈ V}) ?_).trans hz.le
    intro x hx
    let w : Fin (n+1) → Space d := fun j => (i.insertNth x y : Fin (n+1) → Space d) j-p
    have hmem := rectangular_zero_residual_mem_prefix w i hx
    have hsub : w '' Iio i ⊆ v '' Iio i := by
      rintro _ ⟨j,hj,rfl⟩
      refine ⟨j,hj,?_⟩
      dsimp [v,w]
      rw [Fin.insertNth_apply_below hj,Fin.insertNth_apply_below hj]
    have hh := (span_mono hsub) hmem
    simpa only [mem_ofPred_eq,V,w,Fin.insertNth_apply_same] using hh
  have hle : (Measure.pi (fun _ : Fin (n+1) => μ))
      {w | gramSchmidt ℝ (fun j => w j-p) i = 0} ≤ 0 := by
    simpa only [zero_mul] using hbound hsections
  exact le_antisymm hle bot_le

theorem affine_null_differences_independent_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) (p : Space d) :
    ∀ᵐ w : Fin (n+1) → Space d ∂Measure.pi (fun _ => μ),
      LinearIndependent ℝ (fun j => w j-p) := by
  have hzero : (Measure.pi (fun _ : Fin (n+1) => μ))
      (⋃ i : Fin (n+1), {w | gramSchmidt ℝ (fun j => w j-p) i = 0}) = 0 :=
    measure_iUnion_null (affine_null_residual_mass μ hnull p)
  have hgood : ∀ᵐ w : Fin (n+1) → Space d ∂Measure.pi (fun _ => μ),
      w ∉ ⋃ i : Fin (n+1), {w | gramSchmidt ℝ (fun j => w j-p) i = 0} := by
    rw [ae_iff]
    simpa only [not_not,ofPred_mem_eq] using hzero
  filter_upwards [hgood] with w hw
  apply rectangular_independent_of_residuals
  intro i hi
  exact hw (mem_iUnion.mpr ⟨i,hi⟩)

end Falconer

end OAI
