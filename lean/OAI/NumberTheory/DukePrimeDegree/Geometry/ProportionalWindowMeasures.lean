import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedIntersections

namespace OAI

/-! # A common unit anchor fixes proportional measures on exhausting windows -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem restrict_eq_of_proportional_unit_anchor
    {A : Type*} [MeasurableSpace A] (ν η : Measure A)
    (U W V : Set A) (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUV : U ⊆ V) (hWV : W ⊆ V) (hνU : ν U = 1) (hηU : η U = 1)
    (a : ℝ≥0∞) (h : ν.restrict V = a • η.restrict V) :
    ν.restrict W = η.restrict W := by
  have H := congrArg (fun ρ : Measure A => ρ U) h
  rw [Measure.restrict_apply hU,inter_eq_left.mpr hUV,hνU,Measure.smul_apply,
    smul_eq_mul,Measure.restrict_apply hU,inter_eq_left.mpr hUV,hηU,mul_one] at H
  rw [←H,one_smul] at h
  have H' := congrArg (fun ρ : Measure A => ρ.restrict W) h
  simpa only [Measure.restrict_restrict hW,inter_eq_left.mpr hWV] using H'

theorem eq_of_exhausting_proportional_windows
    {A : Type*} [MeasurableSpace A] (ν η : Measure A)
    (U : Set A) (hU : MeasurableSet U) (hνU : ν U = 1) (hηU : η U = 1)
    (W : ℕ → Set A) (hW : ∀ m, MeasurableSet (W m)) (hmono : Monotone W)
    (hcover : ⋃ m, W m = univ)
    (h : ∀ m, ∃ (V : Set A) (a : ℝ≥0∞), U ⊆ V ∧ W m ⊆ V ∧ ν.restrict V = a • η.restrict V) :
    ν = η := by
  apply measure_eq_of_restrictionChain W hmono hcover
  intro m
  obtain ⟨V,a,hUV,hWV,he⟩ := h m
  exact restrict_eq_of_proportional_unit_anchor ν η U (W m) V hU (hW m)
    hUV hWV hνU hηU a he

theorem map_restrict_proportional_of_normalized
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (E : A ≃ᵐ B) (ν κ : Measure A) (η : Measure B) (D : Set A) (hD : MeasurableSet D)
    (a b : ℝ≥0∞) (hν : ν.restrict D = b • κ.restrict D)
    (hκ : κ.map E = (anchorNormalize η (E '' D)).restrict (E '' D)) :
    (a • ν.map E).restrict (E '' D) =
      (a*b*(η (E '' D))⁻¹) • η.restrict (E '' D) := by
  have hED : MeasurableSet (E '' D) := E.measurableEmbedding.measurableSet_image.mpr hD
  have hr (ρ : Measure A) : (ρ.map E).restrict (E '' D) = (ρ.restrict D).map E := by
    rw [E.restrict_map,E.injective.preimage_image]
  rw [Measure.restrict_smul,hr ν,hν,Measure.map_smul _ E.measurable.aemeasurable,
    ←hr κ,hκ]
  simp only [anchorNormalize,Measure.restrict_smul,Measure.restrict_restrict hED,
    inter_self,smul_smul,mul_assoc]

end DukePrimeDegree

end

end OAI
