import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightContinuity

namespace OAI

/-! Exact integration of the finite low/large-core split. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrable_weighted_height_mass {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Integrable (fun t => f t*fullStructuredHeightMass R H v e ℓ u W X t) := by
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H v e ℓ u W X
  exact hf.mul_bdd (continuous_fullStructuredHeightMass R H v e ℓ u W X).aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H v e ℓ u W X t)]
      exact hB t))

lemma weighted_height_mass_partition {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) (H : Finset Eisenstein) (P : Eisenstein → Prop)
    (v e : Eisenstein) (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∫ t : ℝ, f t*fullStructuredHeightMass R H v e ℓ u W X t) =
      (∫ t : ℝ, f t*fullStructuredHeightMass R (H.filter P) v e ℓ u W X t)+
      (∫ t : ℝ, f t*fullStructuredHeightMass R (H.filter (fun h => ¬P h)) v e ℓ u W X t) := by
  have he (t : ℝ) : fullStructuredHeightMass R H v e ℓ u W X t =
      fullStructuredHeightMass R (H.filter P) v e ℓ u W X t+
      fullStructuredHeightMass R (H.filter (fun h => ¬P h)) v e ℓ u W X t := by
    exact (Finset.sum_filter_add_sum_filter_not H P _).symm
  simp_rw [he,mul_add]
  exact integral_add (integrable_weighted_height_mass hf R (H.filter P) v e ℓ u W X)
    (integrable_weighted_height_mass hf R (H.filter (fun h => ¬P h)) v e ℓ u W X)

end CubicFirstMoment

end

end OAI
