import OAI.GroupTheory.PolycyclicRecognition.Algebra.SpectralUnitGroup

namespace OAI

/-! # Scalar values of a compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [AddCommGroup V] [Module ℂ V]

def spectralLogValue (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ≠ 0 then
    if hm : Units.mk0 z hz ∈ spectralUnitGroup S then (L ⟨Units.mk0 z hz, hm⟩).toAdd else 0
  else 0

theorem spectralLogValue_unit (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ) (z : spectralUnitGroup S) :
    spectralLogValue S L (z.val : ℂ) = (L z).toAdd := by
  simp [spectralLogValue, Units.ne_zero z.val, z.property]

theorem spectralLogValue_mul (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ) (z w : spectralUnitGroup S) :
    spectralLogValue S L ((z.val : ℂ) * (w.val : ℂ)) =
      spectralLogValue S L (z.val : ℂ) + spectralLogValue S L (w.val : ℂ) := by
  have h := spectralLogValue_unit S L (z * w)
  simpa only [Subgroup.coe_mul, Units.val_mul, spectralLogValue_unit,
    map_mul, toAdd_mul] using h

theorem spectralLogValue_conjugation (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ)
    (hc : ∀ z, (L (spectralUnitConjugation S z)).toAdd = star (L z).toAdd)
    (z : spectralUnitGroup S) :
    spectralLogValue S L (star (z.val : ℂ)) = star (spectralLogValue S L (z.val : ℂ)) := by
  rw [spectralLogValue_unit]
  exact (spectralLogValue_unit S L (spectralUnitConjugation S z)).trans (hc z)

theorem spectralLogValue_conjugation_all (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ)
    (hc : ∀ z, (L (spectralUnitConjugation S z)).toAdd = star (L z).toAdd)
    (z : ℂ) : spectralLogValue S L (star z) = star (spectralLogValue S L z) := by
  classical
  by_cases hz : z = 0
  · simp [hz, spectralLogValue]
  have hcz : star z ≠ 0 := by simpa using hz
  let u : ℂˣ := Units.mk0 z hz
  by_cases hu : u ∈ spectralUnitGroup S
  · exact spectralLogValue_conjugation S L hc ⟨u, hu⟩
  · have hv : Units.mk0 (star z) hcz ∉ spectralUnitGroup S := by
      intro hv
      apply hu
      have h := spectralUnitGroup_star S hv
      convert h using 1
      apply Units.ext
      exact (star_star z).symm
    simp only [spectralLogValue, dite_eq_left hz, dite_eq_left hcz, dite_eq_right hv]
    have hu' : Units.mk0 z hz ∉ spectralUnitGroup S := hu
    rw [dite_eq_right hu', star_zero]

theorem eigenvalue_ne_zero_of_isUnit (S : Module.End ℂ V) (hS : IsUnit S)
    {μ : ℂ} (hμ : S.HasEigenvalue μ) : μ ≠ 0 := by
  intro hz
  exact spectrum.zero_notMem ℂ hS (hz ▸ hμ.mem_spectrum)

def spectralEigenvalue (S : Module.End ℂ V) (hS : IsUnit S)
    (μ : ℂ) (hμ : S.HasEigenvalue μ) : spectralUnitGroup S :=
  ⟨Units.mk0 μ (eigenvalue_ne_zero_of_isUnit S hS hμ),
    Subgroup.subset_closure (Or.inl hμ)⟩

end PolycyclicRecognition

end

end OAI
