import OAI.Algebra.Finitistic.Dimension.PDLowerBound

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : PDMinimal.FiniteModule k A)

theorem bounded_residueTor_of_finite_pd
    (h : ∃ b : ℕ, HasProjectiveDimensionLE M.cat b) :
    ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n) := by
  obtain ⟨b, hb⟩ := h
  have : HasProjectiveDimensionLT M.cat (b+1) := hb
  refine ⟨b, fun n hn => tor_zero_of_pdLT (Residue (A := A)) M n ?_⟩
  exact hasProjectiveDimensionLT_of_ge M.cat (b+1) n (by omega)

/-- Finite projective dimension is equivalent to bounded actual residue Tor. -/
theorem finite_pd_iff_bounded_residueTor :
    projectiveDimension M.cat ≠ ⊤ ↔
      ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n) := by
  rw [projectiveDimension_ne_top_iff]
  exact ⟨bounded_residueTor_of_finite_pd M, finite_pd_of_bounded_residueTor M⟩

/-- The upper detector accepts any actual projective resolution, including a
bar resolution once its exactness and projectivity have been proved. -/
theorem finite_pd_of_resolution
    (P : ProjectiveResolution M.cat)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      (((tensorFunctor k A (Residue (A := A))).mapHomologicalComplex _).obj P.complex |>.homology n)) :
    projectiveDimension M.cat < ⊤ := by
  apply projectiveDimension_lt_top_of_bounded_residueTor M
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun n hn => (hb n hn).of_iso
    (P.isoLeftDerivedObj (tensorFunctor k A (Residue (A := A))) n)⟩

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- The lower detector also accepts any actual projective resolution.
The nonzero class can be supplied by a summand of the bar decomposition. -/
theorem lower_bound_of_resolution (P : ProjectiveResolution M.cat) (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero (((tensorFunctor k A U).mapHomologicalComplex _).obj P.complex |>.homology n)) :
    r ≤ projectiveDimension M.cat := by
  apply lower_bound_of_nonzero_Tor U M r n hrn
  intro hz
  exact h (hz.of_iso (P.isoLeftDerivedObj (tensorFunctor k A U) n).symm)
end LittleFinitistic.PDTensor

end

end OAI
