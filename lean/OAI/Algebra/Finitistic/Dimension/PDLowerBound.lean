import OAI.Algebra.Finitistic.Dimension.PDDetection

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable (M : PDMinimal.FiniteModule k A)

/-- Any right module detects a lower bound through nonzero Tor; it need not
be flat, finite-dimensional, or annihilated by the radical. -/
theorem tor_zero_of_pdLT (n : ℕ) (h : HasProjectiveDimensionLT M.cat n) :
    IsZero (Tor (k := k) U M.cat n) := by
  have ht : Subsingleton (PDMinimal.term M n) := by
    cases n with
    | zero =>
      have hm := (hasProjectiveDimensionLT_zero_iff_isZero _).mp h
      have : Subsingleton M := ModuleCat.subsingleton_of_isZero hm
      exact PDMinimal.cover_subsingleton M
    | succ n => exact PDMinimal.term_zero_of_pdLE M n h
  have hz : IsZero (PDMinimal.term M n).cat := ModuleCat.isZero_iff_subsingleton.mpr ht
  have hm : IsZero ((model U M).X n) := (tensorFunctor k A U).map_isZero hz
  exact (HomologicalComplex.ExactAt.of_isZero hm).isZero_homology.of_iso (torIsoModel U M n)

theorem le_projectiveDimension_of_nonzero_Tor (n : ℕ)
    (h : ¬ IsZero (Tor (k := k) U M.cat n)) : n ≤ projectiveDimension M.cat := by
  by_contra hn
  exact h (tor_zero_of_pdLT U M n (projectiveDimension_lt_iff.mp (lt_of_not_ge hn)))

theorem lower_bound_of_nonzero_Tor (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero (Tor (k := k) U M.cat n)) : r ≤ projectiveDimension M.cat := by
  exact le_trans (by exact_mod_cast hrn) (le_projectiveDimension_of_nonzero_Tor U M n h)

/-- Bounded radical-quotient Tor gives finite numerical projective dimension. -/
theorem projectiveDimension_lt_top_of_bounded_residueTor
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n)) :
    projectiveDimension M.cat < ⊤ := by
  obtain ⟨b, hb⟩ := h
  exact lt_of_le_of_lt
    (projectiveDimension_le_of_residueTor_zero M b (hb (b+1) (by omega))) (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top b))
end LittleFinitistic.PDTensor

end

end OAI
