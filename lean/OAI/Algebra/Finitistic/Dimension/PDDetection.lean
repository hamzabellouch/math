import OAI.Algebra.Finitistic.Dimension.PDTor
import OAI.Algebra.Finitistic.Dimension.PDResidueTensor
import OAI.Algebra.Finitistic.Dimension.PDDimension

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Nakayama detects zero modules using the actual radical-quotient tensor. -/
theorem residueTensor_subsingleton_iff
    (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [Module.Finite A N] :
    Subsingleton (BalancedTensor.Tensor k A (Residue (A := A)) N) ↔ Subsingleton N := by
  constructor
  · intro h
    by_contra hn
    have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hn
    have := residueTensor_nontrivial (k := k) (A := A) N
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (BalancedTensor.Tensor k A (Residue (A := A)) N)
    exact hxy (h.elim x y)
  · intro h
    have := h
    infer_instance

variable [FiniteDimensional k A] (M : PDMinimal.FiniteModule k A)

/-- For the semisimple quotient S, the n-th Tor is zero exactly when the n-th
term of the constructed minimal projective resolution is zero. -/
theorem residueTor_zero_iff_term (n : ℕ) :
    IsZero (Tor (k := k) (Residue (A := A)) M.cat n) ↔
      Subsingleton (PDMinimal.term M n) := by
  let e := torIsoTerm (Residue (A := A)) M residue_annihilated n
  rw [e.isZero_iff]
  change IsZero (ModuleCat.of k (BalancedTensor.Tensor k A (Residue (A := A))
    (ScalarModule k A (PDMinimal.term M n).cat))) ↔ _
  rw [ModuleCat.isZero_iff_subsingleton]
  have : Module.Finite A (ScalarModule k A (PDMinimal.term M n).cat) :=
    show Module.Finite A (PDMinimal.term M n) from inferInstance
  exact residueTensor_subsingleton_iff (k := k) (ScalarModule k A (PDMinimal.term M n).cat)

/-- Projective dimension of a finite-dimensional module over an actual
finite-dimensional algebra is detected by its derived tensor with A/rad A.
No detection theorem is assumed: the proof constructs minimal resolutions. -/
theorem pdLE_iff_residueTor_zero (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      IsZero (Tor (k := k) (Residue (A := A)) M.cat (n+1)) := by
  rw [PDMinimal.pdLE_iff_term_zero, residueTor_zero_iff_term]

/-- The finite-projective-dimension implication used in cor:pd-detection. -/
theorem finite_pd_of_bounded_residueTor
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n)) :
    ∃ b : ℕ, HasProjectiveDimensionLE M.cat b := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, (pdLE_iff_residueTor_zero M b).mpr (hb (b+1) (by omega))⟩

/-- The conclusion uses mathlib's actual numerical projective dimension. -/
theorem projectiveDimension_le_of_residueTor_zero (n : ℕ)
    (h : IsZero (Tor (k := k) (Residue (A := A)) M.cat (n+1))) :
    projectiveDimension M.cat ≤ n :=
  (projectiveDimension_le_iff _ _).mpr ((pdLE_iff_residueTor_zero M n).mpr h)
end LittleFinitistic.PDTensor

end

end OAI
