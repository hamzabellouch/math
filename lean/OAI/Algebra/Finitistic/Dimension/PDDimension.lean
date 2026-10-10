import OAI.Algebra.Finitistic.Dimension.PDMinimalResolution
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma cover_subsingleton (M : FiniteModule k A) [Subsingleton M] :
    Subsingleton (cover M).source := by
  have hp : (cover M).π = 0 := Subsingleton.elim _ _
  have hsurj := (cover M).minimal 0 (by simp [hp])
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  exact ha.symm.trans hb

lemma cover_injective (M : FiniteModule k A) [Module.Projective A M] :
    Function.Injective (cover M).π := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (cover M).π LinearMap.id
    (cover M).surjective
  have he : (cover M).π.comp (g.comp (cover M).π) = (cover M).π := by
    rw [← LinearMap.comp_assoc, hg, LinearMap.id_comp]
  have hs := (cover M).minimal _ he
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨(cover M).π y, hy⟩
  have hgp : g.comp (cover M).π = LinearMap.id := by
    ext x
    obtain ⟨y, rfl⟩ := hgs x
    exact congrArg g (DFunLike.congr_fun hg y)
  exact LinearMap.injective_of_comp_eq_id _ _ hgp

lemma next_subsingleton_of_projective (M : FiniteModule k A) [Module.Projective A M] :
    Subsingleton (next M) := by
  have he := LinearMap.ker_eq_bot.mpr (cover_injective M)
  change Subsingleton (LinearMap.ker (cover M).π)
  rw [he]
  infer_instance

/-- Vanishing of a term of the constructed resolution gives the standard
categorical projective-dimension bound. -/
theorem pdLT_of_term_zero (M : FiniteModule k A) (n i : ℕ)
    (hz : Subsingleton (term M (i+n))) :
    HasProjectiveDimensionLT (syzygy M i).cat n := by
  induction n generalizing i with
  | zero =>
    have : Subsingleton (term M i) := by simpa using hz
    have : Subsingleton (syzygy M i) :=
      Function.Surjective.subsingleton (cover _).surjective
    exact (hasProjectiveDimensionLT_zero_iff_isZero _).mpr
      (ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton (syzygy M i) from inferInstance))
  | succ n ih =>
    have hnext : HasProjectiveDimensionLT (syzygy M (i+1)).cat n :=
      ih (i+1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz)
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    exact hs.hasProjectiveDimensionLT_X₃ n hnext inferInstance

lemma syzygy_projective (M : FiniteModule k A) (n i : ℕ)
    (h : HasProjectiveDimensionLT (syzygy M i).cat (n+1)) :
    Projective (syzygy M (i+n)).cat := by
  induction n generalizing i with
  | zero =>
    simpa using projective_iff_hasProjectiveDimensionLT_one.mpr h
  | succ n ih =>
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    have hn : HasProjectiveDimensionLT (syzygy M (i+1)).cat (n+1) :=
      (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i+1) hn

/-- Finite projective dimension forces the minimal resolution to terminate. -/
theorem term_zero_of_pdLE (M : FiniteModule k A) (n : ℕ)
    (h : HasProjectiveDimensionLE M.cat n) : Subsingleton (term M (n+1)) := by
  have hp := syzygy_projective M n 0 h
  rw [Nat.zero_add] at hp
  have : Module.Projective A (syzygy M n) :=
    (IsProjective.iff_projective _).mpr (by simpa only [Nat.zero_add, FiniteModule.cat] using hp)
  have : Subsingleton (syzygy M (n+1)) := next_subsingleton_of_projective (syzygy M n)
  exact cover_subsingleton _

/-- The actual minimal-resolution term criterion, proved from covers and
short-exact-sequence dimension shifting. -/
theorem pdLE_iff_term_zero (M : FiniteModule k A) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔ Subsingleton (term M (n+1)) :=
  ⟨term_zero_of_pdLE M n, fun h => pdLT_of_term_zero M (n+1) 0 (by simpa using h)⟩
end LittleFinitistic.PDMinimal

end

end OAI
