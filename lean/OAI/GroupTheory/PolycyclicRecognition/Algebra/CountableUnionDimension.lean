import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CountableUnionCohomology
import Mathlib.Basic.Countable.Defs

namespace OAI

/-! # Integral dimension bounds for countable increasing unions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

theorem projectiveDimension_of_cohomology_vanishing (d : ℕ)
    (h : ∀ (A : Rep ℤ G) (i : ℕ), d < i → IsZero (groupCohomology A i)) :
    HasProjectiveDimensionLE (trivialIntegral G) d := by
  let P := Rep.standardResolution ℤ G
  let := HasExt.standard (Rep ℤ G)
  refine HasProjectiveDimensionLT.mk ?_
  intro i hi A e
  cases i with
  | zero => omega
  | succ j =>
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (j + 2) rfl
    let C := P.complex.linearYonedaObj ℤ A
    have hC : C.ExactAt (j + 1) :=
      (C.exactAt_iff_isZero_homology (j + 1)).mpr
        (IsZero.of_iso (h A (j + 1) (by omega)) (groupCohomologyIso A (j + 1) P).symm)
    have hS : (C.sc' j (j + 1) (j + 2)).Exact :=
      (C.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp)).mp hC
    have hf' : (C.sc' j (j + 1) (j + 2)).g f = 0 := hf
    obtain ⟨g, hg⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS f hf'
    exact (P.extMk_eq_zero_iff f (j + 2) rfl hf j rfl).mpr ⟨g, hg⟩

/-- Countable unions cost at most one additional integral dimension. -/
theorem cohomologicalDimension_le_of_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (d : ℕ)
    (hd : ∀ n, HasProjectiveDimensionLE (trivialIntegral (S n)) d) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  apply projectiveDimension_of_cohomology_vanishing
  intro A i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  apply groupCohomology_isZero_of_exhaustion S hS hcover A k
  · intro n
    let := hd n
    exact groupCohomology_isZero_above_dimension d _ _ (by omega)
  · intro n
    let := hd n
    exact groupCohomology_isZero_above_dimension d _ _ (by omega)

theorem exists_fg_subgroup_exhaustion [Countable G] :
    ∃ S : ℕ → Subgroup G, Monotone S ∧ (∀ n, (S n).FG) ∧
      ∀ g, ∃ n, g ∈ S n := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let T (n : ℕ) : Set G := Set.range (fun i : Fin n => e i)
  let S (n : ℕ) := Subgroup.closure (T n)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i j hij
    apply Subgroup.closure_mono
    rintro g ⟨k, rfl⟩
    exact ⟨⟨k, k.isLt.trans_le hij⟩, rfl⟩
  · intro n
    exact (Subgroup.fg_iff _).mpr ⟨T n, rfl, Set.finite_range _⟩
  · intro g
    obtain ⟨n, rfl⟩ := he g
    exact ⟨n + 1, Subgroup.subset_closure ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩⟩

theorem cohomologicalDimension_le_of_fg_subgroups [Countable G] (d : ℕ)
    (h : ∀ H : Subgroup G, H.FG → HasProjectiveDimensionLE (trivialIntegral H) d) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  obtain ⟨S, hS, hfg, hcover⟩ := exists_fg_subgroup_exhaustion (G := G)
  exact cohomologicalDimension_le_of_exhaustion S hS hcover d (fun n => h (S n) (hfg n))

end PolycyclicRecognition

end

end OAI
