import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinsuppCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

namespace OAI

/-! # The regular module detects finite cohomological dimension

For a finite resolution, vanishing with regular coefficients implies the
same vanishing with free coefficients. Free covers and dimension shifting
then give vanishing with every coefficient module.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

def regularFreeCover (A : Rep.{0} ℤ G) : Rep.free ℤ G A ⟶ A :=
  Rep.freeLift ℤ G A id

instance regularFreeCover_epi (A : Rep.{0} ℤ G) : Epi (regularFreeCover A) := by
  rw [Rep.epi_iff_surjective]
  intro a
  refine ⟨Finsupp.single a (MonoidAlgebra.single 1 1), ?_⟩
  change Representation.freeLift A.ρ id
    (Finsupp.single a (MonoidAlgebra.single 1 1)) = a
  rw [Representation.freeLift_single_single]
  simp only [id_eq, map_one, Module.End.one_apply]
  exact @one_smul ℤ A _ A.hV2.toMulAction a

theorem cohomology_vanishes_above_regular_bound
    (hG : HasFiniteProjectiveResolution G) (n : ℕ)
    (hreg : ∀ i, n < i → IsZero (groupCohomology (Rep.leftRegular ℤ G) i)) :
    ∀ i, n < i → ∀ A : Rep ℤ G, IsZero (groupCohomology A i) := by
  obtain ⟨P, d, hfin, hbound⟩ := hG
  let := projectiveDimension_of_boundedResolution P d hbound
  have hfree (i : ℕ) (hi : n < i) (A : Rep ℤ G) :
      IsZero (groupCohomology (Rep.free ℤ G A) i) := by
    exact IsZero.of_iso ((moduleFinsuppFunctor ℤ A).map_isZero (hreg i hi))
      (finsuppCohomologyIso ℤ G A P hfin (Rep.leftRegular ℤ G) i)
  have hshift : ∀ k i, n < i → d < i + k →
      ∀ A : Rep ℤ G, IsZero (groupCohomology A i) := by
    intro k
    induction k with
    | zero =>
      intro i _ hi A
      exact groupCohomology_isZero_above_dimension d A i (by omega)
    | succ k ih =>
      intro i hi hdi A
      let f := regularFreeCover A
      let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
      have hz : IsZero (groupCohomology S.X₁ (i + 1)) := ih (i + 1) (by omega) (by omega) _
      let := groupCohomology.mono_δ_of_isZero hS i (hfree i hi A)
      exact IsZero.of_mono (groupCohomology.δ hS i (i + 1) rfl) hz
  intro i hi A
  exact hshift (d + 1) i hi (by omega) A

theorem projectiveDimension_of_regular_cohomology_bound
    (hG : HasFiniteProjectiveResolution G) (n : ℕ)
    (hreg : ∀ i, n < i → IsZero (groupCohomology (Rep.leftRegular ℤ G) i)) :
    HasProjectiveDimensionLE (trivialIntegral G) n := by
  have hAll := cohomology_vanishes_above_regular_bound hG n hreg
  obtain ⟨P, _, _, _⟩ := hG
  let := HasExt.standard (Rep ℤ G)
  refine HasProjectiveDimensionLT.mk ?_
  intro i hi A e
  cases i with
  | zero => omega
  | succ j =>
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (j + 2) rfl
    have hz := hAll (j + 1) (by omega) A
    let C := P.complex.linearYonedaObj ℤ A
    have hC : C.ExactAt (j + 1) :=
      (C.exactAt_iff_isZero_homology (j + 1)).mpr
        (IsZero.of_iso hz (groupCohomologyIso A (j + 1) P).symm)
    have hS : (C.sc' j (j + 1) (j + 2)).Exact :=
      (C.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp)).mp hC
    have hf' : (C.sc' j (j + 1) (j + 2)).g f = 0 := hf
    obtain ⟨g, hg⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS f hf'
    exact (P.extMk_eq_zero_iff f (j + 2) rfl hf j rfl).mpr ⟨g, hg⟩

theorem IsIntegralPoincareDualityGroup.cohomologicalDimension {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    HasProjectiveDimensionLE (trivialIntegral G) n :=
  projectiveDimension_of_regular_cohomology_bound hG.1 n
    (fun i hi => hG.2.1 i (by omega))

theorem IsIntegralPoincareDualityGroup.dimension_unique {m n : ℕ}
    (hm : IsIntegralPoincareDualityGroup G m) (hn : IsIntegralPoincareDualityGroup G n) :
    m = n := by
  apply Nat.le_antisymm
  · let := hn.cohomologicalDimension
    exact hm.dimension_le
  · let := hm.cohomologicalDimension
    exact hn.dimension_le

theorem IsIntegralPoincareDualityGroup.subgroup_dimension_le {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (H : Subgroup G) {m : ℕ}
    (hH : IsIntegralPoincareDualityGroup H m) : m ≤ n := by
  let := hG.cohomologicalDimension
  let := subgroup_cohomologicalDimension_le H n
  exact hH.dimension_le

end PolycyclicRecognition

end

end OAI
