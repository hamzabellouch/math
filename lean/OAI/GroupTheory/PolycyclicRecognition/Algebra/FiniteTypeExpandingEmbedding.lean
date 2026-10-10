import OAI.GroupTheory.PolycyclicRecognition.Algebra.NumberFieldExpandingPlace
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TranscendentalExpandingEmbedding
import Mathlib.LinearAlgebra.Countable

namespace OAI

/-! # A valued embedding that expands a specified nontorsion element

The coefficient field may have finite transcendence degree. For an algebraic
element, choose a place of its number field and extend that embedding. For a
transcendental element, use an expanding complex specialization.
-/

noncomputable section
namespace PolycyclicRecognition
open NumberField IsDedekindDomain

theorem numberField_expanding_normed_embedding
    {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0)
    (hnt : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (f : K →+* L), 1 < ‖f z‖ := by
  obtain h | h := nontorsion_numberField_expanding_place z hz hnt
  · obtain ⟨σ, hσ⟩ := h
    exact ⟨ℂ, inferInstance, inferInstance, inferInstance, σ, hσ⟩
  · obtain ⟨v, hv⟩ := h
    let E := HeightOneSpectrum.adicCompletion K v
    let σ : K →+* E := FinitePlace.embedding v
    let : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne
      ⟨σ z, (map_ne_zero σ).mpr hz, ne_of_gt hv⟩
    let : CharZero E := (RingHom.charZero_iff σ.injective).mp inferInstance
    obtain ⟨L, hL, hC, hA, f, hf⟩ := exists_complete_algebraicallyClosed_normed_extension E
    let : NontriviallyNormedField L := hL
    let : CompleteSpace L := hC
    let : IsAlgClosed L := hA
    refine ⟨L, hL, hC, hA, f.comp σ, ?_⟩
    simpa only [RingHom.comp_apply, hf] using hv

theorem finiteType_nontorsion_expanding_embedding
    {K : Type} [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K]
    (z : K) (hz : z ≠ 0) (hnt : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (f : K →+* L), 1 < ‖f z‖ := by
  by_cases ha : IsAlgebraic ℚ z
  · let F := IntermediateField.adjoin ℚ {z}
    let zF : F := IntermediateField.AdjoinSimple.gen ℚ z
    let : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional ha.isIntegral
    let : NumberField F := NumberField.of_module_finite ℚ F
    have hzF : zF ≠ 0 := fun h => hz (congrArg (fun a : F => (a : K)) h)
    have hnF (m : ℕ) (hm : 0 < m) : zF ^ m ≠ 1 := by
      intro h
      exact hnt m hm (congrArg (fun a : F => (a : K)) h)
    obtain ⟨L, hL, hC, hA, f, hf⟩ := numberField_expanding_normed_embedding zF hzF hnF
    let : NontriviallyNormedField L := hL
    let : CompleteSpace L := hC
    let : IsAlgClosed L := hA
    let : Uncountable L := uncountable_complete_normedField L
    let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
    let : Algebra F L := f.toAlgebra
    let : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp ℚ F K
    obtain ⟨g⟩ := nonempty_algHom_of_countable_finite_trdeg F K L
    refine ⟨L, hL, hC, hA, g.toRingHom, ?_⟩
    have hg := g.commutes zF
    change g z = f zF at hg
    change 1 < ‖g z‖
    rw [hg]
    exact hf
  · obtain ⟨f, hf⟩ := transcendental_expanding_complex_embedding z ha
    exact ⟨ℂ, inferInstance, inferInstance, inferInstance, f, hf⟩

end PolycyclicRecognition

end

end OAI
