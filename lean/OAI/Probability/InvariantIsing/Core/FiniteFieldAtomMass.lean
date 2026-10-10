import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure

namespace OAI

/-! Atom masses of a finitely supported external-field law, allowing
several labels to describe the same field value. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def fieldAtomMass {A : Type*} [Fintype A] (γ c : A → ℝ) (x : ℝ) : ℝ :=
  ∑ a, if c a=x then γ a else 0

lemma finiteField_atom_mass {A : Type*} [Fintype A] (γ c : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (x : ℝ) :
    (finiteSpectralMeasure γ c).real {x}=fieldAtomMass γ c x := by
  have hi := integral_finiteSpectralMeasure γ c hγ
    (({x} : Set ℝ).indicator (fun _ => (1:ℝ)))
  change (∫ y, ({x} : Set ℝ).indicator (1 : ℝ → ℝ) y ∂finiteSpectralMeasure γ c) = _ at hi
  rw [integral_indicator_one (measurableSet_singleton x)] at hi
  simpa only [fieldAtomMass,Set.indicator_apply,Set.mem_singleton_iff,mul_ite,
    mul_one,mul_zero] using hi

lemma fieldAtomMass_nonneg {A : Type*} [Fintype A] (γ c : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (x : ℝ) : 0 ≤ fieldAtomMass γ c x := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hγ a
  · rfl

lemma fieldAtomMass_pos_at {A : Type*} [Fintype A] (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (a : A) : 0 < fieldAtomMass γ c (c a) := by
  have hh := Finset.single_le_sum (f := fun i => if c i=c a then γ i else 0)
    (fun i _ => by split_ifs; exact (hγ i).le; rfl) (Finset.mem_univ a)
  simp only [ite_true] at hh
  exact (hγ a).trans_le hh

lemma fieldAtomMass_eq_of_law_eq {A B : Type*} [Fintype A] [Fintype B]
    (γ c : A → ℝ) (δ d : B → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ j, 0 ≤ δ j)
    (he : finiteSpectralMeasure γ c=finiteSpectralMeasure δ d) (x : ℝ) :
    fieldAtomMass γ c x=fieldAtomMass δ d x := by
  rw [← finiteField_atom_mass γ c hγ,← finiteField_atom_mass δ d hδ,he]

end InvariantIsing

end

end OAI
