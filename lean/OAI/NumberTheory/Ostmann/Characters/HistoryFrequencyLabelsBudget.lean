import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabels
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsNodes
import OAI.NumberTheory.Ostmann.Characters.TemplateResidueExposure

namespace OAI

noncomputable section
namespace Ostmann.Characters.HistoryFrequencyLabels
open FrequencyExposure

@[reducible] def DataMatches {R : ℕ} (d : List Bool → Data R) :
    (k : ℕ) → List Bool → ℤ → HistoryReconstruction.Tree k → Prop
  | 0, _, _, _ => True
  | k+1, p, s, t =>
      ((d p).s = s ∧ (d p).s' = s ∧ (d p).v = t.1.1 ∧ (d p).w = t.1.2 ∧
        (d p).v' = t.1.1 ∧ (d p).w' = t.1.2) ∧
      DataMatches d k (false::p) t.1.1 t.2.1 ∧
      DataMatches d k (true::p) t.1.2 t.2.2

theorem dataMatches_of_nodes {R : ℕ} (d : List Bool → Data R)
    (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k)
    (h : ∀ q a, (q,a) ∈ nodes k p s t →
      (d q).s = a.1 ∧ (d q).s' = a.1 ∧ (d q).v = a.2.1 ∧ (d q).w = a.2.2 ∧
      (d q).v' = a.2.1 ∧ (d q).w' = a.2.2) : DataMatches d k p s t := by
  induction k generalizing p s with
  | zero => trivial
  | succ k ih =>
    refine ⟨h p (s,t.1.1,t.1.2) List.mem_cons_self, ?_, ?_⟩
    · apply ih
      intro q a ha
      exact h q a (List.mem_cons_of_mem _ (List.mem_append_left _ ha))
    · apply ih
      intro q a ha
      exact h q a (List.mem_cons_of_mem _ (List.mem_append_right _ ha))

theorem diagonalData_matches (k : ℕ) (p : List Bool) (s : ℤ)
    (t : HistoryReconstruction.Tree k) :
    DataMatches (diagonalData k p s t) k p s t :=
  dataMatches_of_nodes _ k p s t (fun _ _ h => diagonalData_at h)

theorem budget_eq_literalWeight {R : ℕ} (d : List Bool → Data R) (C : NNReal)
    (ε : ℝ) (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k)
    (h : DataMatches d k p s t) :
    ((FrequencyExposure.budget C ε d k p).value : ℝ) =
      literalWeight (ReducedFrequencyTree.factor ε C) k p s t := by
  induction k generalizing p s with
  | zero => rfl
  | succ k ih =>
    change (C:ℝ)*(reducedPair (d p):ℝ)^(ε-1)*
      ((FrequencyExposure.budget C ε d k (false::p)).value:ℝ)*
      ((FrequencyExposure.budget C ε d k (true::p)).value:ℝ) =
      ReducedFrequencyTree.factor ε C p s t.1.1 t.1.2 *
        literalWeight (ReducedFrequencyTree.factor ε C) k (false::p) t.1.1 t.2.1 *
        literalWeight (ReducedFrequencyTree.factor ε C) k (true::p) t.1.2 t.2.2
    rw [ih _ _ _ h.2.1, ih _ _ _ h.2.2]
    rcases h.1 with ⟨hs,hs',hv,hw,hv',hw'⟩
    simp only [reducedPair,hs,hs',hv,hw,hv',hw',Nat.lcm_self,ReducedFrequencyTree.factor]

theorem dataMatches_ambient {R : ℕ} (d : List Bool → Data R) (K k : ℕ)
    (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k)
    (h : DataMatches d k p s t) :
    DataMatches (fun q => Template.ambientData K R (d q)) k p s t := by
  induction k generalizing p s with
  | zero => trivial
  | succ k ih => exact ⟨h.1, ih _ _ _ h.2.1, ih _ _ _ h.2.2⟩

theorem diagonal_ambient_budget_eq (C : NNReal) (ε : ℝ) (K k : ℕ)
    (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k) :
    ((FrequencyExposure.budget C ε
      (fun q => Template.ambientData K (modulus k p s t) (diagonalData k p s t q))
        k p).value : ℝ) = literalWeight (ReducedFrequencyTree.factor ε C) k p s t :=
  budget_eq_literalWeight _ C ε k p s t
    (dataMatches_ambient _ K k p s t (diagonalData_matches k p s t))

end Ostmann.Characters.HistoryFrequencyLabels

end

end OAI
