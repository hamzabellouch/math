import Mathlib
import OAI.Geometry.HyperbolicGroups.Selection
import OAI.Geometry.HyperbolicGroups.SamplingStage
import OAI.Geometry.HyperbolicGroups.Presentation

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))

abbrev LetterGroup (m : ℕ) := LetterPresentation.Group (s m).size (s m).master (s m).six

def letter (m : ℕ) : (Alphabet s) m → LetterGroup s m :=
  LetterPresentation.letter (s m).size (s m).master (s m).six

def inverse (m : ℕ) : (Alphabet s) m ≃ (Alphabet s) m :=
  LetterPresentation.inverseLetter (s m).size

lemma letter_inverse (m : ℕ) (i : (Alphabet s) m) :
    letter s m (inverse s m i) = (letter s m i)⁻¹ :=
  LetterPresentation.letter_inv _ _ _ _

lemma letter_generates (m : ℕ) : Subgroup.closure (Set.range (letter s m)) = ⊤ :=
  LetterPresentation.letter_generates _ _ _

def potential (m : ℕ) (a : (Matches s) m) : MasterGraph.Potential (label s m a) (letter s m) :=
  LetterPresentation.potential _ _ _ a

abbrev Rows (m : ℕ) (u : (Alphabet s) m) := SixTable.Rows (s m).six u
instance (m : ℕ) (u : (Alphabet s) m) : Nonempty (Rows s m u) :=
  SixTable.rows_nonempty ((stageError_le_third m).trans_lt (by norm_num)) (s m).six_good u

def rowLaw (m : ℕ) (u : (Alphabet s) m) : FiniteLaw (Rows s m u) := FiniteLaw.uniform

def row (m : ℕ) (u : (Alphabet s) m) (x : Rows s m u) : Fin 5 → (Alphabet s) m :=
  SixTable.row (s m).six u x

lemma row_relation (m : ℕ) (u : (Alphabet s) m) (x : Rows s m u) :
    (List.ofFn (letter s m ∘ row s m u x)).prod = (letter s m u)⁻¹ :=
  LetterPresentation.six_tail_relator _ _ _ _ _

lemma marginal (m : ℕ) (u : (Alphabet s) m) (j : Fin 5) (i : (Alphabet s) m) :
    (((rowLaw s m u).map (fun x => row s m u x j)).mass i) ≤ 2 / Fintype.card ((Alphabet s) m) :=
  SixTable.marginal_bound (stageError_le_third m) (s m).six_good u j i

/-- Concrete no-action conclusion for the literal random letter presentations,
provided the still-missing diagram argument proves those same groups infinite.
The sampling laws, relator potentials, row relations and marginals are proved,
not supplied by this hypothesis. -/
theorem eventually_noAction [∀ m, Infinite (LetterGroup s m)] :
    ∀ᶠ m in atTop, NoGeometricCATZeroAction (LetterGroup s m) :=
  MasterGraph.eventually_noAction (letter s) (inverse s) (letter_inverse s)
    (letter_generates s) (potential s) (samplingSequence s) (Rows s) (rowLaw s)
    (row s) (row_relation s) (marginal s)

end SamplingStage
end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
