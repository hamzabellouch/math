import OAI.Probability.MatroidProphet.Residual.Nominal
import OAI.Probability.MatroidProphet.Residual.Transfer
import OAI.Probability.MatroidProphet.Reverse.Paths

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α]

noncomputable def nominalLayerSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : Set α :=
  {e | e ∈ U ∧ activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
    e ∈ nominalPath M hE κ D C h b.val.val ∧ e ∉ nominalPath M hE κ D C h (b.val.val - 1)}

noncomputable def nominalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M (nominalLayerSet M hE κ D C h U ε b \ O)
      (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def safeLayerSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : Set α :=
  (I ∩ nominalLayerSet M hE κ D C h U ε b) \
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def safeLayerStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε, (safeLayerSet M hE κ D C T h U I ε b).ncard

def boolParity (parity : Bool) : Fin 2 := if parity then 1 else 0

lemma boolParity_val (parity : Bool) : ((boolParity parity).val : ℤ) = (if parity then 1 else 0) := by
  cases parity <;> rfl

lemma nominalLayerSet_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : nominalLayerSet M hE κ D C h U ε b ⊆ U :=
  fun _ he => he.1

lemma nominalLayerSet_disjoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2) :
    Pairwise (fun b c => Disjoint (nominalLayerSet M hE κ D C h U ε b)
      (nominalLayerSet M hE κ D C h U ε c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro e hb hc
  have hval : b.val.val ≠ c.val.val := by
    intro heq
    exact hbc (Subtype.ext (Subtype.ext heq))
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · exact hc.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hb.2.2.2.1)
  · exact hb.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hc.2.2.2.1)

end MatroidProphet

end OAI
