import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceDataSplitWidth

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

theorem canonicalSourceLeafDataSplitWidth_degreeCost (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (X Δ Wp Wl H : ℝ) (D M : ℕ) (he : ∀u,(e u).syntaxSize ≤ M) :
    (canonicalSourceLeafDataSplitWidth k B V T J j b s e t i x X Δ Wp Wl H D).degreeCost ≤
      sourceDegreeFactor k j*(M+1)+1 := by
  let Z := sourceExpressionFactor k j*(M+1)
  have hg : ∀q : Fin (canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t).length,
      ((canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t).get q).expression.syntaxSize ≤ Z := by
    intro q
    have hh := canonicalSourceGuardListSplitWidth_size k B V T J X Δ Wp Wl j s e t M he _ (List.get_mem _ q)
    exact hh.trans (Nat.mul_le_mul_right (M+1) (Nat.le_add_right _ _))
  have hl : ∀q : Fin (2^j),
      (periodExpression k (indexedBottomExpressions k j b s e t q).2.2).syntaxSize ≤ Z := by
    intro q
    have hm : periodExpression k (indexedBottomExpressions k j b s e t q).2.2 ∈
        obstructionExpressions k j b s e t :=
      List.mem_append_right _ (List.mem_map.mpr
        ⟨_,indexedBottomExpressions_mem k j b s e t q,rfl⟩)
    have hh := obstructionExpressions_size k j b s e t M he _ hm
    exact hh.trans (Nat.mul_le_mul_right (M+1) (Nat.le_add_left _ _))
  have hh := leafData_degreeCost_size k _ _ i x X (coarseLower D H Δ Wl) (-Δ+Wl) Z hg hl
  simp only [Fintype.card_fin] at hh
  apply hh.trans
  have hc := canonicalSourceGuardListSplitWidth_length_le k B V T J X Δ Wp Wl j s e t
  change 2*((canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s e t).length+3*2^j)*Z+1 ≤ _
  calc
    _ ≤ 2*((guardCountFactor k j+8*2^j)+3*2^j)*Z+1 := by gcongr
    _ = sourceDegreeFactor k j*(M+1)+1 := by dsimp [sourceDegreeFactor,Z]; ring

theorem sampled_canonicalSourceLeafDataSplitWidth_degreeCost (k j : ℕ) (width : Role → ℕ)
    (m : ℕ) (hw : ∀r,width r ≤ m+1) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (b : Bool) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (x : Other i → ℤ)
    (X Δ Wp Wl H : ℝ) (D : ℕ) :
    (canonicalSourceLeafDataSplitWidth k B V T J j b s (sampledExpressions k j width) t i x
      X Δ Wp Wl H D).degreeCost ≤ sourceDegreeFactor k j*(2*(m+2)+1)+1 := by
  apply canonicalSourceLeafDataSplitWidth_degreeCost k B V T J j b s _ t i x X Δ Wp Wl H D (2*(m+2))
  intro u
  have hh := hw ((schedule k j).role u)
  exact (sampledExpressions_syntaxSize k j width u).trans (by omega)

theorem sampled_canonicalSourceGuardListSplitWidth_good (k j : ℕ) (width : Role → ℕ)
    (B V : ℕ → ℤ) (T : ℕ → ℝ) (J : ℤ) (X Δ Wp Wl : ℝ)
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (a : (schedule k j).Constituent width → ℤ)
    (hf : frequencyArithmetic k V j s
      (evalExpressions a (sampledExpressions k j width)) t) :
    ∀ q ∈ canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s
      (sampledExpressions k j width) t, HistoryReconstruction.Good a q.expression :=
  canonicalSourceGuardListSplitWidth_good k B V T J X Δ Wp Wl j s _ t a
    (sampledExpressions_good k j width a) hf

theorem sampled_canonicalSourceGuardListSplitWidth_size (k j : ℕ) (width : Role → ℕ)
    (m : ℕ) (hw : ∀r,width r ≤ m+1) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ Wp Wl : ℝ) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    ∀ q ∈ canonicalSourceGuardListSplitWidth k B V T J X Δ Wp Wl j s
      (sampledExpressions k j width) t,
      q.expression.syntaxSize ≤ sourceExpressionFactor k j*(2*(m+2)+1) := by
  have he (u : (schedule k j).Slot) :
      (sampledExpressions k j width u).syntaxSize ≤ 2*(m+2) := by
    have hh := hw ((schedule k j).role u)
    exact (sampledExpressions_syntaxSize k j width u).trans (by omega)
  intro q hq
  have h := canonicalSourceGuardListSplitWidth_size k B V T J X Δ Wp Wl j s
    (sampledExpressions k j width) t (2*(m+2)) he q hq
  exact h.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
