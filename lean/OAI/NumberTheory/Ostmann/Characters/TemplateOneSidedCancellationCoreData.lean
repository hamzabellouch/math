import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCoarseWindow
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationDataNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedWindowRegularityMasks

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def coarseLower (D : ℕ) (H Δ W : ℝ) : ℝ := min (-(D:ℝ)*H) (-Δ+W)

def coreLeafData (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (X Δ W H : ℝ) (D : ℕ) :
    HistoryPolynomialData (Fin (coreGuardList k B V g m j s e t).length ⊕ (Fin (2^j) × Bool))
      (Fin (2^j)) :=
  leafData k (fun q => (coreGuardList k B V g m j s e t).get q)
    (indexedBottomExpressions k j b s e t) i x X (coarseLower D H Δ W) (-Δ+W)

omit [DecidableEq ι] in
theorem coreGuardList_good [_decidableEqIndex : DecidableEq ι] (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (hg : ∀j s a q,q∈g j s → HistoryReconstruction.Good a q.expression)
    (hm : ∀j s a q,q∈m j s → HistoryReconstruction.Good a q.expression)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (a : ι → ℤ) (he : ∀i,HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀q∈coreGuardList k B V g m j s e t,HistoryReconstruction.Good a q.expression := by
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · exact historyGuards_good k B V g hg j s e t a he hf q hq
  · exact maskGuards_good k V m hm j s e t a he hf q hq

theorem coreLeafData_weight (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (hg : ∀j s a q,q∈g j s → HistoryReconstruction.Good a q.expression)
    (hm : ∀j s a q,q∈m j s → HistoryReconstruction.Good a q.expression)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (n : ℤ)
    {X Δ W H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (he : ∀u,HistoryReconstruction.Good (insertCoordinate i x n) (e u))
    (hs : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).syntaxSize ≤ D)
    (hfixed : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).FixedLogBound H)
    (hvars : ∀u,|((insertCoordinate i x n u : ℤ) : ℝ)| ≤ Real.exp H)
    (hf : frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x n) e) t) :
    (coreLeafData k B V g m j b s e t i x X Δ W H D).weight
      (𝓕 SchwartzCutoff.psi) (n:ℝ) =
      conjugateBy b (coreHistoryWeight k (fun j _ => B j) (fun j _ => V j)
        (fun j s x _ => canonicalMask k g j s x) (canonicalMask k m)
        X Δ W j s (evalExpressions (insertCoordinate i x n) e) t) := by
  have hx : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hgood := indexedBottomExpressions_period_good_of_frequencyArithmetic k V j b s e t _ he hf
  have hupper (u : Fin (2^j)) :
      (period k 0 (evalBottom k (insertCoordinate i x n) (indexedBottomExpressions k j b s e t u)).2.2:ℝ) ≤
        X*Real.exp (-coarseLower D H Δ W) := by
    apply (period_upper_from_syntax k _ _ hX hH D (hs u) (hfixed u) hvars (hgood u)).trans
    apply mul_le_mul_of_nonneg_left _ hx.le
    apply Real.exp_le_exp.mpr
    have hh := min_le_left (-(D:ℝ)*H) (-Δ+W)
    dsimp only [coarseLower]
    linarith
  have hg' := coreGuardList_good k B V g m hg hm j s e t _ he hf
  rw [coreLeafData,leafData_weight_eq_original_lower k _ _ i x n hx
    (fun u => hg' _ (List.get_mem _ u)) hgood hupper,
    coreHistoryWeight_eq_profiles k B V g m X Δ W hx j b s e t _]
  simp only [hf,true_and,guardsHold,List.forall_mem_iff_get]
  split_ifs <;> rfl

theorem coordinate_coreLeafData_weight (k : ℕ) (B V : ℕ → ℤ)
    (g m : (l : ℕ) → ℤ → Fin (coordinateWindowExpressions k l).length → Option SourceWindow)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (n : ℤ)
    {X Δ W H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (he : ∀u,HistoryReconstruction.Good (insertCoordinate i x n) (e u))
    (hs : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).syntaxSize ≤ D)
    (hfixed : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).FixedLogBound H)
    (hvars : ∀u,|((insertCoordinate i x n u : ℤ) : ℝ)| ≤ Real.exp H)
    (hf : frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x n) e) t) :
    (coreLeafData k B V (fun l v=>coordinateWindowGuards k l (g l v))
      (fun l v=>coordinateWindowGuards k l (m l v)) j b s e t i x X Δ W H D).weight
      (𝓕 SchwartzCutoff.psi) (n:ℝ) =
      conjugateBy b (coreHistoryWeight k (fun j _ => B j) (fun j _ => V j)
        (fun l v x _ => canonicalMask k (fun l v=>coordinateWindowGuards k l (g l v)) l v x)
        (canonicalMask k (fun l v=>coordinateWindowGuards k l (m l v)))
        X Δ W j s (evalExpressions (insertCoordinate i x n) e) t) :=
  coreLeafData_weight k B V _ _
    (fun l v a=>coordinateWindowGuards_good k l (g l v) a)
    (fun l v a=>coordinateWindowGuards_good k l (m l v) a)
    j b s e t i x n hX hH D he hs hfixed hvars hf

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
