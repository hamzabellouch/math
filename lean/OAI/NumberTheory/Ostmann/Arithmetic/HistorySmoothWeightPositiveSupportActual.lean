import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPositiveSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
variable {ι : Type*}

theorem allPivots_encode_node_iff (P : ℝ→Prop) (x : ι→ℝ)
    {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ} {a : State} {p : ℕ}
    {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : InternalKey (.node a p u hp hm left right)→Expr ι) :
    AllPivots P x (.node a p u hp hm left right)
      (encode V outside _ hs e comp) ↔
      P ((pivotExpr hs e (fun i => comp (Sum.inl i))).realEval x) ∧
      AllPivots P x left (encode V outside left (History.supported_left hs)
        (leftState hs e (fun i => comp (Sum.inl i)))
        (fun i => comp (Sum.inr (Sum.inl i)))) ∧
      AllPivots P x right (encode V outside right (History.supported_right hs)
        (rightState hs e (fun i => comp (Sum.inl i)))
        (fun i => comp (Sum.inr (Sum.inr i)))) := by
  simp only [encode,AllPivots,treeRoot_encode,leftState]

theorem pivotExpr_pos_of_encode_scalar_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι→ℝ) {l : ℕ} {V : ℕ→ℕ} {a : State} {p : ℕ}
    {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : InternalKey (.node a p u hp hm left right)→Expr ι)
    (hz : realHistoryScalar b s X tb td G outside x (.node a p u hp hm left right)
      (encode V outside _ hs e comp)≠0) :
    0 < (pivotExpr hs e (fun i => comp (Sum.inl i))).realEval x := by
  have hpos := allPivotsPositive_of_realHistoryScalar_ne_zero b s X tb td G outside x
    (.node a p u hp hm left right) (encode V outside _ hs e comp) hz
  exact ((allPivots_encode_node_iff (fun p => 0 < p) x hs e comp).mp hpos).1

theorem allPivotCells_of_actualRealHistoryScalar_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) {l : ℕ} {V : ℕ→ℕ} (h : History l) (hs : h.Supported V outside)
    (x : Key h→ℝ) (hz : actualRealHistoryScalar b s X tb td G outside h hs x≠0) :
    AllPivotCells G x h (symbolicHistory h hs) :=
  allPivotCells_of_realHistoryScalar_ne_zero b s X tb td G outside x h (symbolicHistory h hs) hz

theorem allPivotsPositive_of_actualRealHistoryScalar_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) {l : ℕ} {V : ℕ→ℕ} (h : History l) (hs : h.Supported V outside)
    (x : Key h→ℝ) (hz : actualRealHistoryScalar b s X tb td G outside h hs x≠0) :
    AllPivotsPositive x h (symbolicHistory h hs) :=
  (allPivotCells_of_actualRealHistoryScalar_ne_zero b s X tb td G outside h hs x hz).positive

theorem actualRealHistoryScalar_eq_zero_of_not_allPivotsPositive (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) {l : ℕ} {V : ℕ→ℕ} (h : History l) (hs : h.Supported V outside)
    (x : Key h→ℝ) (hn : ¬AllPivotsPositive x h (symbolicHistory h hs)) :
    actualRealHistoryScalar b s X tb td G outside h hs x=0 :=
  realHistoryScalar_eq_zero_of_not_allPivotsPositive b s X tb td G outside x h
    (symbolicHistory h hs) hn

theorem allPivotCells_of_actualRealXi_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) {l : ℕ} {V : ℕ→ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁→ℝ) (x₂ : Key h₂→ℝ)
    (hz : actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂≠0) :
    AllPivotCells G x₁ h₁ (symbolicHistory h₁ hs₁) ∧
      AllPivotCells G x₂ h₂ (symbolicHistory h₂ hs₂) := by
  have hparts : actualRealHistoryScalar b s X tb td G outside h₁ hs₁ x₁≠0 ∧
      actualRealHistoryScalar b s X tb td G outside h₂ hs₂ x₂≠0 := by
    simpa only [actualRealXi,mul_ne_zero_iff,star_ne_zero] using hz
  exact ⟨allPivotCells_of_actualRealHistoryScalar_ne_zero b s X tb td G outside h₁ hs₁ x₁ hparts.1,
    allPivotCells_of_actualRealHistoryScalar_ne_zero b s X tb td G outside h₂ hs₂ x₂ hparts.2⟩

theorem allPivotsPositive_of_actualRealXi_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) {l : ℕ} {V : ℕ→ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁→ℝ) (x₂ : Key h₂→ℝ)
    (hz : actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂≠0) :
    AllPivotsPositive x₁ h₁ (symbolicHistory h₁ hs₁) ∧
      AllPivotsPositive x₂ h₂ (symbolicHistory h₂ hs₂) := by
  have hp := allPivotCells_of_actualRealXi_ne_zero b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂ hz
  exact ⟨hp.1.positive,hp.2.positive⟩

theorem actualRealXi_eq_zero_of_not_allPivotsPositive (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) {l : ℕ} {V : ℕ→ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁→ℝ) (x₂ : Key h₂→ℝ)
    (hn : ¬AllPivotsPositive x₁ h₁ (symbolicHistory h₁ hs₁) ∨
      ¬AllPivotsPositive x₂ h₂ (symbolicHistory h₂ hs₂)) :
    actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂=0 := by
  by_contra hz
  have hp := allPivotsPositive_of_actualRealXi_ne_zero b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂ hz
  exact hn.elim (fun h => h hp.1) (fun h => h hp.2)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
