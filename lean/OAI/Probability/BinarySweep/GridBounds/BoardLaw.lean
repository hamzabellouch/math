import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridSplitSweep
import OAI.Probability.BinarySweep.FiniteLaws.FiniteLawAverage

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open GridSplit

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

abbrev BoardChoices (X Y : Type*) := (Y → Equiv.Perm X) × (X → Equiv.Perm Y)
def boardWeight (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ)
    (LR : BoardChoices X Y) : ℝ := (∏y,p (LR.1 y))*(∏x,q (LR.2 x))
def boardSweep (LR : BoardChoices X Y) : Equiv.Perm (X×Y) :=
  columnPerm LR.2 * rowPerm LR.1
def boardLaw (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) : Equiv.Perm (X×Y) → ℝ :=
  pushLaw (boardWeight p q) boardSweep

lemma boardSampleLaw {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → Equiv.Perm X) (g : B → Equiv.Perm Y) :
    pushLaw (fun LR : (Y → A)×(X → B) => (∏y,p (LR.1 y))*(∏x,q (LR.2 x)))
      (fun LR => columnPerm (g ∘ LR.2) * rowPerm (f ∘ LR.1))=
      boardLaw (pushLaw p f) (pushLaw q g) := by
  have he := pushLaw_prod (fun L : Y → A => ∏y,p (L y)) (fun R : X → B => ∏x,q (R x))
    (fun L y => f (L y)) (fun R x => g (R x))
  rw [pushLaw_pi,pushLaw_pi] at he
  unfold boardLaw boardWeight
  rw [←he,pushLaw_comp]
  rfl

variable {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y']

def boardChoicesEquiv (e : X ≃ X') (f : Y ≃ Y') : BoardChoices X Y ≃ BoardChoices X' Y' :=
  Equiv.prodCongr (f.arrowCongr e.permCongr) (e.arrowCongr f.permCongr)

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma rowPerm_congr (e : X ≃ X') (f : Y ≃ Y') (L : Y → Equiv.Perm X) :
    (Equiv.prodCongr e f).permCongr (rowPerm L)=
      rowPerm (f.arrowCongr e.permCongr L) := by
  apply Equiv.ext
  intro xy
  apply Prod.ext <;> simp [rowPerm,Equiv.permCongr_apply,Equiv.arrowCongr_apply]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma columnPerm_congr (e : X ≃ X') (f : Y ≃ Y') (R : X → Equiv.Perm Y) :
    (Equiv.prodCongr e f).permCongr (columnPerm R)=
      columnPerm (e.arrowCongr f.permCongr R) := by
  apply Equiv.ext
  intro xy
  apply Prod.ext <;> simp [columnPerm,Equiv.permCongr_apply,Equiv.arrowCongr_apply]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y'] in
lemma boardSweep_congr (e : X ≃ X') (f : Y ≃ Y') (LR : BoardChoices X Y) :
    (Equiv.prodCongr e f).permCongr (boardSweep LR)=
      boardSweep (boardChoicesEquiv e f LR) := by
  change (Equiv.prodCongr e f).permCongrHom (columnPerm LR.2 * rowPerm LR.1)=_
  rw [map_mul]
  change (Equiv.prodCongr e f).permCongr (columnPerm LR.2) *
    (Equiv.prodCongr e f).permCongr (rowPerm LR.1)=_
  rw [rowPerm_congr,columnPerm_congr]
  rfl

omit [DecidableEq X'] [DecidableEq Y'] in
lemma boardWeight_congr (e : X ≃ X') (f : Y ≃ Y')
    (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) (LR : BoardChoices X Y) :
    boardWeight (pushLaw p e.permCongr) (pushLaw q f.permCongr)
      (boardChoicesEquiv e f LR)=boardWeight p q LR := by
  unfold boardWeight boardChoicesEquiv
  simp only [Equiv.prodCongr_apply,pushLaw_equiv_apply]
  rw [←f.prod_comp,←e.prod_comp]
  have he (σ : Equiv.Perm X) : e.symm.permCongr (e.permCongr σ)=σ :=
    e.permCongr.symm_apply_apply σ
  have hf (σ : Equiv.Perm Y) : f.symm.permCongr (f.permCongr σ)=σ :=
    f.permCongr.symm_apply_apply σ
  simp [Equiv.arrowCongr_apply,he,hf]

lemma boardLaw_congr (e : X ≃ X') (f : Y ≃ Y')
    (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) :
    pushLaw (boardLaw p q) (Equiv.prodCongr e f).permCongr=
      boardLaw (pushLaw p e.permCongr) (pushLaw q f.permCongr) := by
  unfold boardLaw
  rw [pushLaw_comp]
  have hw : boardWeight (pushLaw p e.permCongr) (pushLaw q f.permCongr) ∘
      boardChoicesEquiv e f=boardWeight p q := funext (boardWeight_congr e f p q)
  have hs : (Equiv.prodCongr e f).permCongr ∘ boardSweep=
      boardSweep ∘ boardChoicesEquiv e f := funext (boardSweep_congr e f)
  rw [hs,←hw]
  exact pushLaw_equiv (boardChoicesEquiv e f) _ _

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {X Y A B Ω : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype Ω]
lemma board_equiv_sample (p : A → ℝ) (q : B → ℝ)
    (f : A → Equiv.Perm X) (g : B → Equiv.Perm Y)
    (e : Ω ≃ (Y → A)×(X → B)) (w : Ω → ℝ) (F : Ω → Equiv.Perm (X×Y))
    (hw : ∀c,w c=(∏y,p ((e c).1 y))*(∏x,q ((e c).2 x)))
    (hF : ∀c,F c=GridSplit.columnPerm (g ∘ (e c).2)*GridSplit.rowPerm (f ∘ (e c).1)) :
    pushLaw w F=boardLaw (pushLaw p f) (pushLaw q g) := by
  have hw' : w=(fun LR : (Y→A)×(X→B) => (∏y,p (LR.1 y))*(∏x,q (LR.2 x))) ∘ e := funext hw
  have hf' : F=(fun LR : (Y→A)×(X→B) => GridSplit.columnPerm (g ∘ LR.2)*GridSplit.rowPerm (f ∘ LR.1)) ∘ e := funext hF
  rw [hw',hf',pushLaw_equiv]
  exact boardSampleLaw p q f g
end BinaryCoordinateSweeps

end

end OAI
