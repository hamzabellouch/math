import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CountSumDimension
import OAI.Combinatorics.Chromatic.Walls.StringPositiveFactor

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle
noncomputable section
variable {A B I : Type*}
variable (a : A→ℕ) (b : B→ℕ) (da : A→(I→ℕ)) (db : B→(I→ℕ))
variable (ka : A→ℤ) (kb : B→ℤ)

def stringSumEven (x : (A×ℕ)⊕(B×ℕ)) : Prop :=
  Sum.elim (fun y:A×ℕ=>a y.1≠0) (fun y:B×ℕ=>b y.1≠0) x

lemma stringSumEven_iff (x : (A⊕B)×ℕ) :
    Sum.elim a b x.1≠0 ↔ stringSumEven a b (Equiv.sumProdDistrib A B ℕ x) := by
  rcases x with ⟨x,j⟩
  cases x <;> rfl

def stringSumCounts (d : I→ℕ) :
    StringCounts (Sum.elim a b) (Sum.elim da db) d ≃
      DimensionCounts (stringSumEven a b)
        (Sum.elim (fun x:A×ℕ=>da x.1) (fun x:B×ℕ=>db x.1)) d :=
  (countReindex (Equiv.sumProdDistrib A B ℕ) _ _ (stringSumEven_iff a b)).subtypeEquiv (fun f=>by
    change f.val.sum _=d ↔ (countReindex _ _ _ (stringSumEven_iff a b) f).val.sum _=d
    rw [countReindex_sum]
    have H : ∀x:(A⊕B)×ℕ,Sum.elim (fun x:A×ℕ=>da x.1) (fun x:B×ℕ=>db x.1)
        (Equiv.sumProdDistrib A B ℕ x)=Sum.elim da db x.1 := by
      intro x
      rcases x with ⟨x,j⟩
      cases x <;> rfl
    simp_rw [H])

lemma stringSumCounts_energy (d : I→ℕ) (f : StringCounts (Sum.elim a b) (Sum.elim da db) d) :
    countEnergy (stringSumEven a b)
      (Sum.elim (fun x:A×ℕ=>ka x.1-2*(x.2:ℤ)) (fun x:B×ℕ=>kb x.1-2*(x.2:ℤ)))
      (stringSumCounts a b da db d f).val=
      stringEnergy (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb) d f := by
  change (countReindex _ _ _ (stringSumEven_iff a b) f.val).val.sum _=_
  rw [countReindex_sum]
  dsimp only [stringEnergy,countEnergy]
  apply Finsupp.sum_congr
  intro x hx
  rcases x with ⟨x,j⟩
  cases x <;> rfl

variable [Fintype I] [DecidableEq I]
variable (ha : ∀d,Admissible (stringEnergy a da ka d))
variable (hb : ∀d,Admissible (stringEnergy b db kb d))
include ha hb in
lemma stringSum_admissible (d : I→ℕ) :
    Admissible (stringEnergy (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb) d) :=
  admissible_injective
    (countSum_admissible (fun x:A×ℕ=>a x.1≠0) (fun x:B×ℕ=>b x.1≠0)
      (fun x=>da x.1) (fun x=>db x.1)
      (fun x=>ka x.1-2*(x.2:ℤ)) (fun x=>kb x.1-2*(x.2:ℤ)) ha hb d)
    (stringSumCounts a b da db d) (stringSumCounts a b da db d).injective
    (stringSumCounts_energy a b da db ka kb d)

lemma stringSum_series (d : I→ℕ) :
    stringSeries (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb)
      (stringSum_admissible a b da db ka kb ha hb) d=
      ∑s : DimensionSplit d,stringSeries a da ka ha s.left*stringSeries b db kb hb s.right := by
  rw [stringSeries,series_equiv _
    (countSum_admissible (fun x:A×ℕ=>a x.1≠0) (fun x:B×ℕ=>b x.1≠0)
      (fun x=>da x.1) (fun x=>db x.1)
      (fun x=>ka x.1-2*(x.2:ℤ)) (fun x=>kb x.1-2*(x.2:ℤ)) ha hb d)
    (stringSumCounts a b da db d)
    (stringSumCounts_energy a b da db ka kb d)]
  exact countSum_series (fun x:A×ℕ=>a x.1≠0) (fun x:B×ℕ=>b x.1≠0)
    (fun x=>da x.1) (fun x=>db x.1)
    (fun x=>ka x.1-2*(x.2:ℤ)) (fun x=>kb x.1-2*(x.2:ℤ)) ha hb d
end
end ElementaryPositivity.UnitSelections

end

end OAI
