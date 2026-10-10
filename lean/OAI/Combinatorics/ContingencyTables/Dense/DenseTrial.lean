import OAI.Combinatorics.ContingencyTables.Dense.DenseOffsets

namespace OAI

/-! # Accepted dense trials are in bijection with the actual tables -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

abbrev DenseTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (q : ℕ) :=
  Grid (I := Fin q) (4 * d ^ 8) × Offset (integerWidth R P d)

def trialFree (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (e : I × J ≃ Fin q)
    (t : DenseTrial R P d q) : I × J → ℕ :=
  fun p => (trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8) t p).val

def TrialAccepted (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (e : I × J ≃ Fin q)
    (t : DenseTrial R P d q) : Prop := ∀ i j, 0 ≤ DenseAffine.integerTable R P (trialFree R P d e t) i j

def trialTable (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (e : I × J ≃ Fin q)
    (htotal : ∑ i, R i = ∑ j, P j) (t : DenseTrial R P d q) (ht : TrialAccepted R P d e t) :
    Table R P := ⟨DenseAffine.naturalTable R P (trialFree R P d e t),
      DenseAffine.naturalTable_rows R P _ ht, DenseAffine.naturalTable_columns R P _ ht htotal⟩

def tableTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) : DenseTrial R P d q :=
  (trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8)).symm (tableFreeBox R P d hd hR hP X)

theorem trialFree_tableTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) (p : I × J) :
    trialFree R P d e (tableTrial R P d hd hR hP e X) p = X.val (some p.1) (some p.2) := by
  exact congrArg Fin.val (congrFun
    ((trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8)).apply_symm_apply
      (tableFreeBox R P d hd hR hP X)) p)

theorem tableTrial_accepted (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) :
    TrialAccepted R P d e (tableTrial R P d hd hR hP e X) := by
  have hf : trialFree R P d e (tableTrial R P d hd hR hP e X) =
      (fun p => X.val (some p.1) (some p.2)) := funext (trialFree_tableTrial R P d hd hR hP e X)
  intro i j
  rw [hf, DenseAffine.integerTable_recover R P X.val X.property.1 X.property.2]
  exact Int.natCast_nonneg _

theorem trialTable_tableTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (X : Table R P) :
    trialTable R P d e htotal (tableTrial R P d hd hR hP e X)
      (tableTrial_accepted R P d hd hR hP e X) = X := by
  apply Subtype.ext
  exact DenseAffine.naturalTable_unique R P _ (tableTrial_accepted R P d hd hR hP e X)
    X.val X.property.1 X.property.2 (fun i j => (trialFree_tableTrial R P d hd hR hP e X (i, j)).symm)

theorem tableTrial_trialTable (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j)
    (t : DenseTrial R P d q) (ht : TrialAccepted R P d e t) :
    tableTrial R P d hd hR hP e (trialTable R P d e htotal t ht) = t := by
  apply (trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8)).injective
  rw [tableTrial, Equiv.apply_symm_apply]
  funext p
  apply Fin.ext
  exact DenseAffine.naturalTable_free R P (trialFree R P d e t) p.1 p.2

def acceptedTrialEquiv (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) :
    {t : DenseTrial R P d q // TrialAccepted R P d e t} ≃ Table R P where
  toFun t := trialTable R P d e htotal t.val t.property
  invFun X := ⟨tableTrial R P d hd hR hP e X, tableTrial_accepted R P d hd hR hP e X⟩
  left_inv t := Subtype.ext (tableTrial_trialTable R P d hd hR hP e htotal t.val t.property)
  right_inv X := trialTable_tableTrial R P d hd hR hP e htotal X

end

end ContingencyTables.GridBoundary

end OAI
