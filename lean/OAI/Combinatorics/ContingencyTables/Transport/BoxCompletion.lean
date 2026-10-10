import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialSemantics

namespace OAI

/-! # Enumerating tables through their free entries -/

namespace ContingencyTables.BoxCompletion
open DenseAffine DensePrograms
open scoped BigOperators Classical
noncomputable section

abbrev Box (m n N : ℕ) := Fin (m*n) → Fin (N+1)

def freeValues {m n N : ℕ} (z : Box m n N) : Fin m×Fin n → ℕ :=
  fun ij => (z (finProdFinEquiv ij)).val

def decode {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : ∑ i,R i=∑ j,P j) (N : ℕ) (z : Box m n N) : Option (Table R P) :=
  if hz : ∀ i j,0 ≤ integerTable R P (freeValues z) i j then
    some ⟨naturalTable R P (freeValues z),naturalTable_rows R P _ hz,
      naturalTable_columns R P _ hz htotal⟩
  else none

def encode {m n N : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hN : (∑ i,R i)≤N) (X : Table R P) : Box m n N := fun k =>
  ⟨X.val (some (finProdFinEquiv.symm k).1) (some (finProdFinEquiv.symm k).2),
    Nat.lt_succ_of_le ((entry_le_total X.property _ _).trans hN)⟩

lemma freeValues_encode {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hN : (∑ i,R i)≤N) (X : Table R P) :
    freeValues (encode R P hN X)=fun ij => X.val (some ij.1) (some ij.2) := by
  funext ij
  simp only [freeValues,encode,Equiv.symm_apply_apply]

lemma decode_encode {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j)
    (hN : (∑ i,R i)≤N) (X : Table R P) :
    decode R P htotal N (encode R P hN X)=some X := by
  have he := integerTable_recover R P X.val X.property.1 X.property.2
  have hz : ∀ i j,0 ≤ integerTable R P (freeValues (encode R P hN X)) i j := by
    rw [freeValues_encode,he]
    exact fun _ _ => Int.natCast_nonneg _
  rw [decode,dite_eq_left hz]
  congr 1
  apply Subtype.ext
  funext i j
  simp only [naturalTable,freeValues_encode,he,Int.toNat_natCast]

/-- Each feasible table occurs at exactly one enumerated free vector. -/
theorem decode_eq_some {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j)
    (hN : (∑ i,R i)≤N) (z : Box m n N) (X : Table R P) :
    decode R P htotal N z=some X ↔ z=encode R P hN X := by
  constructor
  · intro h
    unfold decode at h
    split at h
    next hz =>
      have he := Option.some.inj h
      funext k
      apply Fin.ext
      have hv := congrArg (fun Y : Table R P =>
        Y.val (some (finProdFinEquiv.symm k).1) (some (finProdFinEquiv.symm k).2)) he
      simpa only [naturalTable_free,freeValues,Prod.mk.eta,
        Equiv.apply_symm_apply,encode] using hv
    next hz => cases h
  · rintro rfl
    exact decode_encode R P htotal hN X

lemma decode_elim_sum {A : Type*} [Fintype A] (y : Option A) (w : A → ℕ) :
    y.elim 0 w=∑ a,if y=some a then w a else 0 := by
  cases y <;> simp

/-- Summing over candidate completions counts each feasible table once,
and gives zero weight to every rejected completion. -/
theorem sum_decode {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j)
    (hN : (∑ i,R i)≤N) (w : Table R P → ℕ) :
    (∑ z : Box m n N,(decode R P htotal N z).elim 0 w)=∑ X,w X := by
  simp_rw [decode_elim_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  simp_rw [decode_eq_some R P htotal hN]
  simp

/-- The existing executable acceptance test returns the same optional
table as the finite enumeration used in the counting proof. -/
theorem acceptCompletion_eq {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) (z : Box m n N) :
    acceptCompletion ((marginCode R,marginCode P),
      matrixCode (fun i j => freeValues z (i,j)))=
      (decode R P htotal N z).map tableOutput := by
  by_cases hz : ∀ i j,0 ≤ integerTable R P (freeValues z) i j
  · have hv := (completionValid_code R P (fun i j => freeValues z (i,j))).mpr hz
    simp only [acceptCompletion,hv,ite_true,decode,dite_eq_left hz]
    rw [completedMatrix_code]
    rfl
  · have hv : completionValid ((marginCode R,marginCode P),
        matrixCode (fun i j => freeValues z (i,j)))≠true := by
      intro h
      exact hz ((completionValid_code R P _).mp h)
    simp only [acceptCompletion,hv,Bool.false_eq_true,ite_false,decode,dite_eq_right hz,
      Option.map_none]

end
end ContingencyTables.BoxCompletion

end OAI
