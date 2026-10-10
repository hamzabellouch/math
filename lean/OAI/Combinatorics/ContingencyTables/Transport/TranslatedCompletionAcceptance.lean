import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletions
import OAI.Combinatorics.ContingencyTables.Sampling.Padding

namespace OAI

/-! # Acceptance probability of the literal reference-row translation -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def referencePosition : Option I ⊕ J → Option I × Option J :=
  Sum.elim (fun i => (i,none)) (fun j => (none,some j))

abbrev ReferenceGood (R : Option I → ℕ) (P : Option J → ℕ) (t : ℕ) :=
  {X : Table R P // ¬∃ k : Option I ⊕ J,
    X.val (referencePosition k).1 (referencePosition k).2 < t}

lemma reference_good_nonnegative
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (hzero : ∀ i j,D (some i) (some j)=0) (t : ℕ)
    (hbound : ∀ i j,|D i j| ≤ (t:ℤ)) (X : ReferenceGood R P t) :
    ∀ i j,0 ≤ (X.val.val i j:ℤ)+D i j := by
  have hcell (k : Option I ⊕ J) :
      0 ≤ (X.val.val (referencePosition k).1 (referencePosition k).2:ℤ)+
        D (referencePosition k).1 (referencePosition k).2 := by
    have hn : t ≤ X.val.val (referencePosition k).1 (referencePosition k).2 :=
      Nat.le_of_not_gt (fun h => X.property ⟨k,h⟩)
    have hn' : (t:ℤ) ≤ X.val.val (referencePosition k).1 (referencePosition k).2 := by exact_mod_cast hn
    have hl := (abs_le.mp (hbound (referencePosition k).1 (referencePosition k).2)).1
    omega
  intro i j
  cases j with
  | none => exact hcell (.inl i)
  | some j =>
    cases i with
    | none => exact hcell (.inr j)
    | some i => rw [hzero i j,add_zero]; positivity

lemma reference_good_card_le
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (hzero : ∀ i j,D (some i) (some j)=0) (t : ℕ)
    (hbound : ∀ i j,|D i j| ≤ (t:ℤ)) :
    Fintype.card (ReferenceGood R P t) ≤ Fintype.card (Accepted R P D) := by
  let embed : ReferenceGood R P t → Accepted R P D :=
    fun X => ⟨X.val,reference_good_nonnegative R P D hzero t hbound X⟩
  apply Fintype.card_le_of_injective embed
  intro X Y h
  apply Subtype.ext
  exact congrArg (fun Z : Accepted R P D => Z.val) h

lemma reference_cell_fraction
    (R : Option I → ℕ) (P : Option J → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀) (k : Option I ⊕ J) :
    (Fintype.card {X : Table R P // X.val (referencePosition k).1 (referencePosition k).2 < t}:ℝ)/
      Fintype.card (Table R P) ≤ 4*t*(d:ℝ)^3/a₀ := by
  simpa only [Fintype.card_eq_nat_card] using
    small_entry_probability htotal (referencePosition k).1 (referencePosition k).2
      a₀ d t hd hrows hcols (hrow _) (hcol _) ha₀ ht

lemma reference_good_fraction
    (R : Option I → ℕ) (P : Option J → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀) :
    1-(Fintype.card I+Fintype.card J+1:ℕ)*(4*t*(d:ℝ)^3/a₀) ≤
      (Fintype.card (ReferenceGood R P t):ℝ)/Fintype.card (Table R P) := by
  have hcard : (0:ℝ) < Fintype.card (Table R P) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty R P htotal)
  have hfrac := fraction_not_exists
    (fun (k : Option I ⊕ J) (X : Table R P) =>
      X.val (referencePosition k).1 (referencePosition k).2 < t)
    (4*t*(d:ℝ)^3/a₀) hcard (fun k => by
      simpa only [Fintype.card_eq_nat_card] using reference_cell_fraction R P htotal a₀ d t hd hrows hcols hrow hcol ha₀ ht k)
  have hcK : Fintype.card (Option I ⊕ J)=Fintype.card I+Fintype.card J+1 := by
    rw [Fintype.card_sum,Fintype.card_option]
    omega
  rw [hcK] at hfrac
  simpa only [Fintype.card_eq_nat_card] using hfrac

/-- The reference row and reference column contain only |I|+|J|+1
possibly changed entries. No completion outside those entries can reject. -/
theorem reference_acceptance
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (hzero : ∀ i j,D (some i) (some j)=0)
    (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀)
    (hbound : ∀ i j,|D i j| ≤ (t:ℤ)) :
    1-(Fintype.card I+Fintype.card J+1:ℕ)*(4*t*(d:ℝ)^3/a₀) ≤
      (Fintype.card (Accepted R P D):ℝ)/Fintype.card (Table R P) := by
  have hcount : (Fintype.card (ReferenceGood R P t):ℝ) ≤ Fintype.card (Accepted R P D) := by
    exact_mod_cast reference_good_card_le R P D hzero t hbound
  exact (reference_good_fraction R P htotal a₀ d t hd hrows hcols hrow hcol ha₀ ht).trans
    (div_le_div_of_nonneg_right hcount (Nat.cast_nonneg _))

/-- Applying the previous estimate to the actual signed star only needs
bounds on the changes to its row and column margins. -/
theorem star_acceptance
    (R : Option I → ℕ) (P : Option J → ℕ)
    (δR : Option I → ℤ) (δP : Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (a₀ d M t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hrow : ∀ i,a₀ ≤ R i) (hcol : ∀ j,a₀ ≤ P j)
    (ha₀ : 4*d ≤ a₀) (ht : 2*t ≤ a₀)
    (hR : ∀ i,|δR i| ≤ (M:ℤ)) (hP : ∀ j,|δP j| ≤ (M:ℤ))
    (hscale : M*(Fintype.card J+1) ≤ t) :
    1-(Fintype.card I+Fintype.card J+1:ℕ)*(4*t*(d:ℝ)^3/a₀) ≤
      (Fintype.card (Accepted R P (star δR δP)):ℝ)/Fintype.card (Table R P) := by
  apply reference_acceptance R P (star δR δP) htotal (fun _ _ => rfl)
    a₀ d t hd hrows hcols hrow hcol ha₀ ht
  intro i j
  exact (star_abs_le δR δP M (by positivity) hR hP i j).trans (by exact_mod_cast hscale)

end ContingencyTables.CompletionTranslation

end OAI
