import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairFlagScope
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryOccurrenceRows HistorySymbolicScope
open HistoryRepeatedRenaming ClearedCoefficientFlags MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def rootFreeLevel (h k : History l) (j : PairKey h k) : ℕ :=
  match j.val with
  | .inl _ => 0
  | .inr _ => l+1

theorem left_rootFreeLevel (h k : History l) (j : Key h) :
    rootFreeLevel h k (leftMap h k j)=HistoryCoefficientBounds.rootFreeLevel h j := by
  rcases j with b | j <;> rfl

theorem right_rootFreeLevel (h k : History l) (j : Key k) :
    rootFreeLevel h k (rightMap h k j)=HistoryCoefficientBounds.rootFreeLevel k j := by
  rcases j with b | j <;> rfl

theorem row_rootFree (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) :
    Above (rootFreeLevel h k) (level h k i) (row h k hs ks i).1 ∧
    Above (rootFreeLevel h k) (level h k i) (row h k hs ks i).2 := by
  have hh := rows_above h hs _ _ (HistoryCoefficientBounds.rootFreeLevel h)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs false)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs true)
  have hk := rows_above k ks _ _ (HistoryCoefficientBounds.rootFreeLevel k)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove k ks false)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove k ks true)
  rcases i with i | i
  · exact ⟨(above_rename _ (leftMap h k) _ _ (left_rootFreeLevel h k) _).mpr (hh i).1,
      (above_rename _ (leftMap h k) _ _ (left_rootFreeLevel h k) _).mpr (hh i).2⟩
  · exact ⟨(above_rename _ (rightMap h k) _ _ (right_rootFreeLevel h k) _).mpr (hk i).1,
      (above_rename _ (rightMap h k) _ _ (right_rootFreeLevel h k) _).mpr (hk i).2⟩

def EarlierSmall (h k : History l) (t : ℕ) (P : MvPolynomial (PairKey h k) ℤ) : Prop :=
  ∀ j ∈ P.vars, (∃ a : ℕ × ℤ, j.val=Sum.inr a) ∧ t<pairLevel h k j

theorem earlierSmall_of_above (h k : History l) (t : ℕ) (P : MvPolynomial (PairKey h k) ℤ)
    (hp : PolynomialAbove (pairLevel h k) t P)
    (hf : PolynomialAbove (rootFreeLevel h k) t P) : EarlierSmall h k t P := by
  intro j hj
  refine ⟨?_,hp j hj⟩
  have hh := hf j hj
  rcases he : j.val with b | a
  · simp only [rootFreeLevel,he] at hh
    omega
  · exact ⟨a,rfl⟩

theorem flags_earlierSmall (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) :
    EarlierSmall h k (level h k i) (leftFlag h k hs ks i) ∧
    EarlierSmall h k (level h k i) (rightFlag h k hs ks i) := by
  have hp := flags_above h k hs ks i
  have hr := row_rootFree h k hs ks i
  have hf := coefficients_above _ _ _ _ hr.1 hr.2
  exact ⟨earlierSmall_of_above h k _ _ hp.1 hf.1,
    earlierSmall_of_above h k _ _ hp.2 hf.2.1⟩

theorem minor_earlierSmall (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i j : Occurrences h k) (hlevel : level h k i=level h k j) :
    EarlierSmall h k (level h k i) (minorFlag h k hs ks i j) := by
  have hi := row_rootFree h k hs ks i
  have hj := row_rootFree h k hs ks j
  rw [← hlevel] at hj
  exact earlierSmall_of_above h k _ _ (minorFlag_above h k hs ks i j hlevel)
    (minor_above _ _ _ _ _ _ hi.1 hi.2 hj.1 hj.2)

theorem eval_congr (h k : History l) (t : ℕ) (P : MvPolynomial (PairKey h k) ℤ)
    (hP : EarlierSmall h k t P) {R : Type*} [CommRing R] (x y : PairKey h k → R)
    (hxy : ∀ j, (∃ a : ℕ × ℤ, j.val=Sum.inr a) → t<pairLevel h k j → x j=y j) :
    eval₂ (Int.castRingHom R) x P=eval₂ (Int.castRingHom R) y P := by
  apply eval₂Hom_congr' rfl _ rfl
  intro j hj _
  exact hxy j (hP j hj).1 (hP j hj).2

theorem exists_earlierSmall_polynomial (h k : History l) (t : ℕ)
    (P : MvPolynomial (PairKey h k) ℤ) (hP : EarlierSmall h k t P) :
    ∃ Q : MvPolynomial {j : PairKey h k //
      (∃ a : ℕ × ℤ, j.val=Sum.inr a) ∧ t<pairLevel h k j} ℤ,
      rename Subtype.val Q=P := by
  apply exists_rename_eq_of_vars_subset_range P Subtype.val Subtype.val_injective
  intro j hj
  exact ⟨⟨j,hP j hj⟩,rfl⟩

end Ostmann.Arithmetic.HistoryPairFlagScope

end

end OAI
