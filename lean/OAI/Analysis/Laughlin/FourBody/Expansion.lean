import OAI.Analysis.Laughlin.FourBody.Assembly

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def sourceEntryThree (Q : ℕ) (e : ℕ × ℕ × ℤ) (x : Space Q) : Space Q :=
  ∑ i, (pairOrbitalUnit Q e.1 e.2.1 i : ℂ) • sourceThreeEnd Q i x

theorem sourceEntryThree_eq (Q : ℕ) (e : ℕ × ℕ × ℤ)
    (hp : e.1 < 2*Q-2+1) (hj : e.2.1 ≤ Q) (x : Space Q) :
    sourceEntryThree Q e x = annihilate ⟨e.2.1,by omega⟩ (sourcePairEnd Q e.1 x) := by
  rw [sourceEntryThree,pairOrbitalUnit_family_sum Q e.1 e.2.1 hp hj]
  rfl

theorem sourceRowLevel_entries (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ)) (x : Space Q) :
    sourceRowLevel Q t T entries x =
      (entries.map (fun e => if e.1+e.2.1=T then
        (sourceAlpha t e : ℂ) • sourceEntryThree Q e x else 0)).sum := by
  induction entries with
  | nil => simp [sourceRowLevel,threeBodyLevelVector]
  | cons e entries ih =>
    simp only [sourceRowLevel,threeBodyLevelVector,List.map_cons,List.sum_cons,
      Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    by_cases h : e.1+e.2.1=T
    · simp only [ite_eq_left h,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,sourceEntryThree,
        Finset.smul_sum,smul_smul]
    · simp [h]

theorem occupationInner_list_left {I : Type*} (Q : ℕ) (l : List I)
    (f : I → Space Q) (x : Space Q) :
    occupationInner Q (l.map f).sum x = (l.map (fun i => occupationInner Q (f i) x)).sum := by
  induction l with
  | nil => simp [occupationInner]
  | cons i l ih => simp only [List.map_cons,List.sum_cons,occupationInner_add_left,ih]

theorem occupationInner_list_right {I : Type*} (Q : ℕ) (l : List I)
    (f : I → Space Q) (x : Space Q) :
    occupationInner Q x (l.map f).sum = (l.map (fun i => occupationInner Q x (f i))).sum := by
  induction l with
  | nil => simp [occupationInner]
  | cons i l ih => simp only [List.map_cons,List.sum_cons,occupationInner_add_right,ih]

theorem finset_list_sum_swap {I J A : Type*} [AddCommMonoid A]
    (s : Finset I) (l : List J) (f : I → J → A) :
    (∑ i ∈ s, (l.map (f i)).sum) = (l.map (fun j => ∑ i ∈ s, f i j)).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem rowLevel_sum_select {A : Type*} [AddCommMonoid A] (t n : ℕ)
    (ht : t ≤ n) (hn : n < 16) (f : RowLevel t → A) :
    (∑ T : RowLevel t, if n=T.val.val then f T else 0) = f ⟨⟨n,hn⟩,ht⟩ := by
  classical
  have he (T : RowLevel t) : n=T.val.val ↔ T=⟨⟨n,hn⟩,ht⟩ := by
    constructor
    · intro h; exact Subtype.ext (Fin.ext h.symm)
    · intro h; subst T; rfl
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end Laughlin.Fock

end OAI
