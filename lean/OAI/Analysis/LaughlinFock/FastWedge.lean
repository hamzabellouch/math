import Mathlib
import OAI.Analysis.LaughlinFock.RationalWedge

namespace OAI

/-! Fast Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def occupationWeight {Q : ℕ} (A : Occupation Q) : ℕ := ∑ x ∈ A, x.val

 
def fastHighestTerm (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) : ℚ :=
  if x<y ∧ j<k ∧ (x.val+y.val-1)+j.val+k.val=D then
    rationalHighestTerm D r (x.val+y.val-1) j.val k.val x.val y.val *
      rationalWordVacuum [x,y,j,k] A
  else 0

def fastHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ j ∈ A, ∑ k ∈ A, ∑ x ∈ A, ∑ y ∈ A, fastHighestTerm D r A x y j k

theorem fourHighestShell_sum {M : Type*} [AddCommMonoid M] (D : ℕ)
    (f : FourUncoupled 24 → M) :
    (∑ b : FourHighestShell 24 D, f b.val) =
      ∑ p : Fin 47, ∑ jk : IncreasingPair 24,
        if p.val+jk.val.1.val+jk.val.2.val=D then f (p,jk) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun b : FourUncoupled 24 => b.1.val+b.2.val.1.val+b.2.val.2.val=D)) (by simp) f]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem highest_pair_weight_sum (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (xy jk : IncreasingPair 24) :
    (∑ p : Fin 47, if p.val+jk.val.1.val+jk.val.2.val=D then
      rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
        rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0) =
    fastHighestTerm D r A xy.val.1 xy.val.2 jk.val.1 jk.val.2 := by
  have hp : xy.val.1.val+xy.val.2.val-1 < 47 := by
    have hx := xy.val.1.isLt
    have hy := xy.val.2.isLt
    have hxy := xy.property
    change xy.val.1.val < xy.val.2.val at hxy
    omega
  let p : Fin 47 := ⟨xy.val.1.val+xy.val.2.val-1, hp⟩
  rw [Finset.sum_eq_single p]
  · simp [fastHighestTerm, xy.property, jk.property, p]
  · intro b _ hn
    have hd : xy.val.1.val+xy.val.2.val ≠ b.val+1 := by
      intro h
      apply hn
      apply Fin.ext
      dsimp [p]
      omega
    simp [rationalHighestTerm, hd]
  · simp

theorem rationalHighestEntry_expand (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    rationalHighestEntry D r A =
      ∑ j : Orbital 24, ∑ k : Orbital 24, ∑ x : Orbital 24, ∑ y : Orbital 24,
        fastHighestTerm D r A x y j k := by
  classical
  unfold rationalHighestEntry
  rw [fourHighestShell_sum D (fun b => ∑ xy : IncreasingPair 24,
    rationalHighestTerm D r b.1.val b.2.val.1.val b.2.val.2.val xy.val.1.val xy.val.2.val *
      rationalWordVacuum [xy.val.1,xy.val.2,b.2.val.1,b.2.val.2] A)]
  have he : (∑ p : Fin 47, ∑ jk : IncreasingPair 24,
      if p.val+jk.val.1.val+jk.val.2.val=D then
        ∑ xy : IncreasingPair 24,
          rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
            rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0) =
        ∑ jk : IncreasingPair 24, ∑ xy : IncreasingPair 24,
          fastHighestTerm D r A xy.val.1 xy.val.2 jk.val.1 jk.val.2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro jk _
    have hh (p : Fin 47) :
        (if p.val+jk.val.1.val+jk.val.2.val=D then
          ∑ xy : IncreasingPair 24,
            rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
              rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0) =
        ∑ xy : IncreasingPair 24, if p.val+jk.val.1.val+jk.val.2.val=D then
            rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
              rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0 := by
      split_ifs <;> simp
    simp_rw [hh]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun xy _ => highest_pair_weight_sum D r A xy jk)
  rw [he, increasingPair_sum 24 (fun j k => ∑ xy : IncreasingPair 24,
    fastHighestTerm D r A xy.val.1 xy.val.2 j k)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j<k
  · rw [ite_eq_left hjk, increasingPair_sum 24 (fun x y => fastHighestTerm D r A x y j k)]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : x<y
    · rw [ite_eq_left hxy]
    · simp [fastHighestTerm, hxy]
  · simp [fastHighestTerm, hjk]

theorem fastHighestTerm_support (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) (hn : fastHighestTerm D r A x y j k ≠ 0) :
    x ∈ A ∧ y ∈ A ∧ j ∈ A ∧ k ∈ A := by
  unfold fastHighestTerm at hn
  split_ifs at hn with h
  · have hn' : rationalWordVacuum [x,y,j,k] A ≠ 0 := fun hm => hn (by rw [hm, mul_zero])
    obtain ⟨_,hs⟩ := rationalWordVacuum_support _ _ hn'
    simp [← hs]
  · simp at hn

theorem rationalHighestEntry_fast (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    rationalHighestEntry D r A = fastHighestEntry D r A := by
  classical
  rw [rationalHighestEntry_expand]
  unfold fastHighestEntry
  symm
  let f : Orbital 24 × (Orbital 24 × (Orbital 24 × Orbital 24)) → ℚ := fun b =>
    fastHighestTerm D r A b.2.2.1 b.2.2.2 b.1 b.2.1
  have hs : (∑ b ∈ A ×ˢ (A ×ˢ (A ×ˢ A)), f b) =
      ∑ b ∈ Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)), f b := by
    apply Finset.sum_subset (by simp only [Finset.univ_product_univ]; exact Finset.subset_univ _)
    intro b _ hb
    by_contra hn
    obtain ⟨hx,hy,hj,hk⟩ := fastHighestTerm_support D r A b.2.2.1 b.2.2.2 b.1 b.2.1 hn
    exact hb (by simp [hx,hy,hj,hk])
  simpa only [Finset.sum_product] using hs

end LaughlinFock
end

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fastHighestTerm_weight (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) (hn : fastHighestTerm D r A x y j k ≠ 0) :
    occupationWeight A = D+1 := by
  unfold fastHighestTerm at hn
  split_ifs at hn with hh
  · have hn' : rationalWordVacuum [x,y,j,k] A ≠ 0 := fun hm => hn (by rw [hm, mul_zero])
    obtain ⟨hnd,hs⟩ := rationalWordVacuum_support _ _ hn'
    simp only [List.nodup_cons, List.mem_cons, not_or,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true] at hnd
    have hw : occupationWeight A = x.val+y.val+j.val+k.val := by
      unfold occupationWeight
      rw [← hs]
      simp [hnd.1.1, hnd.1.2.1, hnd.1.2.2, hnd.2.1.1, hnd.2.1.2, hnd.2.2,
        Finset.sum_insert, add_assoc]
    rw [hw]
    have hxy : x.val < y.val := hh.1
    omega
  · simp at hn

theorem rationalHighestEntry_weight (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (hw : occupationWeight A ≠ D+1) : rationalHighestEntry D r A = 0 := by
  rw [rationalHighestEntry_fast]
  unfold fastHighestEntry
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_contra hn
  exact hw (fastHighestTerm_weight D r A x y j k hn)

 
def highestFourOccupations (D : ℕ) : Finset (Occupation 24) :=
  ((Finset.univ : Finset (Orbital 24)).powersetCard 4).filter
    (fun A => occupationWeight A = D+1)

def fastFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A ∈ highestFourOccupations D,
    2 * fastHighestEntry D r A * fastHighestEntry D s A /
      (2^(2*D) * occupationFactorial A)

theorem rationalFourGram_fast (D : ℕ) : rationalFourGram D = fastFourGram D := by
  ext r s
  classical
  unfold rationalFourGram fastFourGram highestFourOccupations
  rw [← Finset.sum_subtype ((Finset.univ : Finset (Orbital 24)).powersetCard 4)
    (by intro A; simp [Finset.mem_powersetCard])
    (fun A => 2 * rationalHighestEntry D r A * rationalHighestEntry D s A /
      (2^(2*D) * occupationFactorial A))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs with h
  · rw [rationalHighestEntry_fast, rationalHighestEntry_fast]
  · simp [rationalHighestEntry_weight D r A h]

end LaughlinFock
end

end OAI
