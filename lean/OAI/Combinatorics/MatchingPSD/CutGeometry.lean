import OAI.Combinatorics.MatchingPSD.AdmissiblePoints

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev GlobalVertices (s q : ℕ) :=
  (Fin (2*s+1) ⊕ Fin (2*s+1)) ⊕ (Fin q × (Fin s × Bool))

def localCutColor (b : Bool) : Fin 3 → Bool := ![true,false,b]
def globalCutColor {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} (y : I → Bool) : (A ⊕ B) ⊕ (I × C) → Bool :=
  Sum.elim (Sum.elim (fun _ => true) (fun _ => false)) (fun v => y v.1)

lemma tableCoordinate_localcut {V : Type u_5} [Fintype V] (z : V → Fin 3)
    (M : Pairing V) (b : Bool) :
    tableCoordinate (localCutColor b ∘ z) (true,false) M =
      crossVector z M 0 + crossVector z M (if b then 2 else 1) := by
  cases b
  · change _ = tableCoordinate z (0,1) M + tableCoordinate z (0,2) M
    simp only [tableCoordinate, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases (show z v=0 ∨ z v=1 ∨ z v=2 by omega) with hv | hv | hv <;>
      rcases (show z (M.1 v)=0 ∨ z (M.1 v)=1 ∨ z (M.1 v)=2 by omega) with hw | hw | hw <;>
      simp [Function.comp_apply, hv, hw, localCutColor]
  · change _ = tableCoordinate z (0,1) M + tableCoordinate z (1,2) M
    rw [tableCoordinate_symm z 1 2]
    simp only [tableCoordinate, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases (show z v=0 ∨ z v=1 ∨ z v=2 by omega) with hv | hv | hv <;>
      rcases (show z (M.1 v)=0 ∨ z (M.1 v)=1 ∨ z (M.1 v)=2 by omega) with hw | hw | hw <;>
      simp [Function.comp_apply, hv, hw, localCutColor]

lemma tableCoordinate_cellwise_cut {I : Type u_6} {C : Type u_7} [Fintype I] [Fintype C]
    (y : I → Bool) (N : I → Pairing C) :
    tableCoordinate (fun v : I × C => y v.1) (true,false) (Pairing.cellwise N) = 0 := by
  apply (tableCoordinate_eq_zero_iff _ _ _).mpr
  rintro ⟨j,c⟩ ⟨h1,h2⟩
  have he : (true : Bool) = false := h1.symm.trans h2
  cases he

lemma localSplit_cut {A : Type u_8} {B : Type u_9} {C : Type u_10} {I : Type u_11} [DecidableEq I]
    (y : I → Bool) (i : I) :
    globalCutColor (A := A) (B := B) (C := C) y ∘ localSplitEquiv i =
      Sum.elim (localCutColor (y i) ∘ threeColor)
        (fun v : {j : I // j ≠ i} × C => y v.1.1) := by
  funext v
  rcases v with (a | c) | ⟨j,c⟩
  · cases a <;> rfl
  · rfl
  · rfl

lemma extendLocal_cut {A : Type u_12} {B : Type u_13} {C : Type u_14} {I : Type u_15} [Fintype A] [Fintype B] [Fintype C]
    [Fintype I] [DecidableEq I] (y : I → Bool) (i : I)
    (M : Pairing ((A ⊕ B) ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    tableCoordinate (globalCutColor y) (true,false) (extendLocal i M N) =
      crossVector threeColor M 0 + crossVector threeColor M (if y i then 2 else 1) := by
  rw [extendLocal, tableCoordinate_transport, localSplit_cut, tableCoordinate_sum,
    tableCoordinate_cellwise_cut (fun j : {j : I // j ≠ i} => y j.1),
    add_zero, tableCoordinate_localcut]

lemma globalCutColor_card (s q : ℕ) (y : Fin q → Bool) :
    Fintype.card {v : GlobalVertices s q // globalCutColor y v = true} =
      2*s+1 + Fintype.card {i : Fin q // y i = true} * (2*s) := by
  classical
  have hc (V : Type) [Fintype V] (f : V → Bool) :
      Fintype.card {v // f v = true} = histogram f true := by
    simp only [Fintype.card_subtype, histogram]
  rw [hc, hc]
  apply Nat.cast_injective (R := ℝ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    histogram_cast_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, globalCutColor,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, mul_zero, add_zero, Finset.sum_add_distrib, Finset.sum_mul,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : y i = true <;> simp [h]
  ring

lemma globalCutColor_odd (s q : ℕ) (y : Fin q → Bool) :
    Odd (Fintype.card {v : GlobalVertices s q // globalCutColor y v = true}) := by
  rw [globalCutColor_card]
  exact ⟨s+Fintype.card {i : Fin q // y i = true}*s, by ring⟩

lemma globalVertices_card (s q : ℕ) :
    Fintype.card (GlobalVertices s q) = 2*s*(q+2)+2 := by
  simp only [GlobalVertices, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ring

end MatchingSmoothing

end OAI
