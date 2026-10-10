import OAI.Combinatorics.MatchingPSD.MatchingFibers

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ThreeCellGeometry
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C]

def abColor : A ⊕ B → Fin 3 := Sum.elim (fun _ => 0) (fun _ => 1)
def threeColor : (A ⊕ B) ⊕ C → Fin 3 := Sum.elim abColor (fun _ => 2)
noncomputable def crossVector {V : Type u_4} [Fintype V] (z : V → Fin 3)
    (M : Pairing V) : Fin 3 → ℝ := fun i => crossCoordinate z i M

lemma crossVector_sum (M : Pairing (A ⊕ B)) (N : Pairing C) :
    crossVector threeColor (Pairing.sum M N) = ![tableCoordinate abColor (0,1) M,0,0] := by
  have h02 : tableCoordinate (abColor : A ⊕ B → Fin 3) (0,2) M = 0 := by
    apply (tableCoordinate_eq_zero_iff _ _ _).mpr
    intro v hv
    have hh := hv.2
    cases he : M.1 v <;> simp [he, abColor] at hh
  have h12 : tableCoordinate (abColor : A ⊕ B → Fin 3) (1,2) M = 0 := by
    apply (tableCoordinate_eq_zero_iff _ _ _).mpr
    intro v hv
    have hh := hv.2
    cases he : M.1 v <;> simp [he, abColor] at hh
  funext i
  fin_cases i <;>
    simp [crossVector, crossCoordinate, crossPair, threeColor,
      tableCoordinate_sum, tableCoordinate_constant, h02, h12]

lemma threeColor_closed (M : Pairing ((A ⊕ B) ⊕ C))
    (h1 : crossCoordinate threeColor 1 M = 0) (h2 : crossCoordinate threeColor 2 M = 0) :
    ∀ a : A ⊕ B, ∃ a' : A ⊕ B, M.1 (.inl a) = .inl a' := by
  have h1' := (tableCoordinate_eq_zero_iff _ _ _).mp h1
  have h2' := (tableCoordinate_eq_zero_iff _ _ _).mp h2
  intro a
  cases hm : M.1 (.inl a) with
  | inl a' => exact ⟨a',rfl⟩
  | inr c =>
    cases a with
    | inl a => exact False.elim (h1' (.inl (.inl a)) ⟨rfl, by rw [hm]; rfl⟩)
    | inr b => exact False.elim (h2' (.inl (.inr b)) ⟨rfl, by rw [hm]; rfl⟩)

noncomputable def starFiberEquiv (x : ℝ) :
    {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x} × Pairing C ≃
      {M : Pairing ((A ⊕ B) ⊕ C) // crossVector threeColor M = ![x,0,0]} :=
  Pairing.sumFiberEquiv _ _
    (fun M N => by rw [crossVector_sum]; simp)
    (fun M hM => threeColor_closed M
      (by have := congrFun hM 1; exact this)
      (by have := congrFun hM 2; exact this))

end ThreeCellGeometry

section GlobalExtension
variable {D : Type u_5} {C : Type u_6} {I : Type u_7} [DecidableEq I]

def insertCellEquiv (i : I) : C ⊕ ({j : I // j ≠ i} × C) ≃ I × C where
  toFun v := v.elim (fun c => (i,c)) (fun jc => (jc.1.1,jc.2))
  invFun v := if h : v.1 = i then .inl v.2 else .inr (⟨v.1,h⟩,v.2)
  left_inv v := by
    cases v with
    | inl c => simp
    | inr jc => simp [jc.1.2]
  right_inv v := by
    rcases v with ⟨j,c⟩
    by_cases h : j = i <;> simp_all

def localSplitEquiv (i : I) : (D ⊕ C) ⊕ ({j : I // j ≠ i} × C) ≃ D ⊕ (I × C) :=
  (Equiv.sumAssoc D C _).trans (Equiv.sumCongr (Equiv.refl D) (insertCellEquiv i))

def extendLocal (i : I) (M : Pairing (D ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    Pairing (D ⊕ (I × C)) :=
  Pairing.transport (localSplitEquiv i) (Pairing.sum M (Pairing.cellwise N))

def liftLocal (i : I) (p : Equiv.Perm (D ⊕ C)) : Equiv.Perm (D ⊕ (I × C)) :=
  (localSplitEquiv i).symm.trans
    ((Equiv.sumCongr p (Equiv.refl _)).trans (localSplitEquiv i))

lemma extendLocal_relabel (i : I) (p : Equiv.Perm (D ⊕ C))
    (M : Pairing (D ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    extendLocal i (Pairing.relabel p M) N = Pairing.relabel (liftLocal i p) (extendLocal i M N) := by
  rw [extendLocal, Pairing.sum_relabel_left, Pairing.transport_relabel]
  rfl

lemma localSplit_inl (i : I) (d : D) :
    localSplitEquiv (C := C) i (.inl (.inl d)) = .inl d := rfl
lemma localSplit_cell (i : I) (c : C) :
    localSplitEquiv (D := D) i (.inl (.inr c)) = .inr (i,c) := rfl
lemma localSplit_outside (i : I) (v : {j : I // j ≠ i} × C) :
    localSplitEquiv (D := D) i (.inr v) = .inr (v.1.1,v.2) := rfl

lemma extendLocal_sum (i : I) (M : Pairing D) (N : I → Pairing C) :
    extendLocal i (Pairing.sum M (N i)) (fun j => N j.1) =
      Pairing.sum M (Pairing.cellwise N) := by
  apply Pairing.ext
  intro v
  obtain ⟨v,rfl⟩ := (localSplitEquiv (D := D) (C := C) i).surjective v
  simp only [extendLocal, Pairing.transport_apply, Equiv.symm_apply_apply]
  cases v with
  | inl v =>
    cases v with
    | inl d => rfl
    | inr c => rfl
  | inr jc => rfl

end GlobalExtension
end MatchingSmoothing

end OAI
