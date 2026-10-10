import OAI.Combinatorics.PolynomialVacuum.Pairing.RowPeriodic
import OAI.Combinatorics.PolynomialVacuum.Cylinder.BoundaryDecomposition
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StripArcs

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

noncomputable def extendSpins (f : Fin H → ZMod M → Spin) (j : ℤ) : ZMod M → Spin :=
  if h : 0≤j ∧ j<(H : ℤ) then f ⟨j.toNat,by omega⟩ else fun _ => Spin.zero

omit [NeZero M] in
@[simp] theorem extendSpins_nat [NeZero M] (f : Fin H → ZMod M → Spin) (j : Fin H) :
    extendSpins f (j.val : ℤ)=f j := by
  simp only [extendSpins]
  rw [dite_eq_left (by constructor <;> omega)]
  congr

omit [NeZero M] in
@[simp] theorem extendSpins_outside [NeZero M] (f : Fin H → ZMod M → Spin) (j : ℤ)
    (hj : ¬(0≤j ∧ j<(H : ℤ))) : extendSpins f j=fun _ => Spin.zero := by
  simp [extendSpins,hj]

noncomputable def stackValues (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (e : Edge M) : ℤ :=
  if e.2=0 then -charge (extendSpins v e.1.2 e.1.1) else
  if e.2=1 then -charge (extendSpins k e.1.2 e.1.1) else
    charge (extendSpins a e.1.2 e.1.1)

noncomputable def stackEdges (M H : ℕ) [NeZero M] : Finset (Edge M) :=
  (Finset.univ ×ˢ Finset.Icc (0 : ℤ) H) ×ˢ Finset.univ

noncomputable def stackCurrent (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) : Edge M →₀ ℤ :=
  Finsupp.onFinset (stackEdges M H) (stackValues v a k) (by
    intro e he
    have hj : 0≤e.1.2 ∧ e.1.2≤(H : ℤ) := by
      by_contra hh
      have h0 : ¬(0≤e.1.2 ∧ e.1.2<((H+1 : ℕ) : ℤ)) := by omega
      have h1 : ¬(0≤e.1.2 ∧ e.1.2<(H : ℤ)) := by omega
      exact he (by simp [stackValues,extendSpins_outside _ _ h0,extendSpins_outside _ _ h1,charge])
    simpa [stackEdges] using hj)

@[simp] theorem stackCurrent_apply (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (e : Edge M) :
    stackCurrent v a k e=stackValues v a k e := rfl

theorem stack_up (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (j : Fin H) (i : ZMod M) (s : Fin 3) :
    orientedFlow (stackCurrent v a k) (.up i j.val,s)=
      arrowTriple (-charge (v j.castSucc i)) (-charge (k j i)) (charge (a j i)) s := by
  rw [orientedFlow_up]
  have hv : extendSpins v (j.val : ℤ)=v j.castSucc := extendSpins_nat v j.castSucc
  simp [stackValues,hv,arrowTriple]

theorem stack_down (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (j : Fin H) (i : ZMod M) (s : Fin 3) :
    orientedFlow (stackCurrent v a k) (.down i j.val,s)=
      arrowTriple (charge (v j.succ i)) (charge (k j i)) (-charge (a j (i+1))) s := by
  rw [orientedFlow_down]
  have hv : extendSpins v ((j.val : ℤ)+1)=v j.succ := by
    simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one] using extendSpins_nat v j.succ
  fin_cases s <;> simp [stackValues,hv,arrowTriple,edgeOf]

theorem stack_up_ice (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (j : Fin H) (i : ZMod M) :
    LocalIce (stackCurrent v a k) (.up i j.val) ↔
      charge (a j i)=charge (k j i)+charge (v j.castSucc i) := by
  unfold LocalIce
  simp_rw [stack_up]
  exact up_ice _ _ _

theorem stack_down_ice (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (j : Fin H) (i : ZMod M) :
    LocalIce (stackCurrent v a k) (.down i j.val) ↔
      charge (a j (i+1))=charge (k j i)+charge (v j.succ i) := by
  unfold LocalIce
  simp_rw [stack_down]
  exact down_ice _ _ _

theorem stack_row_weight (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (j : Fin H) :
    (∏ i : ZMod M,honeycombPiece (v j.succ i,a j i) (a j (i+1),v j.castSucc i) (k j i))=
      ∏ i : ZMod M,localCurrentWeight (stackCurrent v a k) (.up i j.val)*
        localCurrentWeight (stackCurrent v a k) (.down i j.val) := by
  rw [layer_weight_telescopes]
  apply Finset.prod_congr rfl
  intro i _
  simp only [localCurrentWeight,stack_up,stack_down,layer_up,layer_down]

end PolynomialVacuumCylinder

end OAI
