import OAI.Combinatorics.PolynomialVacuum.Cylinder.ClosedStack
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackWeight

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

noncomputable def cylinderBlockCharge (k : ℕ) (s : ZMod M → Spin) : ℤ :=
  ∑j : Fin k,charge (s (-(j.val : ZMod M)))

theorem stack_block_potential (c : StackCoordinates M H) (hc : ∀v,LocalIce (coordinatesCurrent c) v)
    (j : Fin (H+1)) (k : ℕ) :
    cylinderBlockCharge k (c.1 j)=potential (coordinatesCurrent c) (-(k : ZMod M),j.val)-
      potential (coordinatesCurrent c) (0,j.val) := by
  induction k with
  | zero => simp [cylinderBlockCharge]
  | succ k ih =>
    have he := (potential_gradient (coordinatesCurrent c) (allLocalIce_conserved _ hc)
      (-(k : ZMod M)) j.val).1
    change -charge (extendSpins c.1 (j.val : ℤ) (-(k : ZMod M)))=_ at he
    rw [extendSpins_nat] at he
    unfold cylinderBlockCharge at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one,neg_add_rev] at ih ⊢
    have hz : -(1 : ZMod M) + -(k : ZMod M)= -(k : ZMod M)-1 := by ring
    rw [hz]
    omega

theorem stack_prefix (c : StackCoordinates M H) (i : ZMod M) (L : ℕ) :
    finitePrefix (L : ℤ) (column (coordinatesCurrent c) i 2)=
      ∑j : Fin H,if j.val<L then charge (c.2.1 j i) else 0 := by
  have hs : (column (coordinatesCurrent c) i 2).support⊆Finset.Ico (0 : ℤ) H := by
    intro j hj
    have hn : (column (coordinatesCurrent c) i 2) j≠0 := Finsupp.mem_support_iff.mp hj
    by_contra hh
    have ho : ¬(0≤j ∧ j<(H : ℤ)) := by simpa using hh
    exact hn (by simp [column_apply,coordinatesCurrent,stackValues,extendSpins_outside _ j ho,charge])
  simp only [finitePrefix,Finsupp.liftAddHom_apply,Finsupp.sum]
  rw [Finset.sum_subset hs (by intro j _ hj; simp [Finsupp.notMem_support_iff.mp hj])]
  symm
  apply Finset.sum_bij (fun j _=>(j.val : ℤ))
  · intro j _; simp
  · intro j _ k _ he; exact Fin.ext (Int.ofNat_inj.mp he)
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ⟨⟨j.toNat,by omega⟩,Finset.mem_univ _,by dsimp; omega⟩
  · intro j _
    simp only [column_apply,coordinatesCurrent,stackCurrent_apply,stackValues]
    simp only [show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false,extendSpins_nat]
    by_cases hh : j.val<L <;> simp [hh]

theorem stack_potential (c : StackCoordinates M H) (i : ZMod M) (L : ℕ) :
    potential (coordinatesCurrent c) (i,L)= -(∑j : Fin H,if j.val<L then charge (c.2.1 j (i+1)) else 0) := by
  exact congrArg Neg.neg (stack_prefix c (i+1) L)

noncomputable def seamTwists (H L : ℕ) (j : Fin H) : ℂ := if j.val<L then zeta else zeta⁻¹
noncomputable def seamDecoration (L k : ℕ) (κ : ℂ) (j : Fin H) (s : ZMod M → Spin) : ℂ :=
  if j.val=L then (κ/zeta)^cylinderBlockCharge k s else 1

private theorem prod_zpow (κ : ℂ) (hκ : κ≠0) {J : Type*} [Fintype J] (f : J → ℤ) :
    (∏j,κ^f j)=κ^(∑j,f j) := by
  have hh (S : Finset J) : (∏j∈S,κ^f j)=κ^(∑j∈S,f j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih => simp [hj,ih,zpow_add₀ hκ]
  exact hh _

theorem stack_twist_product (c : StackCoordinates M H) (L : ℕ) :
    (∏j : Fin H,seamTwists H L j^charge (c.2.1 j 1))=
      zeta^(-potential (coordinatesCurrent c) (0,L))*
        (zeta⁻¹)^(potential (coordinatesCurrent c) (0,L)-topHom (coordinatesCurrent c)) := by
  have hz : zeta≠0 := by simp [zeta_eq_I]
  have he (j : Fin H) : seamTwists H L j^charge (c.2.1 j 1)=
      zeta^(if j.val<L then charge (c.2.1 j 1) else 0)*
      (zeta⁻¹)^(if j.val<L then 0 else charge (c.2.1 j 1)) := by
    unfold seamTwists
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.prod_mul_distrib,prod_zpow _ hz,prod_zpow _ (inv_ne_zero hz),stack_potential]
  have ht : topHom (coordinatesCurrent c)= -(∑j : Fin H,charge (c.2.1 j 1)) := by
    exact congrArg Neg.neg (stack_column_total c.1 c.2.1 c.2.2 1)
  rw [ht]
  simp only [zero_add,neg_neg]
  congr 2
  have hs : (∑j : Fin H,if j.val<L then charge (c.2.1 j 1) else 0)+
      (∑j : Fin H,if j.val<L then 0 else charge (c.2.1 j 1))=
      ∑j : Fin H,charge (c.2.1 j 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  omega

end PolynomialVacuumCylinder

end OAI
