import OAI.Combinatorics.PolynomialVacuum.Cylinder.BandProduct
import OAI.Combinatorics.PolynomialVacuum.Pairing.StackExpansion

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

theorem stack_column_total (v : Fin (H+1) → ZMod M → Spin) (a k : Fin H → ZMod M → Spin)
    (i : ZMod M) : columnTotal (stackCurrent v a k) i=∑j : Fin H,charge (a j i) := by
  have hs : (column (stackCurrent v a k) i 2).support⊆Finset.Ico (0 : ℤ) H := by
    intro j hj
    have hn : (column (stackCurrent v a k) i 2) j≠0 := Finsupp.mem_support_iff.mp hj
    by_contra hh
    have ho : ¬(0≤j ∧ j<(H : ℤ)) := by simpa using hh
    exact hn (by simp [column_apply,stackValues,extendSpins_outside a j ho,charge])
  unfold columnTotal Finsupp.sum
  rw [Finset.sum_subset hs (by intro j _ hj; exact Finsupp.notMem_support_iff.mp hj)]
  symm
  apply Finset.sum_bij (fun j _ => (j.val : ℤ))
  · intro j _; simp
  · intro j _ l _ he; exact Fin.ext (Int.ofNat_inj.mp he)
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ⟨⟨j.toNat,by omega⟩,Finset.mem_univ _,by dsimp; omega⟩
  · intro j _
    simp [column_apply,stackValues,extendSpins_nat]

theorem stack_domain_weight (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) :
    domainWeight (bandSites M H) (stackCurrent v a k)=
      (∏j : Fin H,zeta^charge (a j 1))*stackLocalWeight v a k := by
  have hz : ∀E : Finset (Fin H),zeta^(∑j∈E,charge (a j 1))=∏j∈E,zeta^charge (a j 1) := by
    intro E
    induction E using Finset.induction_on with
    | empty => simp
    | @insert j E hj ih =>
      rw [Finset.sum_insert hj,Finset.prod_insert hj,zpow_add₀ (by simp [zeta_eq_I]),ih]
  rw [domainWeight,stack_local_domain,stack_column_total,hz]
  exact mul_comm _ _

end PolynomialVacuumCylinder
namespace PolynomialVacuumAlgebra
open PolynomialVacuumCylinder

theorem physicalStackWeight_domain (N H : ℕ) (inp : Fin (N+1) → Spin)
    (r a k : Fin H → (Fin (N+1) → Spin)) :
    physicalStackWeight N H zeta inp r a k=
      domainWeight (bandSites (N+1) H)
        (stackCurrent (stackVertical N H inp r) (stackInternal N H a) (stackInternal N H k)) :=
  (stack_domain_weight _ _ _).symm
end PolynomialVacuumAlgebra

end OAI
