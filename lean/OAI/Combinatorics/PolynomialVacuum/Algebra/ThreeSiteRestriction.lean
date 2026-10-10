import OAI.Combinatorics.PolynomialVacuum.Algebra.TrilinearRigidity
import OAI.Combinatorics.PolynomialVacuum.Algebra.QuotientExchange
import OAI.Combinatorics.PolynomialVacuum.Algebra.CupQuotientBounds

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

def setFirstThree {α : Type*} (u : ℕ → α) (a b c : α) : ℕ → α :=
  Function.update (Function.update (Function.update u 0 a) 1 b) 2 c
@[simp] theorem setFirstThree_0 {α : Type*} (u : ℕ → α) (a b c : α) : setFirstThree u a b c 0=a := by simp [setFirstThree]
@[simp] theorem setFirstThree_1 {α : Type*} (u : ℕ → α) (a b c : α) : setFirstThree u a b c 1=b := by simp [setFirstThree]
@[simp] theorem setFirstThree_2 {α : Type*} (u : ℕ → α) (a b c : α) : setFirstThree u a b c 2=c := by simp [setFirstThree]

theorem setFirstThree_restore {α : Type*} (u : ℕ → α) : setFirstThree u (u 0) (u 1) (u 2)=u := by
  funext j
  by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
    simp_all [setFirstThree]

theorem setFirstThree_update0 {α : Type*} (u : ℕ → α) (a b c d : α) :
    Function.update (setFirstThree u d b c) 0 a=setFirstThree u a b c := by
  funext j
  by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
    simp_all [setFirstThree,Function.update_apply]
theorem setFirstThree_update1 {α : Type*} (u : ℕ → α) (a b c d : α) :
    Function.update (setFirstThree u a d c) 1 b=setFirstThree u a b c := by
  funext j
  by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
    simp_all [setFirstThree,Function.update_apply]
theorem setFirstThree_update2 {α : Type*} (u : ℕ → α) (a b c d : α) :
    Function.update (setFirstThree u a b d) 2 c=setFirstThree u a b c := by
  simp [setFirstThree]

theorem setFirstThree_pair01 (s : ℕ → Spin) (a b c : Spin) (ab : Pair) :
    replacePair (setFirstThree s a b c) 0 1 ab=setFirstThree s ab.1 ab.2 c := by
  simp only [replacePair,setFirstThree_update0,setFirstThree_update1]
theorem setFirstThree_pair12 (s : ℕ → Spin) (a b c : Spin) (bc : Pair) :
    replacePair (setFirstThree s a b c) 1 2 bc=setFirstThree s a bc.1 bc.2 := by
  simp only [replacePair,setFirstThree_update1,setFirstThree_update2]

theorem setFirstThree_swap01 (Y : ℕ → ℂ) (x y z : ℂ) :
    swapSite 0 (setFirstThree Y x y z)=setFirstThree Y y x z := by
  funext j
  by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
    simp_all [swapSite,Equiv.swap_apply_def,setFirstThree]
theorem setFirstThree_swap12 (Y : ℕ → ℂ) (x y z : ℂ) :
    swapSite 1 (setFirstThree Y x y z)=setFirstThree Y x z y := by
  funext j
  by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
    simp_all [swapSite,Equiv.swap_apply_def,setFirstThree]

noncomputable def restrictThree (r : NatPolyTensor) (Y : ℕ → ℂ) (s : ℕ → Spin) : TripleSpectral :=
  fun x y z a b c => eval (setFirstThree Y x y z) (r (setFirstThree s a b c))

theorem restrictThree_exchange1 (r : NatPolyTensor) (Y : ℕ → ℂ) (s : ℕ → Spin)
    (he : ∀ X, siteR 0 (X 0) (X 1) (evalNatPolyTensor r X)=
      eigenOne (X 0) (X 1) • evalNatPolyTensor r (swapSite 0 X)) :
    ∀ z c, PairFunctionExchange (fun x y ab => restrictThree r Y s x y z ab.1 ab.2 c) := by
  intro z c x y
  funext ab
  have hh := congrFun (he (setFirstThree Y x y z)) (setFirstThree s ab.1 ab.2 c)
  simpa only [siteR,Nat.reduceAdd,Prod.mk.eta,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,
    setFirstThree_0,setFirstThree_1,setFirstThree_pair01,setFirstThree_swap01,
    Matrix.mulVec,dotProduct,evalNatPolyTensor,restrictThree,Pi.smul_apply,smul_eq_mul] using hh

theorem restrictThree_exchange2 (r : NatPolyTensor) (Y : ℕ → ℂ) (s : ℕ → Spin)
    (he : ∀ X, siteR 1 (X 1) (X 2) (evalNatPolyTensor r X)=
      eigenOne (X 1) (X 2) • evalNatPolyTensor r (swapSite 1 X)) :
    ∀ x a, PairFunctionExchange (fun y z bc => restrictThree r Y s x y z a bc.1 bc.2) := by
  intro x a y z
  funext bc
  have hh := congrFun (he (setFirstThree Y x y z)) (setFirstThree s a bc.1 bc.2)
  simpa only [siteR,Nat.reduceAdd,Prod.mk.eta,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,
    setFirstThree_1,setFirstThree_2,setFirstThree_pair12,setFirstThree_swap12,
    Matrix.mulVec,dotProduct,evalNatPolyTensor,restrictThree,Pi.smul_apply,smul_eq_mul] using hh

end PolynomialVacuumAlgebra

end OAI
