import OAI.Combinatorics.PolynomialVacuum.Algebra.FinalExchange
import OAI.Combinatorics.PolynomialVacuum.Algebra.QuotientRigidity

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

def rotationIndex (n j : ℕ) : ℕ := if j=0 then n else j-1

def natRotate {α : Type*} (n : ℕ) (X : ℕ → α) : ℕ → α := X ∘ rotationIndex n

@[simp] theorem natRotate_zero {α : Type*} (n : ℕ) (X : ℕ → α) : natRotate n X 0=X n := by simp [natRotate,rotationIndex]
@[simp] theorem natRotate_succ {α : Type*} (n j : ℕ) (X : ℕ → α) : natRotate n X (j+1)=X j := by simp [natRotate,rotationIndex]

theorem rotationIndex_injective (n : ℕ) : Function.Injective (fun j : Fin (n+1) => rotationIndex n j.val) := by
  intro a b h
  apply Fin.ext
  simp only [rotationIndex] at h
  split_ifs at h <;> omega

theorem natRotate_update {α : Type*} {n j : ℕ} (hj : j<n) (X : ℕ → α) (a : α) :
    natRotate n (Function.update X j a)=Function.update (natRotate n X) (j+1) a := by
  funext k
  simp only [natRotate,Function.comp_apply,rotationIndex,Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem natRotate_replacePair {n j : ℕ} (hj : j+1<n) (s : ℕ → Spin) (ab : Pair) :
    natRotate n (replacePair s j (j+1) ab)=replacePair (natRotate n s) (j+1) (j+2) ab := by
  simp only [replacePair,natRotate_update (by omega : j<n),natRotate_update hj,Nat.add_assoc,Nat.reduceAdd]

theorem natRotate_swapSite {α : Type*} {n j : ℕ} (hj : j+1<n) (X : ℕ → α) :
    natRotate n (swapSite j X)=swapSite (j+1) (natRotate n X) := by
  funext k
  cases k with
  | zero =>
    rw [natRotate_zero,swapSite_other (by omega : n≠j) (by omega : n≠j+1),
      swapSite_other (by omega : 0≠j+1) (by omega : 0≠j+1+1),natRotate_zero]
  | succ k =>
    rw [natRotate_succ]
    by_cases h0 : k=j
    · subst k
      rw [swapSite_left,swapSite_left,natRotate_succ]
    · by_cases h1 : k=j+1
      · subst k
        rw [swapSite_right,swapSite_right,natRotate_succ]
      · rw [swapSite_other h0 h1,swapSite_other (by omega : k+1≠j+1) (by omega : k+1≠j+1+1),natRotate_succ]

theorem natRotate_skipTwo {α : Type*} {n j : ℕ} (hj : j<n+1) (X : ℕ → α) :
    skipTwo (j+1) (natRotate (n+2) X)=natRotate n (skipTwo j X) := by
  funext k
  simp only [natRotate,Function.comp_apply,rotationIndex,skipTwo]
  split_ifs <;> try simp_all only [Nat.succ_sub_one]
  all_goals try (congr 1; omega)

noncomputable def rotateTensor (n : ℕ) (W : SpinTensor ℕ ℂ) : SpinTensor ℕ ℂ :=
  fun s => zeta ^ (-charge (s n)) * W (natRotate n s)

noncomputable def cyclicTransform (n : ℕ) (Ψ : NatSpectralTensor) : NatSpectralTensor :=
  fun X => rotateTensor n (Ψ (natRotate n X))

def NaturalCyclic (n : ℕ) (Ψ : NatSpectralTensor) : Prop := ∀ X, cyclicTransform n Ψ X=Ψ X

theorem siteR_rotateTensor {n j : ℕ} (hj : j+1<n) (x y : ℂ) (W : SpinTensor ℕ ℂ) :
    siteR j x y (rotateTensor n W)=rotateTensor n (siteR (j+1) x y W) := by
  funext s
  simp only [siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,rotateTensor,
    natRotate_succ,natRotate_replacePair hj,replacePair_other s (by omega : n≠j) (by omega : n≠j+1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  ring

theorem cyclicTransform_exchange {n : ℕ} (Ψ : NatSpectralTensor)
    (hex : LowerExchange Ψ (n+1)) : LowerExchange (cyclicTransform n Ψ) n := by
  intro j hj X
  rw [cyclicTransform,siteR_rotateTensor hj]
  have he := hex (j+1) (by omega) (natRotate n X)
  simp only [natRotate_succ] at he
  rw [he]
  funext s
  simp only [rotateTensor,cyclicTransform,Pi.smul_apply,smul_eq_mul,natRotate_swapSite hj]
  ring

noncomputable def rotatedPolynomial {n : ℕ} (Ψ : State (n+1)) (s : ℕ → Spin) : MvPolynomial ℕ ℂ :=
  rename (fun j : Fin (n+1) => rotationIndex n j.val) (Ψ (fun j => natRotate n s j.val))

noncomputable def cyclicDiscrepancy {n : ℕ} (Ψ : State (n+1)) : NatPolyTensor :=
  fun s => C (zeta ^ (-charge (s n))) * rotatedPolynomial Ψ s - coordinatePolynomial Ψ s

@[simp] theorem eval_rotatedPolynomial {n : ℕ} (Ψ : State (n+1)) (s : ℕ → Spin) (X : ℕ → ℂ) :
    eval X (rotatedPolynomial Ψ s)=liftState Ψ (natRotate n X) (natRotate n s) := by
  simp only [rotatedPolynomial,eval_rename,liftState,liftPolyTensor,natRotate,Function.comp_def]

theorem eval_cyclicDiscrepancy {n : ℕ} (Ψ : State (n+1)) (X : ℕ → ℂ) :
    evalNatPolyTensor (cyclicDiscrepancy Ψ) X=cyclicTransform n (liftState Ψ) X-liftState Ψ X := by
  funext s
  simp only [evalNatPolyTensor,cyclicDiscrepancy,map_sub,map_mul,eval_C,eval_rotatedPolynomial,
    eval_coordinatePolynomial,Pi.sub_apply,cyclicTransform,rotateTensor]

theorem cyclicDiscrepancy_exchange {n : ℕ} (Ψ : State (n+1))
    (hex : LowerExchange (liftState Ψ) (n+1)) :
    LowerExchange (evalNatPolyTensor (cyclicDiscrepancy Ψ)) n := by
  intro j hj X
  simp only [eval_cyclicDiscrepancy,map_sub,cyclicTransform_exchange _ hex j hj,
    hex j (by omega) X,smul_sub]

end PolynomialVacuumAlgebra

end OAI
