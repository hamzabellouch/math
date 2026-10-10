import Mathlib
import OAI.Combinatorics.UniformKServer.FinitePiLaw

namespace OAI

/-! Fubini for an arbitrary function on the same finite independent tape.
The one-coordinate ledger may depend on every other coordinate. -/
noncomputable section
namespace UniformKServer.FiniteProbability

section
open Finset
open scoped Classical
variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]
local instance restDecEq (i : I) : DecidableEq {j : I // j ≠ i} :=
  fun a b => Classical.propDecidable (a=b)

theorem Law.expect_pi_split (P : ∀ i, Law (A i)) (i : I) (f : (∀ i, A i)→ℝ) :
    (Law.pi P).expect f =
      (Law.pi (fun j : {j // j≠i} => P j.val)).expect
        (fun b => (P i).expect (fun a => f ((Equiv.piSplitAt i A).symm (a,b)))) := by
  let e := Equiv.piSplitAt i A
  have hweight (x : A i × (∀ j : {j // j ≠ i}, A j.val)) :
      (Law.pi P).weight (e.symm x) = (P i).weight x.1 *
        ∏ j : {j // j ≠ i}, (P j.val).weight (x.2 j) := by
    change (∏ j, (P j).weight (e.symm x j))=_
    rw [←mul_prod_erase _ _ (mem_univ i)]
    have h0 : e.symm x i=x.1 := by simp [e,Equiv.piSplitAt]
    rw [h0]
    congr 1
    rw [Finset.prod_subtype (p:=fun j : I => j ≠ i) (univ.erase i) (by simp [eq_comm])]
    apply prod_congr rfl
    intro j _
    simp [e,Equiv.piSplitAt,j.property]
  unfold Law.expect
  rw [←e.symm.sum_comp,Fintype.sum_prod_type]
  simp only [Law.pi,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  change (Law.pi P).weight (e.symm (a,b))*f (e.symm (a,b))=_
  rw [hweight]
  dsimp only [e]
  ring

theorem Law.expect_pi_fiber_le (P : ∀ i, Law (A i)) (i : I) (f : (∀ i, A i)→ℝ)
    (c : ℝ) (h : ∀ b, (P i).expect (fun a => f ((Equiv.piSplitAt i A).symm (a,b)))≤c) :
    (Law.pi P).expect f≤c := by
  rw [Law.expect_pi_split P i f]
  exact ((Law.pi _).expect_mono _ (fun _=>c) h).trans_eq (Law.expect_const _ _)

end

section
open Finset
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem Law.expect_prod_reverse (P : Law Ω) (Q : Law Γ) (f : Ω→Γ→ℝ) :
    (P.prod Q).expect (fun z=>f z.1 z.2)=Q.expect (fun b=>P.expect (fun a=>f a b)) := by
  simp only [Law.expect,Law.prod,Fintype.sum_prod_type,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

end

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
theorem Law.expect_pair (P : Law Ω) (Q : Law Γ) (f : Ω×Γ→ℝ) :
    (P.prod Q).expect f=P.expect (fun a=>Q.expect (fun b=>f (a,b))) :=
  Law.expect_prod P Q (fun a b=>f (a,b))
theorem Law.expect_pair_reverse (P : Law Ω) (Q : Law Γ) (f : Ω×Γ→ℝ) :
    (P.prod Q).expect f=Q.expect (fun b=>P.expect (fun a=>f (a,b))) :=
  Law.expect_prod_reverse P Q (fun a b=>f (a,b))
end UniformKServer.FiniteProbability

end

end OAI
