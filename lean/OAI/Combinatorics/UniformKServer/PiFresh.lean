import Mathlib
import OAI.Combinatorics.UniformKServer.FinitePiLaw

namespace OAI

                              
section

noncomputable section
namespace UniformKServer.FiniteProbability
open Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]

theorem Law.expect_eq_indicator {Y : Type*} [Fintype Y] (P : Law Y) (y : Y) :
    P.expect (fun z => if z=y then (1:ℝ) else 0)=P.weight y := by
  simp only [Law.expect,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true]

theorem Law.expect_pi_fresh (P : ∀ i, Law (A i)) (i : I) {Y : Type*}
    (f : (∀ i, A i) → Y) (hf : ∀ a b, (∀ j, j ≠ i → a j=b j) → f a=f b)
    (g : Y → A i → ℝ) :
    (Law.pi P).expect (fun a => g (f a) (a i))=
      ((Law.pi P).prod (P i)).expect (fun z => g (f z.1) z.2) := by
  have hid (a : ∀ i, A i) : g (f a) (a i)=
      ∑ b : A i, (if a i=b then (1:ℝ) else 0)*g (f a) b := by
    simp only [ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
  rw [Law.expect_congr _ _ _ hid,Law.expect_finset_sum]
  have hs (b : A i) :
      (Law.pi P).expect (fun a => (if a i=b then (1:ℝ) else 0)*g (f a) b)=
        (P i).weight b*(Law.pi P).expect (fun a => g (f a) b) := by
    rw [Law.expect_pi_separate (P:=P) i (fun c => if c=b then (1:ℝ) else 0)
      (fun a => g (f a) b) (by intro a c he; rw [hf a c he]),Law.expect_eq_indicator]
  simp_rw [hs]
  rw [Law.expect_prod (Law.pi P) (P i) (fun a b => g (f a) b)]
  change _ = (Law.pi P).expect (fun a => ∑ b, (P i).weight b*g (f a) b)
  rw [Law.expect_finset_sum]
  apply sum_congr rfl
  intro b _
  rw [Law.expect_mul]

end UniformKServer.FiniteProbability

end


end

end OAI
