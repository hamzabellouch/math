import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenFlow
import OAI.Combinatorics.UniformKServer.PilotTemplates

namespace OAI

                                    
section

/-! Conditional tests of the true labeled pre-request positions. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw PilotEdits
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

theorem counts_test (D : Data X Ω k) (t : ℕ) (ω : Ω) (b : X→ℝ) :
    (∑ p,counts D t ω p*b p)=∑ a : Fin k,b (D.position t ω a) := by
  simp only [counts,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [atom,ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]

theorem filtered_test (D : Data X Ω k) (t : ℕ) (b : Ω→X→ℝ)
    (hb : ∀ ω v,(D.filtration (t+1)).r ω v→b ω=b v) :
    average D.weight (fun ω=>∑ p,filtered D t ω p*b ω p)=
      average D.weight (fun ω=>∑ a : Fin k,b ω (D.position t ω a)) := by
  have hp (p : X) : (∑ ω,D.weight ω*(filtered D t ω p*b ω p))=
      ∑ ω,D.weight ω*(counts D t ω p*b ω p) := by
    have h := test_identity (fun v=>(D.positive v).le) (D.filtration (t+1))
      (fun ω=>b ω p) (fun ω=>counts D t ω p) (fun ω v hv=>congrFun (hb ω v hv) p)
    unfold filtered
    convert h using 1 <;> apply sum_congr rfl <;> intro ω _ <;> ring
  unfold average
  simp_rw [←counts_test D t]
  simp only [mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl (fun p _=>hp p)

end UniformKServer.HiddenFlow

end


end

end OAI
