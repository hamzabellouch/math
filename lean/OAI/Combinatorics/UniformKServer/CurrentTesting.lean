import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenTesting

namespace OAI

                                     
section

/-! All-time adapted testing of the literal hidden member positions. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw PilotEdits
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

theorem current_test (D : Data X Ω k) (t : ℕ) (b : Ω→X→ℝ)
    (hb : ∀ ω v,(D.filtration t).r ω v→b ω=b v) :
    average D.weight (fun ω=>∑ p,current D t ω p*b ω p)=
      average D.weight (fun ω=>∑ a : Fin k,b ω (D.position t ω a)) := by
  have hp (p : X) : (∑ ω,D.weight ω*(current D t ω p*b ω p))=
      ∑ ω,D.weight ω*(counts D t ω p*b ω p) := by
    have h := test_identity (fun v=>(D.positive v).le) (D.filtration t)
      (fun ω=>b ω p) (fun ω=>counts D t ω p) (fun ω v hv=>congrFun (hb ω v hv) p)
    unfold current
    convert h using 1 <;> apply sum_congr rfl <;> intro ω _ <;> ring
  unfold average
  simp_rw [←counts_test D t]
  simp only [mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl (fun p _=>hp p)

omit [Fintype X] in
theorem member_distance (D : Data X Ω k) [MetricSpace X] (t : ℕ) (ω : Ω) :
    (∑ a : Fin k,dist (D.position t ω a) (D.position (t+1) ω a))=
      dist (D.position t ω (D.chosen t ω)) (D.request t ω) := by
  calc
    _=dist (D.position t ω (D.chosen t ω)) (D.position (t+1) ω (D.chosen t ω)) := by
      apply sum_eq_single (D.chosen t ω)
      · intro a _ ha
        rw [D.update,ite_eq_right ha,dist_self]
      · intro ha
        exact (ha (mem_univ _)).elim
    _=_ := by rw [D.update,ite_eq_left rfl]

end UniformKServer.HiddenFlow

end


end

end OAI
