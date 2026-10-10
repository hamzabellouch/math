import Mathlib
import OAI.Combinatorics.UniformKServer.RoundingChain
import OAI.Combinatorics.UniformKServer.Disintegration

namespace OAI

noncomputable section

/-! The adapted joint repair gives genuine conditional state transitions, with
both marginal identities and their exact transport expectation. -/
namespace UniformKServer.TreeRounding.ChainInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]
variable (D : ChainInput S k X Ω)

theorem first_law (t : ℕ) (ω : Ω) :
    (D.joint t ω).map Prod.fst=(D.distribution t ω).law := by
  apply FiniteProbability.Law.ext_expect
  intro f
  rw [Law.expect_map]
  exact D.first t ω f

theorem second_law (t : ℕ) (ω : Ω) :
    (D.joint t ω).map Prod.snd=(D.distribution (t+1) ω).law := by
  apply FiniteProbability.Law.ext_expect
  intro f
  rw [Law.expect_map]
  exact D.second t ω f

def kernel (t : ℕ) (ω : Ω) (s : State S k) : FiniteProbability.Law (State S k) :=
  ((D.joint t ω).conditional Prod.fst (D.joint t ω) s).map Prod.snd

theorem kernel_causal (t : ℕ) (ω v : Ω) (he : (D.filtration (t+1)).r ω v) :
    D.kernel t ω=D.kernel t v := by
  funext s
  unfold kernel
  rw [D.joint_causal t ω v he]

theorem kernel_cost (t : ℕ) (ω : Ω) (f : State S k→State S k→ℝ) :
    (D.distribution t ω).law.expect (fun s=>(D.kernel t ω s).expect (f s))=
      (D.joint t ω).expect (fun st=>f st.1 st.2) := by
  have he (s : State S k) : (D.kernel t ω s).expect (f s)=
      ((D.joint t ω).conditional Prod.fst (D.joint t ω) s).expect (fun u=>f s u.2) :=
    Law.expect_map _ _ _
  simp_rw [he]
  rw [←D.first_law t ω]
  exact (D.joint t ω).disintegrate Prod.fst (D.joint t ω) (fun s st=>f s st.2)

theorem kernel_next (t : ℕ) (ω : Ω) :
    (D.distribution t ω).law.bind (D.kernel t ω)=(D.distribution (t+1) ω).law := by
  apply FiniteProbability.Law.ext_expect
  intro f
  rw [Law.expect_bind,D.kernel_cost t ω (fun _ u=>f u)]
  exact D.second t ω f

theorem kernel_rounded (t : ℕ) (ω : Ω) (s u : State S k)
    (hs : 0 < (D.distribution t ω).law.weight s) (hu : 0 < (D.kernel t ω s).weight u) :
    Rounded (D.allocation (t+1) ω) u.value := by
  rw [←D.first_law t ω] at hs
  obtain ⟨st,he,hst⟩ := map_positive _ Prod.snd u hu
  have hp := (D.joint t ω).conditional_positive Prod.fst (D.joint t ω) s hs st hst
  have hpos : 0 < ((D.joint t ω).map Prod.snd).weight u := by
    have hh := lt_of_lt_of_le hp.2 ((D.joint t ω).weight_le_map Prod.snd st)
    simpa only [he] using hh
  rw [D.second_law t ω] at hpos
  exact (D.distribution (t+1) ω).rounded u hpos

end UniformKServer.TreeRounding.ChainInput

end

end OAI
