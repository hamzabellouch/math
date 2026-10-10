import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ReciprocalLossBudget

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {L J : ℝ}
def ContextDescription.cleanDomain (C : ContextDescription (κ:=κ) p x L J) (c : κ) (i : Fin n) :=
  if 0 < map p C.context c then C.domain c i else ∅
lemma ContextDescription.clean_contains (C : ContextDescription (κ:=κ) p x L J) :
    ∀z,0<p z→∀i,x z i∈C.cleanDomain (C.context z) i := by
  intro z hz i
  have hp : 0 < map p C.context (C.context z) := by
    change 0 < ∑a,if C.context a=C.context z then p a else 0
    have hh:=Finset.single_le_sum (s:=Finset.univ) (a:=z)
      (f:=fun a=>if C.context a=C.context z then p a else 0)
      (fun a _=>by split_ifs; exact p.nonneg a; exact le_rfl) (Finset.mem_univ z)
    simp only at hh
    exact hz.trans_le hh
  simpa only [cleanDomain,ite_eq_left hp] using C.contains z hz i
lemma ContextDescription.clean_cap (C : ContextDescription (κ:=κ) p x L J) :
    ∀c i,((C.cleanDomain c i).card:ℝ)≤Real.exp J := by
  intro c i
  by_cases hp : 0 < map p C.context c
  · obtain ⟨z,hz,rfl⟩:=map_positive p C.context c hp
    have hh:=C.cap z hz i
    rw [cleanDomain,ite_eq_left hp]
    apply card_le_of_log_le (by positivity) (Real.exp_pos _)
    simpa only [Real.log_exp] using hh
  · simp only [cleanDomain,ite_eq_right hp,Finset.card_empty,Nat.cast_zero]
    exact (Real.exp_pos _).le
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} {admissible : (Fin N→α)→Prop}
def Prepared.mono {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible}
    {ctx : Ω→κ} {J B B' M : ℝ} (P : Prepared S ctx J B M) (hB : B≤B') :
    Prepared S ctx J B' M where
  domain:=P.domain
  contains:=P.contains
  cap:=P.cap
  deficit:=P.deficit.trans hB
  incident:=P.incident
  consistent:=P.consistent
  occupancy:=P.occupancy
end
end SharpRamseyFive.SelectedTuple

end OAI
