import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingDeficit

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical
noncomputable section
variable {Ω α Γ : Type*} [Fintype Ω] [Fintype α] [Fintype Γ]

theorem entropy_append_alphabet (p : Law Ω) (C : Ω→Γ) (F : Ω→α)
    (D : Γ→Finset α) (hD : ∀ x,p.mass x≠0→F x∈D (C x)) :
    entropy (p.map (fun x=>(F x,C x))) ≤ entropy (p.map C)+
      ∑ x,p.mass x*log (D (C x)).card := by
  rw [entropy_cond_chain,←p.sum_map C (fun c=>log (D c).card)]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro c _
  by_cases hc : (p.map C).mass c=0
  · simp [hc]
  · apply mul_le_mul_of_nonneg_left _ ((p.map C).nonneg c)
    apply entropy_mapped_support
    intro x hx
    obtain ⟨hp,he⟩ := p.cond_support C c hc x hx
    simpa only [←he] using hD x hp

def ProtocolValid (D : ∀ n:ℕ,(Fin n→α)→Finset α) :
    ∀ n:ℕ,(Fin n→α)→Prop
  | 0,_ => True
  | n+1,x => ProtocolValid D n (Fin.init x) ∧ x (Fin.last n)∈D n (Fin.init x)

noncomputable def protocolCost (D : ∀ n:ℕ,(Fin n→α)→Finset α) :
    ∀ n:ℕ,(Fin n→α)→ℝ
  | 0,_ => 0
  | n+1,x => protocolCost D n (Fin.init x)+log (D n (Fin.init x)).card

omit [Fintype Γ] in

theorem protocol_entropy (p : Law Ω) (D : ∀ n:ℕ,(Fin n→α)→Finset α)
    (n : ℕ) (F : Ω→Fin n→α) (hF : ∀ x,p.mass x≠0→ProtocolValid D n (F x)) :
    entropy (p.map F)≤∑ x,p.mass x*protocolCost D n (F x) := by
  induction n with
  | zero =>
    have h := entropy_le_log_card (p.map F) univ (fun x hx=>False.elim (hx (mem_univ x)))
    simpa only [card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,
      Nat.cast_one,log_one,protocolCost,mul_zero,sum_const_zero] using h
  | succ n ih =>
    let C := fun x=>Fin.init (F x)
    let a := fun x=>F x (Fin.last n)
    have hi := ih C (fun x hx=>(hF x hx).1)
    have ha := entropy_append_alphabet p C a (D n) (fun x hx=>(hF x hx).2)
    have he : entropy (p.map (fun x=>(a x,C x)))=entropy (p.map F) := by
      have h := entropy_map_eq_of_leftInverse (p.map F)
        (fun y:Fin (n+1)→α=>(y (Fin.last n),Fin.init y))
        (fun z:α×(Fin n→α)=>Fin.snoc z.2 z.1) (fun y=>Fin.snoc_init_self y)
      rw [Law.map_map] at h
      exact h
    rw [he] at ha
    have hs : (∑ x,p.mass x*protocolCost D n (C x))+
        (∑ x,p.mass x*log (D n (C x)).card)=
        ∑ x,p.mass x*protocolCost D (n+1) (F x) := by
      simp only [protocolCost,mul_add,sum_add_distrib,C]
    rw [←hs]
    linarith

omit [Fintype Γ] in

theorem protocol_entropy_maximum (p : Law Ω)
    (D : ∀ n:ℕ,(Fin n→α)→Finset α) (n : ℕ) (F : Ω→Fin n→α) (K : ℝ)
    (hF : ∀ x,p.mass x≠0→ProtocolValid D n (F x))
    (hK : ∀ x,p.mass x≠0→protocolCost D n (F x)≤K) :
    entropy (p.map F)≤K := by
  apply (protocol_entropy p D n F hF).trans
  calc
    _ ≤ ∑ x,p.mass x*K := by
      apply sum_le_sum
      intro x _
      by_cases hx : p.mass x=0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left (hK x hx) (p.nonneg x)
    _ = K := by rw [←sum_mul,p.total,one_mul]

end
end SharpLogRamsey.Selection

end

end OAI
