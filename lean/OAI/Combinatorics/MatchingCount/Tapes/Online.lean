import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.OnlineStackCompiler

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

inductive Executes (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
    (out : α → TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ → Experiment α → Prop
  | done (a) : Executes M coin out (out a) (.done a)
  | read (l v S) (f : Bool → Λ) (p : Bool → Experiment α)
      (hf : coin l=some f)
      (rest : ∀ b,Executes M coin out ⟨some (f b),v,S⟩ (p b)) :
      Executes M coin out ⟨some l,v,S⟩ (.read p)
  | step (l v S) (p : Experiment α) (safe : coin l=none)
      (rest : Executes M coin out (TM2.stepAux (M l) v S) p) :
      Executes M coin out ⟨some l,v,S⟩ (.delay 1 p)

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}
lemma bind {β : Type} (h : Executes M coin out c p) (q : α → Experiment β)
    (out' : β → TM2.Cfg Γ Λ σ) (hq : ∀ a,Executes M coin out' (out a) (q a)) :
    Executes M coin out' c (p.bind q) := by
  induction h with
  | done a => exact hq a
  | read l v S f p hf rest ih => exact .read l v S f _ hf ih
  | step l v S p safe rest ih => exact .step l v S _ safe ih

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

noncomputable def factor (M : Λ → TM2.Stmt Γ Λ σ) (H n : ℕ) : ℕ :=
  overhead M*(1+2*accesses M*(H+n*accesses M+1))+1
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_mono [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H H' n n' : ℕ) (hH : H≤H') (hn : n≤n') :
    factor M H n ≤ factor M H' n' := by unfold factor; gcongr
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_shift [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H n : ℕ) : factor M (H+accesses M) n=factor M H (1+n) := by
  unfold factor
  congr 3; ring

theorem compile (h : Executes M coin out c p) (H : ℕ) (hH : StackCost.StackBound c.stk H) :
    ∃ q : Experiment α,
      PhysicalPost.Implements (table M coin) (fun a=>cfg (out a)) (cfg c) q ∧
      (∀ f : α → ℚ,q.mean f=p.mean f) ∧ q.cost ≤ p.cost*factor M H p.cost := by
  induction h generalizing H with
  | done a => exact ⟨.done a,.done a,fun _=>rfl,by simp [Experiment.cost]⟩
  | read l v S f p hf rest ih =>
    choose q hq hmean hcost using fun b=>ih b H hH
    refine ⟨.read q,.read _ q (fun b=>?_),?_,?_⟩
    · rw [random M coin l v S f hf b]
      exact hq b
    · intro g
      simp only [Experiment.mean,hmean]
    · have hn0 : (p false).cost≤1+max (p false).cost (p true).cost := by omega
      have hn1 : (p true).cost≤1+max (p false).cost (p true).cost := by omega
      have hc0 := (hcost false).trans (Nat.mul_le_mul_left (p false).cost (factor_mono (M:=M) H H _ _ le_rfl hn0))
      have hc1 := (hcost true).trans (Nat.mul_le_mul_left (p true).cost (factor_mono (M:=M) H H _ _ le_rfl hn1))
      have hp : 1≤factor M H (1+max (p false).cost (p true).cost) := by unfold factor; omega
      simp only [Experiment.cost]
      have hf0 := Nat.mul_le_mul_right (factor M H (1+max (p false).cost (p true).cost)) (le_max_left (p false).cost (p true).cost)
      have hf1 := Nat.mul_le_mul_right (factor M H (1+max (p false).cost (p true).cost)) (le_max_right (p false).cost (p true).cost)
      calc
        1+max (q false).cost (q true).cost ≤ 1+max (p false).cost (p true).cost*factor M H (1+max (p false).cost (p true).cost) := by omega
        _≤ (1+max (p false).cost (p true).cost)*factor M H (1+max (p false).cost (p true).cost) := by nlinarith
  | step l v S p safe rest ih =>
    let c : TM2.Cfg Γ Λ σ:=⟨some l,v,S⟩
    have hs : ∀ u,c.l=some u→coin u=none := by intro u hu; cases hu; exact safe
    obtain ⟨k,hk,he⟩:=deterministic M coin c hs H hH
    obtain ⟨q,hq,hm,hc⟩:=ih (H+accesses M) (StackCost.advance_bound M _ (accesses_bound M) c H hH)
    refine ⟨.delay k q,.delay _ _ k q he hq,hm,?_⟩
    simp only [Experiment.cost]
    rw [factor_shift] at hc
    have hfac : k≤factor M H (1+p.cost) := by
      apply hk.trans
      unfold factor
      have hh : H+accesses M+1≤H+(1+p.cost)*accesses M+1 := by nlinarith
      have hb : overhead M*(1+2*accesses M*(H+accesses M+1))≤
        overhead M*(1+2*accesses M*(H+(1+p.cost)*accesses M+1)) := by gcongr
      omega
    nlinarith
end Executes
end MatchingFPRAS.OnlineStack

end OAI
