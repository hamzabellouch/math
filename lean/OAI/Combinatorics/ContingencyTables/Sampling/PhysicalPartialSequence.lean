import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRetryTail
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgram

namespace OAI

/-! # Sequencing finite prefixes that can stop at a live configuration

A called prefix may have reached the continuation, or may still be inside
its first program. The construction stops exactly at that interface.
-/

namespace ContingencyTables.PhysicalPartialSequence
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

variable {Γ Q R A : Type} [Inhabited Γ]

lemma mean_const (p : Experiment A) (v : ℚ) : p.mean (fun _ => v)=v := by
  induction p with
  | done => rfl
  | delay n p ih => exact ih
  | read p ih => simp only [Experiment.mean,ih]; ring

lemma halted_all {M : Table Γ Q} {out : A → Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (hc : c.state=none) :
    p.All (fun a => out a=c) := by
  induction h with
  | done a => rfl
  | read c p h ih =>
    have he (b : Bool) : PhysicalPost.tick M c b=c := by simp [PhysicalPost.tick,hc]
    exact ⟨by simpa only [he] using ih false (by rw [he]; exact hc),
      by simpa only [he] using ih true (by rw [he]; exact hc)⟩
  | delay c d n p hs hr ih =>
    have he : d=c := by
      rw [←hs (fun _ => false)]
      rcases c with ⟨q,T⟩
      cases hc
      exact execute_halted M n T (fun _ => false)
    subst d
    exact ih hc

lemma early_all_eq (M : Table Γ Q) (c d : Cfg Γ Q) (n : ℕ)
    (h : ∀ b : Stream,execute M n c b=d) :
    (early M n c).All (fun x => x=d) := by
  classical
  rw [Experiment.all_indicator,PhysicalPost.early_mean]
  simp only [h,ite_true,average_const]

/-- Relabelling a physical prefix for sequential composition may shorten
its post-halt padding, and preserves the law of its endpoint configuration. -/
theorem left_prefix (M : Table Γ Q) (N : Table Γ R) (r₀ : R)
    (out : A → Cfg Γ Q) (c : Cfg Γ Q) (p : Experiment A)
    (h : Implements M out c p) :
    ∃ q : Experiment (Cfg Γ Q),
      Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) q ∧
      (∀ f,q.mean f=p.mean (fun a => f (out a))) ∧ q.cost≤p.cost := by
  induction h with
  | done a => exact ⟨.done (out a),.done (out a),fun _ => rfl,le_rfl⟩
  | read c p h ih =>
    by_cases hc : c.state=none
    · have hall := halted_all (Implements.read c p h) hc
      refine ⟨.done c,.done c,?_,Nat.zero_le _⟩
      intro f
      have hm := Experiment.mean_congr_all (.read p) (fun a => f (out a)) (fun _ => f c)
        (hall.mono (by intro a ha; rw [ha]))
      exact (hm.trans (mean_const _ _)).symm
    · obtain ⟨q,hq,hqm,hqc⟩ := ih false
      obtain ⟨r,hr,hrm,hrc⟩ := ih true
      let v : Bool → Experiment (Cfg Γ Q) := fun b => if b then r else q
      refine ⟨.read v,?_,?_,?_⟩
      · apply Implements.read
        intro b
        rcases c with ⟨state,T⟩
        cases state with
        | none => exact False.elim (hc rfl)
        | some s =>
          rw [tick_left]
          cases b
          · exact hq
          · exact hr
      · intro f
        simp only [Experiment.mean,v,Bool.false_eq_true,ite_false,ite_true,hqm,hrm]
      · simp only [Experiment.cost,v,Bool.false_eq_true,ite_false,ite_true]
        omega
  | delay c d n p hs hr ih =>
    obtain ⟨q,hq,hqm,hqc⟩ := ih
    let u := early M n c
    have hu := early_left M N r₀ n c
    have hall : u.All (fun x => x=d) := early_all_eq M c d n hs
    refine ⟨u.bind (fun _ => q),?_,?_,?_⟩
    · apply hu.bind_all (fun _ => q) (leftCfg r₀)
      exact hall.mono (by intro x hx; rw [hx]; exact hq)
    · intro f
      rw [Experiment.mean_bind,mean_const,hqm]
      rfl
    · exact (Experiment.cost_bind_le u (fun _ => q) q.cost (fun _ => le_rfl)).trans
        (Nat.add_le_add (early_cost M n c) hqc)

/-- When endpoint configurations identify their labels, sequential composition
also preserves the complete label law, not just the endpoint law. -/
theorem left_prefix_injective [Nonempty A] (M : Table Γ Q) (N : Table Γ R) (r₀ : R)
    (out : A → Cfg Γ Q) (hinj : Function.Injective out) (c : Cfg Γ Q) (p : Experiment A)
    (h : Implements M out c p) :
    ∃ q : Experiment A,
      Implements (seq M N r₀) (fun a => leftCfg r₀ (out a)) (leftCfg r₀ c) q ∧
      (∀ f,q.mean f=p.mean f) ∧ q.cost≤p.cost := by
  classical
  obtain ⟨q,hq,hqm,hqc⟩ := left_prefix M N r₀ out c p h
  let dec : Cfg Γ Q → A := Function.invFun out
  have hd (a : A) : dec (out a)=a := Function.leftInverse_invFun hinj a
  have hall : q.All (fun x => out (dec x)=x) := by
    apply Experiment.all_of_mean_eq (p := p.map out) (q := q)
    · intro f
      rw [Experiment.mean_map]
      exact hqm f
    · rw [Experiment.all_map]
      exact (Experiment.all_true p).mono (by intro a _; rw [hd])
  refine ⟨q.map dec,hq.map_all dec (fun a => leftCfg r₀ (out a))
    (hall.mono (by intro x hx; rw [hx])),?_,?_⟩
  · intro f
    rw [Experiment.mean_map,hqm]
    simp only [hd]
  · simpa only [Experiment.cost_map] using hqc

end ContingencyTables.PhysicalPartialSequence

end OAI
