import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.AdaptiveStream

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
def All : Experiment α → (α → Prop) → Prop
  | .done a,P => P a
  | .read f,P => All (f false) P ∧ All (f true) P
  | .delay _ p,P => All p P
lemma All.mono {p : Experiment α} {P Q : α → Prop} (h : All p P) (hPQ : ∀ a,P a→Q a) : All p Q := by
  induction p with
  | done a => exact hPQ a h
  | read p ih => exact ⟨ih false h.1,ih true h.2⟩
  | delay n p ih => exact ih h
lemma all_run (p : Experiment α) (P : α → Prop) (h : All p P) (b : Stream) : P (p.run b).1 := by
  induction p generalizing b with
  | done a => exact h
  | read p ih =>
    cases hb : b 0 <;> simp only [run,hb] <;> apply ih <;> first | exact h.1 | exact h.2
  | delay n p ih => exact ih h (shift n b)
lemma mean_nonneg (p : Experiment α) (f : α → ℚ) (h : All p (fun a=>0≤f a)) : 0≤p.mean f := by
  induction p with
  | done a => exact h
  | read p ih => exact div_nonneg (add_nonneg (ih false h.1) (ih true h.2)) (by norm_num)
  | delay n p ih => exact ih h
lemma all_true (p : Experiment α) : All p (fun _=>True) := by
  induction p with
  | done a => trivial
  | read p ih => exact ⟨ih false,ih true⟩
  | delay n p ih => exact ih
lemma all_indicator (p : Experiment α) (P : α → Prop) [DecidablePred P] :
    All p P ↔ p.mean (fun a=>if P a then 0 else 1)=0 := by
  induction p with
  | done a => simp [All,mean]
  | delay n p ih => exact ih
  | read p ih =>
    have hz (b : Bool) : 0≤(p b).mean (fun a=>if P a then 0 else 1) :=
      mean_nonneg _ _ ((all_true _).mono (by intro a _; split <;> norm_num))
    simp only [All,mean,ih]
    constructor
    · rintro ⟨h0,h1⟩; rw [h0,h1]; norm_num
    · intro h
      have h0:=hz false
      have h1:=hz true
      constructor <;> linarith
lemma all_of_mean_eq {p q : Experiment α} (h : ∀ f : α → ℚ,q.mean f=p.mean f)
    (P : α → Prop) (hp : All p P) : All q P := by
  classical
  rw [all_indicator,h,←all_indicator]
  exact hp
lemma cost_bind_le_of_all (p : Experiment α) (q : α → Experiment β) (N : ℕ)
    (h : All p (fun a=>(q a).cost≤N)) : (p.bind q).cost≤p.cost+N := by
  induction p with
  | done a => simpa only [All,bind,cost,Nat.zero_add] using h
  | read p ih =>
    have h0:=ih false h.1
    have h1:=ih true h.2
    simp only [cost,bind]
    omega
  | delay n p ih => simpa only [bind,cost,Nat.add_assoc] using Nat.add_le_add_left (ih h) n
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih
lemma all_map (p : Experiment α) (f : α → β) (P : β → Prop) :
    All (p.map f) P ↔ All p (fun a=>P (f a)) := by
  rw [map,all_bind]; rfl

variable {α : Type}
def worst : Experiment α → (α → ℕ) → ℕ
  | .done a,f => f a
  | .read p,f => max (worst (p false) f) (worst (p true) f)
  | .delay _ p,f => worst p f
lemma all_worst (p : Experiment α) (f : α → ℕ) : All p (fun a=>f a≤p.worst f) := by
  induction p with
  | done a => exact le_rfl
  | read p ih => exact ⟨(ih false).mono (fun a ha=>ha.trans (le_max_left _ _)),
      (ih true).mono (fun a ha=>ha.trans (le_max_right _ _))⟩
  | delay n p ih => exact ih
lemma worst_le (p : Experiment α) (f : α → ℕ) (N : ℕ) (h : All p (fun a=>f a≤N)) : p.worst f≤N := by
  induction p with
  | done a => exact h
  | read p ih => exact max_le (ih false h.1) (ih true h.2)
  | delay n p ih => exact ih h
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
