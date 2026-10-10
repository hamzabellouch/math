import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure
import OAI.Combinatorics.MatchingCount.Machines.OnlineTree

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A B : Type}
lemma worst_mono (p : Experiment A) (f g : A→ℕ) (h : p.All (fun a=>f a≤g a)) :
    p.worst f≤p.worst g := by
  induction p with
  | done a => exact h
  | read p ih => exact max_le_max (ih false h.1) (ih true h.2)
  | delay n p ih => exact ih h
lemma All.and {p : Experiment A} {P Q : A→Prop} (hp : p.All P) (hq : p.All Q) :
    p.All (fun a=>P a ∧ Q a) := by
  induction p with
  | done a => exact ⟨hp,hq⟩
  | read p ih => exact ⟨ih false hp.1 hq.1,ih true hp.2 hq.2⟩
  | delay n p ih => exact ih hp hq
lemma worst_const (p : Experiment A) (n : ℕ) : p.worst (fun _=>n)=n := by
  induction p with
  | done a => rfl
  | read p ih => simp only [worst,ih, max_self]
  | delay n p ih => exact ih
lemma worst_bind (p : Experiment A) (f : A→Experiment B) (h : B→ℕ) :
    (p.bind f).worst h=p.worst (fun a=>(f a).worst h) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,worst,ih]
  | delay n p ih => exact ih
lemma worst_map (p : Experiment A) (f : A→B) (h : B→ℕ) :
    (p.map f).worst h=p.worst (h ∘ f) := worst_bind _ _ _
lemma worst_eq_of_mean_eq {p q : Experiment A} (h : ∀ f : A→ℚ,p.mean f=q.mean f) (g : A→ℕ) :
    p.worst g=q.worst g := by
  apply Nat.le_antisymm
  · exact worst_le _ _ _ (all_of_mean_eq h _ (all_worst q g))
  · exact worst_le _ _ _ (all_of_mean_eq (fun f=>(h f).symm) _ (all_worst p g))
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def WorkBound {f : A→Experiment B} (F : Realizer f) (measure : A→ℕ) : Prop :=
  ∃ p : Polynomial ℕ,∀ a,F.cost a+(f a).worst weight≤p.eval (measure a)
abbrev PolynomialTime {f : A→Experiment B} (F : Realizer f) : Prop := WorkBound F weight
lemma work_deterministic {f : A→B} {F : TreeTyped.Realizer f} {m : A→ℕ}
    (hF : TreeTyped.WorkBound F m) : WorkBound (deterministic F) m := hF
lemma work_congr {f g : A→Experiment B} {F : Realizer f} {m : A→ℕ}
    (h : ∀ a w,(f a).mean w=(g a).mean w) (hF : WorkBound F m) : WorkBound (F.congr h) m := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  change F.cost a+(g a).worst weight≤_
  rw [←Experiment.worst_eq_of_mean_eq (h a)]
  exact hp a
lemma work_remeasure {f : A→Experiment B} {F : Realizer f} {m n : A→ℕ}
    (hF : WorkBound F m) (p : Polynomial ℕ) (hm : ∀ a,m a≤p.eval (n a)) : WorkBound F n := by
  obtain ⟨q,hq⟩:=hF
  exact ⟨q.comp p,fun a=>(hq a).trans (by simpa using polynomial_eval_monotone q (hm a))⟩
lemma work_of_polynomial {f : A→Experiment B} {F : Realizer f} {m : A→ℕ}
    (hF : PolynomialTime F) (p : Polynomial ℕ) (hm : ∀ a,weight a≤p.eval (m a)) : WorkBound F m :=
  work_remeasure hF p hm
lemma work_composition {f : A→Experiment B} {g : B→Experiment C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} {n : B→ℕ} (hF : WorkBound F m) (hG : WorkBound G n)
    (p : Polynomial ℕ) (hm : ∀ a,(f a).All (fun b=>n b≤p.eval (m a))) :
    WorkBound (composition F G) m := by
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=hG
  refine ⟨q+2*(r.comp p),fun a=>?_⟩
  have hb : (f a).All (fun b=>G.cost b+(g b).worst weight≤r.eval (p.eval (m a))) :=
    (hm a).mono (fun b hb=>(hr b).trans (polynomial_eval_monotone r hb))
  have h1:=Experiment.worst_le _ _ _ (hb.mono (fun b hb=>Nat.le_trans (Nat.le_add_right _ _) hb))
  have h2:=Experiment.worst_le _ _ _ (hb.mono (fun b hb=>Nat.le_trans (Nat.le_add_left _ _) hb))
  have h3:=hq a
  change F.cost a+(f a).worst G.cost+((f a).bind g).worst weight≤_
  rw [Experiment.worst_bind]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega
lemma work_then_polynomial {f : A→Experiment B} {g : B→Experiment C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} (hF : WorkBound F m) (hG : PolynomialTime G) : WorkBound (composition F G) m := by
  obtain ⟨p,hp⟩:=hF
  apply work_composition ⟨p,hp⟩ hG p
  intro a
  exact (Experiment.all_worst (f a) weight).mono (fun b hb=>hb.trans (Nat.le_trans (Nat.le_add_left _ _) (hp a)))
lemma polynomial_composition {f : A→Experiment B} {g : B→Experiment C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (composition F G) := work_then_polynomial hF hG
lemma polynomial_deterministic {f : A→B} {F : TreeTyped.Realizer f} (hF : TreeTyped.PolynomialTime F) :
    PolynomialTime (deterministic F) := hF
end MatchingFPRAS.OnlineTree

end OAI
