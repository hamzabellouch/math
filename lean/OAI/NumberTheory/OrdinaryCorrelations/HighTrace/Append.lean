import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Block

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ForestTraversal
open Classical SimpleGraph
noncomputable section
variable {V : Type*} {G H : SimpleGraph V}

lemma Covers.append {u v z : V} {p : G.Walk u v} {q : G.Walk v z}
    {bs cs : List (Block H)} (hp : Covers p bs) (hq : Covers q cs) :
    Covers (p.append q) (bs++cs) := by
  constructor
  · intro x hx
    rcases (Walk.mem_support_append_iff p q).mp hx with hx | hx
    · obtain ⟨b,hb,hx⟩ := hp.1 x hx
      exact ⟨b,List.mem_append.mpr (Or.inl hb),hx⟩
    · obtain ⟨b,hb,hx⟩ := hq.1 x hx
      exact ⟨b,List.mem_append.mpr (Or.inr hb),hx⟩
  · intro e he heH
    rw [Walk.edges_append] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨b,hb,he⟩ := hp.2 e he heH
      exact ⟨b,List.mem_append.mpr (Or.inl hb),he⟩
    · obtain ⟨b,hb,he⟩ := hq.2 e he heH
      exact ⟨b,List.mem_append.mpr (Or.inr hb),he⟩

theorem chunk_cut_cover (H : SimpleGraph V) (L : ℕ) (hL : 0<L) {u v : V} (p : G.Walk u v) :
    ∃ bs : List (Block H),bs.length ≤ p.length/L+cutCount H p+1 ∧
      (∀ b ∈ bs,b.walk.length ≤ L) ∧ Covers p bs := by
  suffices aux : ∀ n,∀ (u v : V) (p : G.Walk u v),p.length=n →
      ∃ bs : List (Block H),bs.length ≤ p.length/L+cutCount H p+1 ∧
        (∀ b ∈ bs,b.walk.length ≤ L) ∧ Covers p bs from aux _ u v p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v p hn
    by_cases hp : p.length ≤ L
    · obtain ⟨z,first,rest,hrest,hlen,hcover⟩ := cut_cover H p
      exact ⟨⟨u,z,first⟩::rest,by simp only [List.length_cons]; exact Nat.succ_le_succ (hrest.trans (Nat.le_add_left _ _)),
        fun b hb => (hlen b hb).trans hp,hcover⟩
    · have hLp : L ≤ p.length := (lt_of_not_ge hp).le
      have htake : (p.take L).length=L := by simp [Walk.take_length,hLp]
      have hdrop : (p.drop L).length=p.length-L := Walk.drop_length p L
      have hlt : (p.drop L).length<n := by omega
      obtain ⟨bs,hbs,hbl,hbc⟩ := ih _ hlt _ _ (p.drop L) rfl
      obtain ⟨z,first,rest,hrest,hlen,hcover⟩ := cut_cover H (p.take L)
      let cs : List (Block H) := ⟨u,z,first⟩::rest
      have hcl : ∀ b ∈ cs,b.walk.length ≤ L := by simpa only [htake] using hlen
      have hcc : Covers (p.take L) cs := hcover
      have hcuts : cutCount H (p.take L)+cutCount H (p.drop L)=cutCount H p := by
        rw [←cutCount_append,p.append_take_drop_eq]
      have hdiv : p.length/L=(p.length-L)/L+1 := by
        conv_lhs => rw [← Nat.sub_add_cancel hLp]
        exact Nat.add_div_right _ hL
      refine ⟨cs++bs,?_,?_,?_⟩
      · simp only [List.length_append,cs,List.length_cons]
        rw [hdrop] at hbs
        omega
      · intro b hb
        exact (List.mem_append.mp hb).elim (hcl b) (hbl b)
      · simpa only [p.append_take_drop_eq L] using hcc.append hbc

end
end OrdinaryCorrelations.ForestTraversal

end

end OAI
