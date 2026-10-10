import Mathlib

namespace OAI

noncomputable section

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable

local instance capMatchingDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

def edgeEnds (e : I → V × V) (i : I) : Finset V := {(e i).1,(e i).2}

def incident (e : I → V × V) (x : V) : Finset I :=
  Finset.univ.filter (fun i => (e i).1 = x ∨ (e i).2 = x)

lemma card_incident (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hd : ∀ x, G.degree x ≤ D) (e : I → V × V)
    (he : ∀ i, G.Adj (e i).1 (e i).2) (hi : Function.Injective e) (x : V) :
    (incident e x).card ≤ 2*D := by
  let L := Finset.univ.filter (fun i => (e i).1 = x)
  let R := Finset.univ.filter (fun i => (e i).2 = x)
  have hL : L.card ≤ G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_le_card_of_injOn (fun i => (e i).2)
    · intro i hiL
      have hix : (e i).1 = x := (Finset.mem_filter.mp hiL).2
      simpa [← hix] using he i
    · intro i hiL k hkL hik
      apply hi
      exact Prod.ext ((Finset.mem_filter.mp hiL).2.trans (Finset.mem_filter.mp hkL).2.symm) hik
  have hR : R.card ≤ G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_le_card_of_injOn (fun i => (e i).1)
    · intro i hiR
      have hix : (e i).2 = x := (Finset.mem_filter.mp hiR).2
      simpa [← hix] using (he i).symm
    · intro i hiR k hkR hik
      apply hi
      exact Prod.ext hik ((Finset.mem_filter.mp hiR).2.trans (Finset.mem_filter.mp hkR).2.symm)
  have heq : incident e x = L ∪ R := by ext i; simp [incident,L,R]
  rw [heq]
  have hh := Finset.card_union_le L R
  have hdx := hd x
  omega

theorem large_matching (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hd : ∀ x, G.degree x ≤ D) (e : I → V × V)
    (he : ∀ i, G.Adj (e i).1 (e i).2) (hi : Function.Injective e) :
    ∃ M : Finset I, (M : Set I).Pairwise (fun i k => Disjoint (edgeEnds e i) (edgeEnds e k)) ∧
      Fintype.card I ≤ M.card*(4*D) := by
  let T : Finset (Finset I) := Finset.univ.filter
    (fun M => (M : Set I).Pairwise (fun i k => Disjoint (edgeEnds e i) (edgeEnds e k)))
  have hT : T.Nonempty := ⟨∅, by simp [T]⟩
  obtain ⟨M,hmax⟩ := T.exists_maximal hT
  have hM : (M : Set I).Pairwise (fun i k => Disjoint (edgeEnds e i) (edgeEnds e k)) :=
    (Finset.mem_filter.mp hmax.1).2
  have cover (i : I) : ∃ m ∈ M, ¬Disjoint (edgeEnds e i) (edgeEnds e m) := by
    by_contra hn
    push Not at hn
    have hiM : i ∉ M := by
      intro hh
      exact Finset.disjoint_left.mp (hn i hh)
        (show (e i).1 ∈ edgeEnds e i by simp [edgeEnds]) (by simp [edgeEnds])
    have hpair : ((insert i M : Finset I) : Set I).Pairwise (fun a b => Disjoint (edgeEnds e a) (edgeEnds e b)) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hai | ham
      · subst a
        rcases Finset.mem_insert.mp hb with hbi | hbm
        · exact False.elim (hab hbi.symm)
        · exact hn b hbm
      · rcases Finset.mem_insert.mp hb with hbi | hbm
        · subst b
          exact (hn a ham).symm
        · exact hM ham hbm hab
    have hmem : insert i M ∈ T := by simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]; exact hpair
    exact hiM ((hmax.2 hmem (Finset.subset_insert i M)) (by simp))
  let touch (m : I) := incident e (e m).1 ∪ incident e (e m).2
  have hall : (Finset.univ : Finset I) ⊆ M.biUnion touch := by
    intro i _
    obtain ⟨m,hm,hmt⟩ := cover i
    refine Finset.mem_biUnion.mpr ⟨m,hm,?_⟩
    have hs : ∃ x, x ∈ edgeEnds e i ∧ x ∈ edgeEnds e m := by
      simpa only [Finset.not_disjoint_iff] using hmt
    rcases hs with ⟨x,hx,hy⟩
    simp only [edgeEnds, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy <;>
      simp [touch,incident,hy]
  have ht (m : I) : (touch m).card ≤ 4*D := by
    have h1 := card_incident G D hd e he hi (e m).1
    have h2 := card_incident G D hd e he hi (e m).2
    have hh := Finset.card_union_le (incident e (e m).1) (incident e (e m).2)
    dsimp [touch]
    omega
  refine ⟨M,hM,?_⟩
  simpa only [Finset.card_univ] using (Finset.card_le_card hall).trans
    (Finset.card_biUnion_le_card_mul M touch (4*D) (fun m _ => ht m))

end ExtremalEdges

end

end OAI
