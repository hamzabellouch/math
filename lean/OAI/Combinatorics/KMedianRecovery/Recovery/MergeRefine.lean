import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergePath

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Good (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X) : Prop :=
  Valid loc F B Q v z lam eta H ∧ (H.toFinset \ F).card ≤ 2

def Coincident (loc : D → X) (F Q : Finset X) (H G : List X) : Prop :=
  ∃ i f : X, ∃ R : Finset X, i ∈ F ∧ f ∉ F ∧ i ∉ R ∧ f ∉ R ∧
    Q ∪ H.toFinset = insert i R ∧ Q ∪ G.toFinset = insert f R ∧
    ∀ j, dist (loc j) i = dist (loc j) f

inductive Edit (loc : D → X) (F B Q : Finset X) : List X → List X → Prop
  | freeAppend (H : List X) (i f : X) (hi : i ∈ F) (hf : f ∈ B)
      (hco : ∀ j, dist (loc j) i = dist (loc j) f) : Edit loc F B Q H (H++[f])
  | paidDelete (C T : List X) (i : X) (hi : i ∈ F) :
      Edit loc F B Q (C++i::T) (C++T)
  | coincident {H G : List X} (hc : Coincident loc F Q H G) : Edit loc F B Q H G

def Adjacent (loc : D → X) (F B Q : Finset X) (H G : List X) : Prop :=
  Edit loc F B Q H G ∨ Edit loc F B Q G H

inductive Chain (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) :
    ℕ → List X → List X → Prop
  | nil {H} (hgood : Good loc F B Q v z lam eta H) : Chain loc F B Q v z lam eta 0 H H
  | cons {n H G J} (hgood : Good loc F B Q v z lam eta H)
      (hstep : Adjacent loc F B Q H G) (tail : Chain loc F B Q v z lam eta n G J) :
      Chain loc F B Q v z lam eta (n+1) H J

lemma Chain.trans {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {n m : ℕ} {H G J : List X} (h : Chain loc F B Q v z lam eta n H G)
    (g : Chain loc F B Q v z lam eta m G J) : Chain loc F B Q v z lam eta (n+m) H J := by
  induction h with
  | nil => simpa using g
  | cons hh hs ht ih => simpa only [Nat.add_right_comm] using Chain.cons hh hs (ih g)

lemma Chain.first_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Chain loc F B Q v z lam eta n H G) :
    Good loc F B Q v z lam eta H := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

lemma Chain.last_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Chain loc F B Q v z lam eta n H G) :
    Good loc F B Q v z lam eta G := by
  induction h with
  | nil h => exact h
  | cons _ _ _ ih => exact ih

lemma Chain.symm {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Chain loc F B Q v z lam eta n H G) :
    Chain loc F B Q v z lam eta n G H := by
  induction h with
  | nil h => exact Chain.nil h
  | cons hh hs ht ih =>
    exact ih.trans (Chain.cons ht.first_good hs.symm (Chain.nil hh))

lemma Good.mono_free {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Good loc F B Q v z lam eta H) (hB : B ⊆ B') :
    Good loc F B' Q v z lam eta H :=
  ⟨⟨prefix_free_mono h.1.1 hB,h.1.2⟩,h.2⟩

omit [Fintype D] [PseudoMetricSpace X] in
lemma cap_append {F : Finset X} {H G : List X} {f : X} (hsub : H.Sublist G)
    (hcap : (G.toFinset \ F).card ≤ 1) : ((H++[f]).toFinset \ F).card ≤ 2 := by
  have hs : (H++[f]).toFinset \ F ⊆ (G.toFinset \ F) ∪ {f} := by
    intro x hx
    obtain ⟨hxH,hxF⟩ := Finset.mem_sdiff.mp hx
    rcases List.mem_append.mp (List.mem_toFinset.mp hxH) with hxH | hxH
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨List.mem_toFinset.mpr (hsub.subset hxH),hxF⟩)
    · exact Finset.mem_union_right _ (by simpa only [List.mem_singleton,Finset.mem_singleton] using hxH)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simp only [Finset.card_singleton] at hc
  omega

lemma entry_fresh {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {C T : List X} {i : X} (h : Prefix loc F B v z lam eta Q (C++i::T)) :
    i ∉ Q ∪ (C++T).toFinset := by
  have hiL : i ∈ C++i::T := List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hiQ : i ∉ Q := fun hi => Finset.disjoint_left.mp h.disjoint hi (List.mem_toFinset.mpr hiL)
  have hd := List.nodup_append.mp h.nodup
  have hiC : i ∉ C := fun hi => hd.2.2 i hi i (List.mem_cons_self ..) rfl
  have hiT := (List.nodup_cons.mp hd.2.1).1
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,not_or]
  exact ⟨hiQ,hiC,hiT⟩

theorem suffix_chain (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (C G : List X) (f : X) (hreg : ∀ i ∈ G, i ∈ F)
    (hvalid : ∀ R : List X, R.Sublist G → Good loc F B Q v z lam eta ((C++R)++[f])) :
    Chain loc F B Q v z lam eta G.length ((C++G)++[f]) (C++[f]) := by
  induction G with
  | nil => simpa only [List.append_nil,List.length_nil] using Chain.nil (hvalid [] (List.Sublist.refl []))
  | cons i G ih =>
    have hi : i ∈ F := hreg i (List.mem_cons_self ..)
    have hg : ∀ R : List X, R.Sublist G → Good loc F B Q v z lam eta ((C++R)++[f]) :=
      fun R hR => hvalid R (List.Sublist.cons i hR)
    have ht := ih (fun j hj => hreg j (List.mem_cons_of_mem _ hj)) hg
    have hs := Edit.paidDelete (loc := loc) (B := B) (Q := Q) C (G++[f]) i hi
    have hs' : Adjacent loc F B Q ((C++(i::G))++[f]) ((C++G)++[f]) :=
      Or.inl (by simpa only [List.append_assoc,List.cons_append] using hs)
    exact Chain.cons (hvalid _ (List.Sublist.refl _)) hs' ht

theorem remove_refinement (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hQ : Q ⊆ F ∪ B) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C T A : List X) (i f : X) (hi : i ∈ F) (hf : f ∉ F ∪ B)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hreg : ∀ j ∈ A, j ∈ F)
    (hbefore : Valid loc F B Q v z lam eta (C++i::T))
    (hafter : Valid loc F B Q v z lam eta ((C++T)++A))
    (hcapb : ((C++i::T).toFinset \ F).card ≤ 1)
    (hcapa : (((C++T)++A).toFinset \ F).card ≤ 1) :
    Chain loc F (insert f B) Q v z lam eta (A.length+2) (C++i::T) ((C++T)++A) := by
  have hfF : f ∉ F := fun h => hf (Finset.mem_union_left _ h)
  have hfH : f ∉ Q ∪ ((C++T)++A).toFinset :=
    fun h => hf ((Finset.union_subset hQ hafter.1.opened_subset) h)
  have hval : ∀ R : List X, R.Sublist A →
      Good loc F (insert f B) Q v z lam eta (((C++T)++R)++[f]) := by
    intro R hR
    refine ⟨delete_suffix_with_copy loc F B Q v z lam eta hv hvsmall hz hlam hrow
      C T A R i f hfH hco hbefore hafter.1 hR,?_⟩
    exact cap_append (hR.append_left (C++T)) hcapa
  have hdel := suffix_chain loc F (insert f B) Q v z lam eta (C++T) A f hreg hval
  have hgoodb : Good loc F (insert f B) Q v z lam eta (C++i::T) :=
    ⟨⟨prefix_free_mono hbefore.1 (Finset.subset_insert f B),hbefore.2⟩,by omega⟩
  have hgooda : Good loc F (insert f B) Q v z lam eta ((C++T)++A) :=
    ⟨⟨prefix_free_mono hafter.1 (Finset.subset_insert f B),hafter.2⟩,by omega⟩
  have hc : Coincident loc F Q (C++i::T) ((C++T)++[f]) := by
    refine ⟨i,f,Q ∪ (C++T).toFinset,hi,hfF,entry_fresh hbefore.1,?_,?_,?_,hco⟩
    · intro hh
      exact hfH ((Finset.union_subset_union_right (by
        intro x hx
        exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (List.mem_toFinset.mp hx))) :
          (C++T).toFinset ⊆ ((C++T)++A).toFinset)) hh)
    · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
    · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_empty,
        Finset.union_insert]
  have hfirst := Chain.cons hgoodb (Or.inl (Edit.coincident hc)) (Chain.nil hdel.last_good)
  have hlast := Chain.cons hdel.first_good
    (Or.inr (Edit.freeAppend ((C++T)++A) i f hi (Finset.mem_insert_self _ _) hco)) (Chain.nil hgooda)
  have hh := (hfirst.trans hdel.symm).trans hlast
  simpa only [Nat.zero_add,Nat.add_comm 1 A.length,Nat.add_assoc] using hh

end

open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] in
lemma Edit.mono_free {loc : D → X} {F B B' Q : Finset X} {H G : List X}
    (h : Edit loc F B Q H G) (hB : B ⊆ B') : Edit loc F B' Q H G := by
  cases h with
  | freeAppend H i f hi hf hco => exact Edit.freeAppend H i f hi (hB hf) hco
  | paidDelete C T i hi => exact Edit.paidDelete C T i hi
  | coincident hc => exact Edit.coincident hc

lemma Chain.mono_free {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Chain loc F B Q v z lam eta n H G) (hB : B ⊆ B') :
    Chain loc F B' Q v z lam eta n H G := by
  induction h with
  | nil hg => exact Chain.nil (hg.mono_free hB)
  | cons hg hs ht ih =>
    exact Chain.cons (hg.mono_free hB) (hs.elim (fun h => Or.inl (h.mono_free hB))
      (fun h => Or.inr (h.mono_free hB))) ih

lemma good_of_one {loc : D → X} {F B B' Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H : List X} (h : PhaseMergePath.Good loc F B Q copy v z lam eta H)
    (hB : pool F B copy ⊆ B') : Good loc F B' Q v z lam eta H :=
  ⟨⟨prefix_free_mono h.1.1 hB,h.1.2⟩,h.2.trans (by omega)⟩

theorem refine_walk (loc : D → X) (F B Q : Finset X) (copy spare : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    {n : ℕ} {H G : List X} (h : Walk loc F B Q copy v z lam eta n H G) :
    ∃ m ≤ n*(F.card+2),
      Chain loc F (pool F (pool F B copy) spare) Q v z lam eta m H G := by
  have hB1 : pool F B copy ⊆ pool F (pool F B copy) spare := subset_pool _ _ _
  have hQ1 : Q ⊆ F ∪ pool F B copy := hQ.trans (Finset.union_subset_union_right (subset_pool _ _ _))
  induction h with
  | nil hg => exact ⟨0,by simp,Chain.nil (good_of_one hg hB1)⟩
  | @cons n H G J hg step tail ih =>
    obtain ⟨m,hm,hchain⟩ := ih
    have hg' := tail.first_good
    have hstep : ∃ l ≤ F.card+2,
        Chain loc F (pool F (pool F B copy) spare) Q v z lam eta l H G := by
      cases step with
      | add H i hi =>
        refine ⟨1,by omega,Chain.cons (good_of_one hg hB1) (Or.inl ?_) (Chain.nil (good_of_one hg' hB1))⟩
        exact Edit.freeAppend H i (copy i) hi
          (hB1 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))) (hd i hi)
      | remove C T A i hi hA hreg =>
        have hh := remove_refinement loc F (pool F B copy) Q v z lam eta hv hvsmall hz hlam
          hQ1 hrow C T A i (spare i) hi (hs i hi) (he i hi) hreg hg.1 hg'.1 hg.2 hg'.2
        refine ⟨A.length+2,Nat.add_le_add_right (regular_length hA hreg) 2,?_⟩
        exact hh.mono_free (insert_subset_pool hi)
      | replace C T i hi hin =>
        have hc' : Coincident loc F Q (C++i::T) (C++copy i::T) := by
          refine ⟨i,copy i,Q ∪ (C++T).toFinset,hi,?_,hin,entry_fresh hg.1.1,?_,?_,hd i hi⟩
          · intro hci
            exact hc i hi (Finset.mem_union_left _ hci)
          · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
          · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
        exact ⟨1,by omega,Chain.cons (good_of_one hg hB1) (Or.inr (Edit.coincident hc'))
          (Chain.nil (good_of_one hg' hB1))⟩
    obtain ⟨l,hl,hlchain⟩ := hstep
    refine ⟨l+m,?_,hlchain.trans hchain⟩
    calc
      l+m ≤ (F.card+2)+n*(F.card+2) := Nat.add_le_add hl hm
      _ = (n+1)*(F.card+2) := by ring

theorem regular_phase_chain (loc : D → X) (F B Q : Finset X) (copy spare : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (hH : Valid loc F B Q v z lam eta H)
    (hG : Valid loc F B Q v z lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) :
    ∃ m ≤ F.card*(F.card+3)*(F.card+2),
      Chain loc F (pool F (pool F B copy) spare) Q v z lam eta m H G := by
  obtain ⟨n,hn,hw⟩ := regular_phase_path loc F B Q copy v z lam eta hv hvsmall hz hlam
    heta hQ hdis hrow hc hd G H hGr hHr hG hH
  obtain ⟨m,hm,hchain⟩ := refine_walk loc F B Q copy spare v z lam eta hv hvsmall hz hlam
    hQ hrow hc hd hs he hw
  exact ⟨m,hm.trans (Nat.mul_le_mul_right (F.card+2) hn),hchain⟩

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive Jump (X : Type*) where
  | add (i : X)
  | remove (C T A : List X) (i : X)
  | replace (C T : List X) (i : X)
  deriving DecidableEq

def Jump.source (copy : X → X) (H : List X) : Jump X → List X
  | .add _ => H
  | .remove C T _ i => C++i::T
  | .replace C T i => C++copy i::T

def Jump.target (copy : X → X) (H : List X) : Jump X → List X
  | .add i => H++[copy i]
  | .remove C T A _ => (C++T)++A
  | .replace C T i => C++i::T

def Jump.labels (F : Finset X) : Jump X → Prop
  | .add i => i∈F
  | .remove _ _ A i => i∈F ∧ ∀ a∈A,a∈F
  | .replace _ _ i => i∈F

instance (F : Finset X) (J : Jump X) : Decidable (J.labels F) := by
  cases J <;> dsimp only [Jump.labels] <;> infer_instance

def cuts : List X → List (List X × X × List X)
  | [] => []
  | i::T => ([],i,T)::(cuts T).map (fun p => (i::p.1,p.2.1,p.2.2))

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma mem_cuts {H C T : List X} {i : X} : (C,i,T)∈cuts H ↔ H=C++i::T := by
  constructor
  · intro h
    induction H generalizing C T i with
    | nil => simp only [cuts,List.not_mem_nil] at h
    | cons x H ih =>
      rcases List.mem_cons.mp h with h | h
      · cases h
        rfl
      · obtain ⟨⟨C',i',T'⟩,hp,he⟩ := List.mem_map.mp h
        cases he
        exact congrArg (List.cons x) (ih hp)
  · intro h
    subst H
    induction C with
    | nil => exact List.mem_cons_self ..
    | cons c C ih =>
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(C,i,T),ih,rfl⟩)

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma cuts_length (H : List X) : (cuts H).length=H.length := by
  induction H with
  | nil => rfl
  | cons x H ih => simp only [cuts,List.length_cons,List.length_map,ih]

def candidates (R : List X) (H G : List X) : List (Jump X) :=
  (R.map Jump.add) ++
  ((cuts H).map (fun p => Jump.remove p.1 p.2.2 (G.drop (H.length-1)) p.2.1)) ++
  ((cuts G).map (fun p => Jump.replace p.1 p.2.2 p.2.1))

def accepts (F : Finset X) (copy : X → X) (H G : List X) (J : Jump X) : Prop :=
  J.source copy H=H ∧ J.target copy H=G ∧ J.labels F

instance (F : Finset X) (copy : X → X) (H G : List X) (J : Jump X) :
    Decidable (accepts F copy H G J) := by unfold accepts; infer_instance

def view (F : Finset X) (R : List X) (copy : X → X) (H G : List X) : Option (Jump X) :=
  (candidates R H G).find? (fun J => decide (accepts F copy H G J))

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma candidates_length (R : List X) (H G : List X) :
    (candidates R H G).length=R.length+H.length+G.length := by
  simp only [candidates,List.length_append,List.length_map,cuts_length]

omit [PseudoMetricSpace X] in
lemma view_sound (F : Finset X) (R : List X) (copy : X → X) (H G : List X) (J : Jump X)
    (h : view F R copy H G=some J) : accepts F copy H G J := by
  have hh := List.find?_some h
  exact of_decide_eq_true hh

lemma view_exists {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam : ℝ}
    {H G : List X} (R : List X) (hR : ∀ i∈F,i∈R)
    (h : Step loc F B Q copy v z lam H G) :
    ∃ J,view F R copy H G=some J := by
  have hex : ∃ J∈candidates R H G, accepts F copy H G J := by
    cases h with
    | add H i hi =>
      refine ⟨.add i,?_,rfl,rfl,hi⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i,hR i hi,rfl⟩))
    | remove C T A i hi hA hreg =>
      refine ⟨.remove C T A i,?_,rfl,rfl,hi,hreg⟩
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨(C,i,T),mem_cuts.mpr rfl,?_⟩
      have hd : ((C++T)++A).drop ((C++i::T).length-1)=A := by
        have he : (C++i::T).length-1=(C++T).length := by simp only [List.length_append,List.length_cons]; omega
        rw [he,List.drop_left]
      simp only [hd]
    | replace C T i hi hin =>
      refine ⟨.replace C T i,?_,rfl,rfl,hi⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(C,i,T),mem_cuts.mpr rfl,rfl⟩)
  have hn : view F R copy H G ≠ none := by
    intro hn
    obtain ⟨J,hJ,hacc⟩ := hex
    have hh := List.find?_eq_none.mp hn J hJ
    exact hh (decide_eq_true hacc)
  exact Option.ne_none_iff_exists'.mp hn

inductive EPath (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) :
    List X → List (List X) → List X → Prop
  | nil {H} (h : PhaseMergeRefinement.Good loc F B Q v z lam eta H) :
      EPath loc F B Q v z lam eta H [] H
  | cons {H G T J} (h : PhaseMergeRefinement.Good loc F B Q v z lam eta H)
      (e : Adjacent loc F B Q H G) (t : EPath loc F B Q v z lam eta G T J) :
      EPath loc F B Q v z lam eta H (G::T) J

lemma EPath.toChain {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J) :
    Chain loc F B Q v z lam eta T.length H J := by
  induction h with
  | nil h => exact .nil h
  | cons h e t ih => exact .cons h e ih

lemma EPath.first_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J) :
    PhaseMergeRefinement.Good loc F B Q v z lam eta H := h.toChain.first_good

lemma EPath.last_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J) :
    PhaseMergeRefinement.Good loc F B Q v z lam eta J := h.toChain.last_good

lemma EPath.append {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J K : List X} {T U : List (List X)} (h : EPath loc F B Q v z lam eta H T J)
    (h' : EPath loc F B Q v z lam eta J U K) :
    EPath loc F B Q v z lam eta H (T++U) K := by
  induction h with
  | nil => exact h'
  | cons h e t ih => exact .cons h e (ih h')

lemma EPath.mono_free {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J)
    (hBB : B⊆B') : EPath loc F B' Q v z lam eta H T J := by
  induction h with
  | nil h => exact .nil (h.mono_free hBB)
  | cons h e t ih =>
    exact .cons (h.mono_free hBB)
      (e.elim (fun he => Or.inl (he.mono_free hBB)) (fun he => Or.inr (he.mono_free hBB))) ih

def growSuffix (C : List X) (f : X) : List X → List (List X)
  | [] => []
  | i::A => growSuffix C f A ++ [(C++i::A)++[f]]

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma growSuffix_length (C A : List X) (f : X) : (growSuffix C f A).length=A.length := by
  induction A with
  | nil => rfl
  | cons i A ih => simp only [growSuffix,List.length_append,List.length_cons,List.length_nil,ih]

 theorem growSuffix_spec (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (C A : List X) (f : X) (hreg : ∀ i∈A,i∈F)
    (hval : ∀ R : List X, R.Sublist A →
      PhaseMergeRefinement.Good loc F B Q v z lam eta ((C++R)++[f])) :
    EPath loc F B Q v z lam eta (C++[f]) (growSuffix C f A) ((C++A)++[f]) := by
  induction A with
  | nil => simpa only [growSuffix,List.append_nil] using EPath.nil (hval [] (List.Sublist.refl []))
  | cons i A ih =>
    have hi : i∈F := hreg i (List.mem_cons_self ..)
    have hg : ∀ R : List X, R.Sublist A →
        PhaseMergeRefinement.Good loc F B Q v z lam eta ((C++R)++[f]) :=
      fun R hR => hval R (List.Sublist.cons i hR)
    have ht := ih (fun j hj => hreg j (List.mem_cons_of_mem _ hj)) hg
    have hs := Edit.paidDelete (loc := loc) (B := B) (Q := Q) C (A++[f]) i hi
    have hs' : Adjacent loc F B Q ((C++A)++[f]) ((C++i::A)++[f]) :=
      Or.inr (by simpa only [List.append_assoc,List.cons_append] using hs)
    exact ht.append (.cons ht.last_good hs' (.nil (hval _ (List.Sublist.refl _))))

def removeVertices (C T A : List X) (f : X) : List (List X) :=
  ((C++T)++[f]) :: (growSuffix (C++T) f A ++ [(C++T)++A])

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma removeVertices_length (C T A : List X) (f : X) :
    (removeVertices C T A f).length=A.length+2 := by
  simp only [removeVertices,List.length_cons,List.length_nil,List.length_append,growSuffix_length]

 theorem removeVertices_spec (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hQ : Q ⊆ F ∪ B) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C T A : List X) (i f : X) (hi : i ∈ F) (hf : f ∉ F ∪ B)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hreg : ∀ j ∈ A, j ∈ F)
    (hbefore : Valid loc F B Q v z lam eta (C++i::T))
    (hafter : Valid loc F B Q v z lam eta ((C++T)++A))
    (hcapb : ((C++i::T).toFinset \ F).card ≤ 1)
    (hcapa : (((C++T)++A).toFinset \ F).card ≤ 1) :
    EPath loc F (insert f B) Q v z lam eta (C++i::T)
      (removeVertices C T A f) ((C++T)++A) := by
  have hfF : f ∉ F := fun h => hf (Finset.mem_union_left _ h)
  have hfH : f ∉ Q ∪ ((C++T)++A).toFinset :=
    fun h => hf ((Finset.union_subset hQ hafter.1.opened_subset) h)
  have hval : ∀ R : List X, R.Sublist A →
      PhaseMergeRefinement.Good loc F (insert f B) Q v z lam eta (((C++T)++R)++[f]) := by
    intro R hR
    refine ⟨delete_suffix_with_copy loc F B Q v z lam eta hv hvsmall hz hlam hrow
      C T A R i f hfH hco hbefore hafter.1 hR,?_⟩
    exact cap_append (hR.append_left (C++T)) hcapa
  have hgrow := growSuffix_spec loc F (insert f B) Q v z lam eta (C++T) A f hreg hval
  have hgoodb : PhaseMergeRefinement.Good loc F (insert f B) Q v z lam eta (C++i::T) :=
    ⟨⟨prefix_free_mono hbefore.1 (Finset.subset_insert f B),hbefore.2⟩,by omega⟩
  have hgooda : PhaseMergeRefinement.Good loc F (insert f B) Q v z lam eta ((C++T)++A) :=
    ⟨⟨prefix_free_mono hafter.1 (Finset.subset_insert f B),hafter.2⟩,by omega⟩
  have hc : Coincident loc F Q (C++i::T) ((C++T)++[f]) := by
    refine ⟨i,f,Q ∪ (C++T).toFinset,hi,hfF,entry_fresh hbefore.1,?_,?_,?_,hco⟩
    · intro hh
      exact hfH ((Finset.union_subset_union_right (by
        intro x hx
        exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (List.mem_toFinset.mp hx))) :
          (C++T).toFinset ⊆ ((C++T)++A).toFinset)) hh)
    · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
    · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_empty,
        Finset.union_insert]
  exact .cons hgoodb (Or.inl (.coincident hc)) (hgrow.append
    (.cons hgrow.last_good (Or.inr (.freeAppend _ i f hi (Finset.mem_insert_self _ _) hco)) (.nil hgooda)))

def Jump.expand (spare : X → X) (G : List X) : Jump X → List (List X)
  | .add _ => [G]
  | .remove C T A i => removeVertices C T A (spare i)
  | .replace _ _ _ => [G]

 theorem expand_spec (loc : D → X) (F B Q : Finset X) (copy spare : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hQ : Q ⊆ F ∪ B) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (J : Jump X) (hacc : accepts F copy H G J)
    (hH : PhaseMergePath.Good loc F B Q copy v z lam eta H)
    (hG : PhaseMergePath.Good loc F B Q copy v z lam eta G) :
    (J.expand spare G).length ≤ F.card+2 ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H (J.expand spare G) G := by
  have hB1 : pool F B copy ⊆ pool F (pool F B copy) spare := subset_pool _ _ _
  have hQ1 : Q ⊆ F ∪ pool F B copy := hQ.trans (Finset.union_subset_union_right (subset_pool _ _ _))
  cases J with
  | add i =>
    simp only [accepts,Jump.source,Jump.target,Jump.labels] at hacc
    rcases hacc with ⟨_,rfl,hi⟩
    refine ⟨by simp only [Jump.expand,List.length_singleton]; omega,?_⟩
    exact .cons (good_of_one hH hB1) (Or.inl (.freeAppend H i (copy i) hi
      (hB1 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))) (hd i hi)))
      (.nil (good_of_one hG hB1))
  | remove C T A i =>
    simp only [accepts,Jump.source,Jump.target,Jump.labels] at hacc
    rcases hacc with ⟨rfl,rfl,hi,hreg⟩
    have hAr := (prefix_append_iff.mp hG.1.1).2
    have hAlen := regular_length hAr hreg
    refine ⟨?_,?_⟩
    · simpa only [Jump.expand,removeVertices_length] using Nat.add_le_add_right hAlen 2
    · have hh := removeVertices_spec loc F (pool F B copy) Q v z lam eta hv hvsmall hz hlam
        hQ1 hrow C T A i (spare i) hi (hs i hi) (he i hi) hreg hH.1 hG.1 hH.2 hG.2
      exact hh.mono_free (insert_subset_pool hi)
  | replace C T i =>
    simp only [accepts,Jump.source,Jump.target,Jump.labels] at hacc
    rcases hacc with ⟨rfl,rfl,hi⟩
    have hc' : Coincident loc F Q (C++i::T) (C++copy i::T) := by
      refine ⟨i,copy i,Q ∪ (C++T).toFinset,hi,?_,entry_fresh hG.1.1,entry_fresh hH.1.1,?_,?_,hd i hi⟩
      · intro hci
        exact hc i hi (Finset.mem_union_left _ hci)
      · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
      · simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
    exact ⟨by simp only [Jump.expand,List.length_singleton]; omega,
      .cons (good_of_one hH hB1) (Or.inr (.coincident hc')) (.nil (good_of_one hG hB1))⟩

def refinePath (F : Finset X) (R : List X) (copy spare : X → X) :
    List X → List (List X) → List (List X)
  | _,[] => []
  | H,G::T =>
    match view F R copy H G with
    | none => G::refinePath F R copy spare G T
    | some J => J.expand spare G ++ refinePath F R copy spare G T

 theorem refinePath_spec (loc : D → X) (F B Q : Finset X) (R : List X) (copy spare : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hR : ∀ i∈F,i∈R) (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    {H G : List X} {T : List (List X)}
    (h : CanonicalMergePath.Path loc F B Q copy v z lam eta H T G) :
    (refinePath F R copy spare H T).length ≤ T.length*(F.card+2) ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H
        (refinePath F R copy spare H T) G := by
  have hB1 : pool F B copy ⊆ pool F (pool F B copy) spare := subset_pool _ _ _
  induction h with
  | nil hg => exact ⟨by simp only [refinePath,List.length_nil,Nat.zero_mul,Nat.le_refl],.nil (good_of_one hg hB1)⟩
  | @cons H G T J hg step tail ih =>
    obtain ⟨V,hV⟩ := view_exists R hR step
    have hacc := view_sound F R copy H G V hV
    have hG := tail.toWalk.first_good
    obtain ⟨hn,hp⟩ := expand_spec loc F B Q copy spare v z lam eta hv hvsmall hz hlam
      hQ hrow hc hd hs he H G V hacc hg hG
    simp only [refinePath,hV,List.length_append,List.length_cons]
    refine ⟨?_,hp.append ih.2⟩
    calc
      (V.expand spare G).length+(refinePath F R copy spare G T).length ≤
          (F.card+2)+T.length*(F.card+2) := Nat.add_le_add hn ih.1
      _ = (T.length+1)*(F.card+2) := by ring

def regularChain (F : Finset X) (R : List X) (complete : Finset X → List X)
    (Q : Finset X) (copy spare : X → X) (H G : List X) : List (List X) :=
  refinePath F R copy spare H (CanonicalMergePath.regularPath complete Q copy G H)

 theorem regularChain_spec (loc : D → X) (F B Q : Finset X) (R : List X) (copy spare : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hcomplete : CanonicalMergePath.CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (heta : 0 ≤ eta) (hR : ∀ i∈F,i∈R) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (hH : Valid loc F B Q v z lam eta H)
    (hG : Valid loc F B Q v z lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) :
    let T := regularChain F R complete Q copy spare H G
    T.length ≤ F.card*(F.card+3)*(F.card+2) ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H T G := by
  obtain ⟨hn,hp⟩ := CanonicalMergePath.regularPath_spec loc F B Q copy v z lam eta complete hcomplete
    hv hvsmall hz hlam heta hQ hdis hrow hc hd G H hGr hHr hG hH
  obtain ⟨hm,ht⟩ := refinePath_spec loc F B Q R copy spare v z lam eta hv hvsmall hz hlam
    hR hQ hrow hc hd hs he hp
  exact ⟨hm.trans (Nat.mul_le_mul_right (F.card+2) hn),ht⟩

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
