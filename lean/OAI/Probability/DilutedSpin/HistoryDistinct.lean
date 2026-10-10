import OAI.Probability.DilutedSpin.TripleMarginal

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

structure HistoryValid (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (P : Finset C) (pos : C → S.Leaf) : Prop where
  loc_inj : Function.Injective loc
  pos_inj : Set.InjOn pos P
  disjoint : ∀ i ∈ U, ∀ c ∈ P, loc i ≠ pos c

lemma HistoryValid.pick_old {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryValid S U loc P pos)
    {c : C} (hc : c ∉ P) {i : ι} (hi : i ∈ U) :
    HistoryValid S (U.erase i) loc (insert c P) (Function.update pos c (loc i)) := by
  refine ⟨h.loc_inj,?_,?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; rfl
    · subst a
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_self,Function.update_of_ne hbc] at hab
      exact False.elim (h.disjoint i hi b hb hab)
    · subst b
      have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_self,Function.update_of_ne hac] at hab
      exact False.elim (h.disjoint i hi a ha hab.symm)
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_of_ne hac,Function.update_of_ne hbc] at hab
      exact h.pos_inj ha hb hab
  · intro j hj a ha
    rcases Finset.mem_erase.mp hj with ⟨hji,hj⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa only [Function.update_self] using (fun e => hji (h.loc_inj e))
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      simpa only [Function.update_of_ne hac] using h.disjoint j hj a ha

omit [DecidableEq ι] in
lemma HistoryValid.pick_fresh {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryValid S U loc P pos)
    {c : C} (hc : c ∉ P) (v : S.Internal) :
    HistoryValid (grow S v) U (fun i => oldLeaf S v (loc i)) (insert c P)
      (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v)) := by
  refine ⟨(oldLeaf_injective S v).comp h.loc_inj,?_,?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; rfl
    · subst a
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_self,Function.update_of_ne hbc] at hab
      exact False.elim (newLeaf_ne_oldLeaf S v (pos b) hab)
    · subst b
      have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_self,Function.update_of_ne hac] at hab
      exact False.elim (newLeaf_ne_oldLeaf S v (pos a) hab.symm)
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_of_ne hac,Function.update_of_ne hbc] at hab
      exact h.pos_inj ha hb (oldLeaf_injective S v hab)
  · intro i hi a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa only [Function.update_self] using (newLeaf_ne_oldLeaf S v (loc i)).symm
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_of_ne hac]
      exact fun e => h.disjoint i hi a ha (oldLeaf_injective S v e)

variable {Ω : Type} [Fintype Ω] [Fintype C]

omit [Fintype Ω] in
/-- A colored history never reuses a position. Thus identities only need to
be proved on terminal tuples of distinct geometric leaves, not sample values. -/
lemma labeledHistory_congr_distinct (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hVW : ∀ S pos f, Function.Injective pos → V S pos f = W S pos f)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (h : HistoryValid S U loc P pos) (f : Sample Ω S → ℝ) :
    labeledHistory m V cs S U loc pos f = labeledHistory m W cs S U loc pos f := by
  induction cs generalizing P S U with
  | nil =>
    apply hVW
    have hp : P = Finset.univ := by simpa using hfull
    exact fun a b e => h.pos_inj (by simp [hp]) (by simp [hp]) e
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact (List.nodup_cons.mp hcs).1 hd
      · exact hdis d (by simp [hd]) hp
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact ih (List.nodup_cons.mp hcs).2 (insert c P) hdis' hfull' S (U.erase i) loc
        (Function.update pos c (loc i)) (h.pick_old hc hi) _
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      exact ih (List.nodup_cons.mp hcs).2 (insert c P) hdis' hfull' (grow S v) U
        (fun i => oldLeaf S v (loc i)) _ (h.pick_fresh hc v) _

lemma anchorHistory_valid (S : PrescribedTree n) (anchor : S.Leaf) {k : ℕ} :
    HistoryValid S (Finset.univ.erase anchor) id ({none} : Finset (Option (Fin k))) (fun _ => anchor) := by
  refine ⟨Function.injective_id,?_,?_⟩
  · intro a ha b hb _
    simp only [Finset.mem_coe,Finset.mem_singleton] at ha hb
    exact ha.trans hb.symm
  · intro i hi c _
    exact (Finset.mem_erase.mp hi).1

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
