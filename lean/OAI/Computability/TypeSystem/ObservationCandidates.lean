import OAI.Computability.TypeSystem.ObservationReduction

namespace OAI

namespace PureTypeSystem.ObservationValues

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- Normalizing the generic expression before a raw typed substitution leaves
its actual normal form unchanged. -/
theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    (A.normalForm.subst e.images).normalForm = (A.subst e.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst (hA.normalForm hw) e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
    (.symm _ _ ((Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts.subst e.images))

noncomputable def normalRead {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    Candidate Ω (A.subst e.images).normalForm :=
  ⟨(preEvaluate Ω C hno (TypingTree.ofTyping (hA.normalForm hw)) e).read.val,
    normal_subst_eq Ω C hno hA e ▸ (preEvaluate Ω C hno (TypingTree.ofTyping (hA.normalForm hw)) e).read.property⟩

theorem normalRead_eq {Γ : List (Expr S)} {A : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (t : TypingTree P Γ A.normalForm (.sort r))
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEvaluate Ω C hno t e).read.val :=
  (normal_tree_independence Ω C hno _ (Expr.normalForm_spec (hA.weaklyNormalizing hw)).2 t e).2 s r rfl rfl

theorem preEvaluate_read_cast_expr {Γ : List (Expr S)} {M N T : Expr S}
    (he : M = N) (t : TypingTree P Γ M T)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (preEvaluate Ω C hno (he ▸ t) e).read.val = (preEvaluate Ω C hno t e).read.val := by
  subst N
  rfl

theorem normalRead_eq_of_nf {Γ : List (Expr S)} {A N : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (t : TypingTree P Γ N (.sort r)) (hn : A.normalForm = N)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEvaluate Ω C hno t e).read.val :=
  (normalRead_eq Ω C hno hA (hn.symm ▸ t) e).trans
    (preEvaluate_read_cast_expr Ω C hno hn.symm t e)

theorem normalRead_congr {Γ : List (Expr S)} {A B : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort r)) (hc : Converts A B)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hB e).val := by
  have he := Expr.normalForm_converts (hA.weaklyNormalizing hw) (hB.weaklyNormalizing hw) hc
  exact normalRead_eq_of_nf Ω C hno hA (TypingTree.ofTyping (hB.normalForm hw)) he e

theorem read_outside {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    (e : Environment (hw := hw) Ω C hno Γ) (ho : Ω.profile (M.subst e.images).normalForm ∉ C) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).normalForm := by
  cases t <;> simp only [preEvaluate,PreResult.lookup,PreResult.sort,PreResult.product,
    PreResult.abstraction,PreResult.application,PreResult.baseResult,PreResult.baseRead,ho,ite_false,dite_false]

theorem normalRead_outside {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (ho : Ω.profile (A.subst e.images) ∉ C) :
    (normalRead Ω C hno hA e).val = Candidates.Top Ω (A.subst e.images).normalForm := by
  have hh := read_outside Ω C hno (TypingTree.ofTyping (hA.normalForm hw)) e (by
    rw [normal_subst_eq Ω C hno hA e,Ω.profile_normalForm]; exact ho)
  exact hh.trans (congrArg (Candidates.Top Ω) (normal_subst_eq Ω C hno hA e))

theorem normalRead_sort {Γ : List (Expr S)} {s r : S}
    (hs : HasType P Γ (.sort s) (.sort r)) (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hs e).val = Candidates.Top Ω (.sort s) := by
  obtain ⟨t,ha,hc⟩ := hs.generation
  let tree : TypingTree P Γ (.sort s) (.sort r) := .sort hs ha hc
  exact (normalRead_eq_of_nf Ω C hno hs tree (Expr.normalForm_of_normal (Normal.sort s)) e).trans (by
    simp only [tree,preEvaluate,PreResult.sort,Expr.subst,Expr.normalForm_of_normal (Normal.sort s)])

/-- The component entry is generic-normal Read; other generic profiles and
unsorted literal expected sorts use exactly typed top. -/
noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ) : Set (Expr S) :=
  if Profile P Γ A ∈ C then
    if hs : ∃ s, HasType P Γ A (.sort s) then (normalRead Ω C hno hs.choose_spec e).val
    else Candidates.Top Ω (A.subst e.images).normalForm
  else Candidates.Top Ω (A.subst e.images).normalForm

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ) :
    Candidates.IsCandidate Ω (A.subst e.images).normalForm (R Ω C hno A e) := by
  unfold R
  split
  · split
    · exact (normalRead Ω C hno _ e).property
    · exact Candidates.top_candidate
  · exact Candidates.top_candidate

theorem R_of_sorted {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hg : Profile P Γ A ∈ C) :
    R Ω C hno A e = (normalRead Ω C hno hA e).val := by
  simp only [R,hg,dite_true,show ∃ s, HasType P Γ A (.sort s) from ⟨s,hA⟩]
  exact normalRead_congr Ω C hno _ hA (.refl _) e

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ)
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C hno A e = Candidates.Top Ω (A.subst e.images).normalForm := by
  unfold R
  split_ifs with hg hs
  · exact normalRead_outside Ω C hno hs.choose_spec e (ho.resolve_left (not_not.mpr hg))
  · rfl
  · rfl

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment (hw := hw) Ω C hno Γ) :
    R Ω C hno (.sort s) e = Candidates.Top Ω (.sort s) := by
  unfold R
  split_ifs with hg hs
  · exact normalRead_sort Ω C hno hs.choose_spec e
  · simp only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]
  · simp only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]

namespace Environment
variable {Ω C hno}
noncomputable def ofImages {Γ : List (Expr S)} (σ : Nat → Expr S)
    (hσ : Ω.TypedSubstitution Γ σ) : Environment (hw := hw) Ω C hno Γ where
  images := σ
  typed := hσ
  parameters := fun i => if hi : ∃ A, Lookup Γ i A then
    (PayloadFits.exists_of_actual (hno := hno) ⟨_,(hσ _ _ hi.choose_spec).actual_type hw⟩).choose else none
  lawful := by
    intro i A hi
    simp only [dite_eq_left (show ∃ B, Lookup Γ i B from ⟨A,hi⟩)]
    have he := Lookup.unique (show Lookup Γ i (Exists.choose (show ∃ B, Lookup Γ i B from ⟨A,hi⟩)) from
      (show ∃ B, Lookup Γ i B from ⟨A,hi⟩).choose_spec) hi
    simpa only [he] using (PayloadFits.exists_of_actual (hno := hno)
      ⟨_,(hσ _ _ (show ∃ B, Lookup Γ i B from ⟨A,hi⟩).choose_spec).actual_type hw⟩).choose_spec

def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.parameters (i+1) = e.parameters i

theorem Ext.reindexed {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : e.Reindexed f Nat.succ := by
  intro i _
  exact ⟨(congrFun he.1 (i+1)).symm,(he.2 i).symm⟩

theorem cons_ext {Γ : List (Expr S)} {D n : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (hn : Ω.HasType n (D.subst e.images)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (D.subst e.images).normalForm p) : e.Ext (e.cons hn p hp) n :=
  ⟨rfl,fun _ => rfl⟩

theorem extend_exists {Γ : List (Expr S)} {D n : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (hn : Ω.HasType n (D.subst e.images)) : ∃ f : Environment (hw := hw) Ω C hno (D :: Γ), e.Ext f n := by
  obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hno := hno) ⟨_,hn.actual_type hw⟩
  exact ⟨e.cons hn p hp,e.cons_ext hn p hp⟩
theorem ext_data {Γ : List (Expr S)} {e f : Environment (hw := hw) Ω C hno Γ}
    (hi : e.images = f.images) (hp : e.parameters = f.parameters) : e = f := by
  cases e; cases f
  cases hi; cases hp
  rfl

theorem Ext.payload {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : PayloadFits Ω C hno (D.subst e.images).normalForm (f.parameters 0) := by
  have hp := f.lawful 0 _ (.zero D Γ)
  simpa only [he.1,Expr.subst_raise_extend] using hp

theorem Ext.eq_cons {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) (hn : Ω.HasType n (D.subst e.images)) :
    f = e.cons hn (f.parameters 0) he.payload := by
  apply ext_data he.1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i

end Environment

theorem R_sorted_conversion {Γ : List (Expr S)} {A B : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort r)) (hc : Converts A B)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno B e := by
  have hp := Profile.converts (P := P) (Γ := Γ) (hA.weaklyNormalizing hw) (hB.weaklyNormalizing hw) hc
  by_cases ha : Profile P Γ A ∈ C
  · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno hB e (hp ▸ ha)]
    exact normalRead_congr Ω C hno hA hB hc e
  · rw [R_outside Ω C hno A e (.inl ha),R_outside Ω C hno B e (.inl (hp ▸ ha))]
    exact congrArg (Candidates.Top Ω) (Expr.normalForm_converts
      ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hB e.typed).weaklyNormalizing hw) (hc.subst e.images))

theorem R_normalForm {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno A.normalForm e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.normalForm_of_normal (Normal.sort s)]
  · exact R_sorted_conversion Ω C hno hA (hA.normalForm hw)
      (Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts e

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno B e := by
  rw [R_normalForm Ω C hno hA e,R_normalForm Ω C hno hB e,
    Expr.normalForm_converts (hA.wn hw) (hB.wn hw) hc]

theorem normalRead_weaken {Γ : List (Expr S)} {A D : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (hD : HasType P Γ D (.sort r))
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    {n : Expr S} (he : e.Ext f n) :
    (normalRead Ω C hno (HasType.weaken hA hD) f).val = (normalRead Ω C hno hA e).val := by
  let t := TypingTree.ofTyping (hA.normalForm hw)
  have hh := normalRead_eq_of_nf Ω C hno (HasType.weaken hA hD)
    (t.rename (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken D))
    (Expr.normalForm_rename (hA.weaklyNormalizing hw) Nat.succ) f
  exact hh.trans (preEvaluate_rename Ω C hno t (.cons hD.valid hD) Nat.succ
    (TypingTree.DeclRenaming.weaken D) e f he.reindexed).2.symm

theorem R_weakening {Γ : List (Expr S)} {A D : Expr S} {r : S}
    (hA : Expected P Γ A) (hD : HasType P Γ D (.sort r))
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    {n : Expr S} (he : e.Ext f n) : R Ω C hno (A.rename Nat.succ) f = R Ω C hno A e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s f).trans (R_sort Ω C hno s e).symm
  · have hp := Profile.weaken hw hA hD
    by_cases ha : Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno (HasType.weaken hA hD) f (hp ▸ ha),R_of_sorted Ω C hno hA e ha]
      exact normalRead_weaken Ω C hno hA hD he
    · rw [R_outside Ω C hno _ f (.inl (hp ▸ ha)),R_outside Ω C hno _ e (.inl ha),
        he.1,Expr.subst_raise_extend]

theorem normalRead_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (h : ContextEquivalent P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.SameData f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno ((h.typing _ _).mp hA) f).val := by
  let t := TypingTree.ofTyping (hA.normalForm hw)
  exact (preEvaluate_recontext Ω C hno t h e f he).2.trans
    (normalRead_eq Ω C hno ((h.typing _ _).mp hA) (t.recontext h) f).symm

theorem R_recontext {Γ Δ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (h : ContextEquivalent P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.SameData f) : R Ω C hno A e = R Ω C hno A f := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · have hp : Profile P Γ A = Profile P Δ A := by
      ext s; exact h.typing _ _
    by_cases ha : Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno ((h.typing _ _).mp hA) f (hp ▸ ha)]
      exact normalRead_recontext Ω C hno hA h e f he
    · rw [R_outside Ω C hno _ e (.inl ha),R_outside Ω C hno _ f (.inl (hp ▸ ha)),he.1]

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem R_eq_normalRead_relevant {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = (normalRead Ω C hno hA e).val := by
  by_cases hg : Profile P Γ A ∈ C
  · exact R_of_sorted Ω C hno hA e hg
  · have ha : Ω.profile (A.subst e.images) ∉ C := fun ha =>
      hg (relevant_actual_mem Ω C hw hC hA e.typed hr ha)
    exact (R_outside Ω C hno A e (.inl hg)).trans (normalRead_outside Ω C hno hA e ha).symm

theorem R_eq_read_normal {Γ : List (Expr S)} {A : Expr S} {s : S}
    (t : TypingTree P Γ A (.sort s)) (hn : Normal A) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = (preEvaluate Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (normalRead_eq_of_nf Ω C hno t.typing t (Expr.normalForm_of_normal hn) e)

theorem R_eq_read_good {Γ : List (Expr S)} {A : Expr S} {s : S}
    (t : TypingTree P Γ A (.sort s)) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) (hg : ReadGood Ω C t e.images) :
    R Ω C hno A e = (preEvaluate Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (good_normal_read Ω C hno hC t (TypingTree.ofTyping (t.typing.normalForm hw)) e hg).symm

theorem normal_product_candidate {Γ : List (Expr S)} {D E : Expr S} {a b c : S}
    (d : TypingTree P Γ D (.sort a)) (q : TypingTree P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hn : Normal (.pi D E)) (hg : Profile P Γ (.pi D E) ∈ C)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) :
    R Ω C hno (.pi D E) e = (PreResult.productCandidate d.typing q.typing hr
      (preEvaluate Ω C hno d) (preEvaluate Ω C hno q) e).val := by
  let t : TypingTree P Γ (.pi D E) (.sort c) :=
    .product (.product d.typing q.typing hr) d q hr (.refl _)
  have he := R_eq_read_normal Ω C hno hC t hn ⟨_,hg,.refl _⟩ e
  exact he.trans (by
    simp only [t,preEvaluate,PreResult.product,Ω.profile_normalForm,ha,ite_true])

theorem normal_product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hn : Normal (.pi D E))
    (hg : Profile P Γ (.pi D E) ∈ C) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let d := TypingTree.ofTyping hD
  let q := TypingTree.ofTyping hE
  let t := PreResult.productData hD hE hr e
  let bd : t.BodyReads := fun n hn p hp => (preEvaluate Ω C hno q (t.extend hn p hp)).read
  have hf := Profile.triple hw hp
  have hdrel : Relevant (P := P) C Γ D := ⟨_,hg,.single (.domain hf)⟩
  have herel : Relevant (P := P) C (D :: Γ) E := ⟨_,hg,.single (.codomain hf)⟩
  have hrd := R_eq_read_normal Ω C hno hC d hn.pi_domain hdrel e
  have htest : t.testers (preEvaluate Ω C hno d e).read = R Ω C hno D e := by
    unfold ProductInstance.testers
    split_ifs with hc
    · exact hrd.symm
    · exact (R_outside Ω C hno D e (.inr (by simpa only [t,PreResult.productData,
        ProductInstance.domainNF,ProductInstance.rawDomain,Ω.profile_normalForm] using hc))).symm
  have hre : ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
      R Ω C hno E f = (preEvaluate Ω C hno q f).read.val :=
    fun f => R_eq_read_normal Ω C hno hC q hn.pi_body herel f
  rw [normal_product_candidate Ω C hno hC d q hr hn hg e ha]
  change h ∈ (t.candidate (preEvaluate Ω C hno d e).read bd).val ↔ _
  constructor
  · intro hh
    refine ⟨?_,?_⟩
    · exact t.product_nf.symm ▸ hh.1
    · intro n hnr f he
      have hnt : n ∈ t.testers (preEvaluate Ω C hno d e).read := htest.symm ▸ hnr
      have hnty := (t.testers_top _ hnt).1
      have hfcons := he.eq_cons (t.rawArgument hnty)
      rw [hfcons,hre]
      by_cases hc : Ω.profile (t.targetNF n) ∈ C
      · exact t.candidate_body _ bd hh hnt hc (f.parameters 0) he.payload
      · have hout := t.candidate_outside _ bd hh hnt hc
        have heo := read_outside Ω C hno q (t.extend hnty (f.parameters 0) he.payload) hc
        exact heo.symm ▸ hout
  · rintro ⟨hht,hbody⟩
    refine ⟨t.product_nf ▸ hht,?_⟩
    intro n hn U hU
    have hnty := (t.testers_top _ hn).1
    have hnr : n ∈ R Ω C hno D e := htest ▸ hn
    simp only [ProductInstance.fibers,hnty,dite_true] at hU
    split_ifs at hU with hc
    · obtain ⟨p,hp,rfl⟩ := hU
      rw [← hre]
      exact hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
    · have heU : U = Candidates.Top Ω (t.targetNF n) := hU
      rw [heU]
      obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hno := hno) ⟨_,(t.rawArgument hnty).actual_type hw⟩
      have hmem := hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
      rw [hre,read_outside Ω C hno q (t.extend hnty p hp) hc] at hmem
      exact hmem

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno}
theorem Ext.argument {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : Ω.HasType n (D.subst e.images) := by
  have hh := f.typed 0 _ (.zero D Γ)
  simpa only [he.1,Expr.extend_zero,Expr.subst_raise_extend] using hh

theorem Ext.convert_domain {Γ : List (Expr S)} {D D' n : Expr S} {a b : S}
    (hD : HasType P Γ D (.sort a)) (hD' : HasType P Γ D' (.sort b)) (hc : Converts D D')
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : ∃ g : Environment (hw := hw) Ω C hno (D' :: Γ), e.Ext g n ∧ f.SameData g := by
  have ht := ContextTower.HasType.subst hD' e.typed
  have hnf := Expr.normalForm_converts ((ContextTower.HasType.subst hD e.typed).weaklyNormalizing hw)
    (ht.weaklyNormalizing hw) (hc.subst e.images)
  have hn := he.argument.conversion ht (hc.subst e.images)
  let g := e.cons hn (f.parameters 0) (hnf ▸ he.payload)
  refine ⟨g,e.cons_ext hn _ _,he.1,?_⟩
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i
end Environment

theorem normalRead_compatible (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {A : Expr S} {s : S} (hA : HasType P Γ A (.sort s))
    (e f : Environment (hw := hw) Ω C hno Γ) (he : e.Compatible f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hA f).val :=
  (preEvaluate_compatible Ω C hno hC (TypingTree.ofTyping (hA.normalForm hw)) e f he).2

theorem R_compatible (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e f : Environment (hw := hw) Ω C hno Γ) (he : e.Compatible f) :
    R Ω C hno A e = R Ω C hno A f := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · by_cases hc : Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e hc,R_of_sorted Ω C hno hA f hc]
      exact normalRead_compatible Ω C hno hC hA e f he
    · rw [R_outside Ω C hno A e (.inl hc),R_outside Ω C hno A f (.inl hc),
        e.actual_expr_eq he.1 hA]

theorem R_binder_conversion {Γ : List (Expr S)} {D D' E E' n : Expr S} {a b s r : S}
    (hD : HasType P Γ D (.sort a)) (hD' : HasType P Γ D' (.sort b)) (hc : Converts D D')
    (hE : HasType P (D :: Γ) E (.sort s)) (hE' : HasType P (D' :: Γ) E' (.sort r))
    (hh : Converts E E') (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno (D :: Γ)) (g : Environment (hw := hw) Ω C hno (D' :: Γ))
    (_he : e.Ext f n) (_he' : e.Ext g n) (heq : f.SameData g) :
    R Ω C hno E f = R Ω C hno E' g := by
  let hctx := ContextEquivalent.head_conversion hD hD' hc
  exact (R_recontext Ω C hno (.sorted hE) hctx f g heq).trans
    (R_sorted_conversion Ω C hno ((hctx.typing _ _).mp hE) hE' hh g)

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hDN := hD.normalForm hw
  have hEN := hE.normalForm hw
  have cD := (Expr.normalForm_spec (hD.weaklyNormalizing hw)).1.converts
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  let ctx := ContextEquivalent.head_conversion hD hDN cD
  have hEN' := (ctx.typing _ _).mp hEN
  have hpn : HasType P Γ (.pi D.normalForm E.normalForm) (.sort c) := .product hDN hEN' hr
  have nc := Converts.pi cD cE
  have hn : Normal (.pi D.normalForm E.normalForm) := .pi
    (Expr.normalForm_spec (hD.weaklyNormalizing hw)).2 (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2
  have hprof := Profile.converts (P := P) (Γ := Γ) (hp.weaklyNormalizing hw) (hpn.weaklyNormalizing hw) nc
  have haprof := Ω.profile_converts ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hpn e.typed).weaklyNormalizing hw) (nc.subst e.images)
  have hnf := Expr.normalForm_converts ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hpn e.typed).weaklyNormalizing hw) (nc.subst e.images)
  have hR := R_sorted_conversion Ω C hno hp hpn nc e
  have hRD := R_normalForm Ω C hno (.sorted hD) e
  rw [hR,normal_product_iff Ω C hno hC hpn hn (hprof ▸ hg) e (haprof ▸ ha) h,hnf]
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr f he
    obtain ⟨g,heg,hfg⟩ := he.convert_domain hD hDN cD
    have hmem := hbody n (hRD ▸ hnr) g heg
    have heq := R_binder_conversion Ω C hno hD hDN cD hE hEN' cE e f g he heg hfg
    exact heq.symm ▸ hmem
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr g heg
    obtain ⟨f,hef,hgf⟩ := heg.convert_domain hDN hD (.symm _ _ cD)
    have hmem := hbody n (hRD.symm ▸ hnr) f hef
    have heq := R_binder_conversion Ω C hno hD hDN cD hE hEN' cE e f g hef heg ⟨hgf.1.symm,hgf.2.symm⟩
    exact heq ▸ hmem

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment (hw := hw) Ω C hno Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (h : Expr S) (ht : h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).normalForm)
    (hb : ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
      e.Ext f n → Expr.app h n ∈ R Ω C hno E f) : h ∈ R Ω C hno (.pi D E) e :=
  (product_iff Ω C hno hC hp hg e ha h).mpr ⟨ht,hb⟩

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem product_argument_active {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hN : HasType P Γ N D)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hpC : Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC : Ω.profile ((E.instantiate N).subst e.images) ∈ C)
    (hD : Ω.profile (D.subst e.images) ∈ ObservationLayers P C) :
    ActiveLayer P C (Ω.profile (D.subst e.images)) := by
  obtain ⟨J,hf,hpath⟩ := Ω.frame_profiles hw (ContextTower.HasType.subst hp e.typed)
    (ContextTower.HasType.subst hN e.typed)
  have hJC : J ∈ C := hC.between (by simpa only [Expr.instantiate_subst] using hNC)
    hpC hpath.reach (.single (.codomain hf))
  exact ⟨_,⟨hD,J,hJC,_,hpC,hf⟩,.refl _⟩

theorem R_instantiate_normal {Γ : List (Expr S)} {D E N : Expr S} {a b c : S}
    (hD : HasType P Γ D (.sort a)) (hE : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (n : TypingTree P Γ N D) (hnE : Normal E) (hnN : Normal N)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC : Ω.profile ((E.instantiate N).subst e.images) ∈ C) :
    R Ω C hno E (e.cons (ContextTower.HasType.subst n.typing e.typed)
      (preEvaluate Ω C hno n e).parameter (preEvaluate Ω C hno n e).parameter_fits) =
    R Ω C hno (E.instantiate N) e := by
  let q := TypingTree.ofTyping hE
  let f := e.cons (ContextTower.HasType.subst n.typing e.typed)
    (preEvaluate Ω C hno n e).parameter (preEvaluate Ω C hno n e).parameter_fits
  let ts := TypingTree.StoredSubstitution.single n
  let qt := q.subst hD.valid (Expr.single N) ts
  have hp := HasType.product hD hE hr
  have hrel : Relevant (P := P) C (D :: Γ) E := ⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hrelN : Relevant (P := P) C Γ (E.instantiate N) :=
    ⟨_,hg,(Profile.instantiate_product_path hw hp n.typing).reach⟩
  have hgood : ReadGood Ω C q f.images := (normal_good Ω C hw hC q hnE f.images f.typed).2 b rfl hrel
  have hgN : ActiveLayer P C (Ω.profile (D.subst e.images)) → ValGood Ω C n e.images :=
    (normal_good Ω C hw hC n hnN e.images e.typed).1
  have hguard : SubstitutionGuard Ω C (D :: Γ) (Expr.single N) f.images :=
    single_guard Ω C e.images (product_argument_active Ω C hno hC hp n.typing e ha hNC)
  have hfi : f.images = Expr.consSub (N.subst e.images) e.images := by
    funext i; cases i <;> rfl
  have hgR := single_goodReplacement Ω C n e.images hgN
  have hgood' : ReadGood Ω C qt e.images := (goodness_subst Ω C hw q hD.valid (Expr.single N) ts
    e.images e.typed (by simpa only [Expr.comp_single,←hfi] using hguard) hgR).2
      (by simpa only [Expr.comp_single,←hfi] using hgood)
  have heval := (preEvaluate_subst Ω C hno q hD.valid (Expr.single N) ts f e
    (single_assigned Ω C hno n e) hguard).2 hgood
  exact (R_eq_read_normal Ω C hno hC q hnE hrel f).trans (heval.trans
    (R_eq_read_good Ω C hno hC qt hrelN e hgood').symm)

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment (hw := hw) Ω C hno Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hN : HasType P Γ N D) (hg : Profile P Γ (.pi D E) ∈ C)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C hno (.pi D E) e) (hn : N.subst e.images ∈ R Ω C hno D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hNN := hN.normalForm hw
  let n := TypingTree.ofTyping hNN
  let pn := (preEvaluate Ω C hno n e).parameter
  have pp := (preEvaluate Ω C hno n e).parameter_fits
  let f := e.cons (ContextTower.HasType.subst hN e.typed) pn pp
  let g := e.cons (ContextTower.HasType.subst hNN e.typed) pn pp
  have hm := ((product_iff Ω C hno hC hp hg e ha h).mp hh).2 (N.subst e.images) hn f
    (e.cons_ext _ pn pp)
  have hnE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2
  have hnN := (Expr.normalForm_spec (hN.weaklyNormalizing hw)).2
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  have cN := (Expr.normalForm_spec (hN.weaklyNormalizing hw)).1.converts
  have hp' : HasType P Γ (.pi D E.normalForm) (.sort c) := .product hD (hE.normalForm hw) hr
  have cP : Converts (.pi D E) (.pi D E.normalForm) := .pi (.refl _) cE
  have cT : Converts (E.instantiate N) (E.normalForm.instantiate N.normalForm) :=
    .trans _ _ _ (cE.subst (Expr.single N)) (cN.instantiate_right E.normalForm)
  have hT := hE.instantiate hN
  have hT' := (hE.normalForm hw).instantiate hNN
  have hRT := R_sorted_conversion Ω C hno hT hT' cT e
  by_cases htC : Ω.profile ((E.normalForm.instantiate N.normalForm).subst e.images) ∈ C
  · have hgg := Profile.converts (P := P) (Γ := Γ) (hp.weaklyNormalizing hw) (hp'.weaklyNormalizing hw) cP
    have haa := Ω.profile_converts ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hp' e.typed).weaklyNormalizing hw) (cP.subst e.images)
    have hfg : f.Compatible g := by
      constructor
      · intro i hi
        cases i with
        | zero => exact cN.subst e.images
        | succ i => exact .refl _
      · intro i hi; cases i <;> rfl
    have hrE := (R_normalForm Ω C hno (.sorted hE) f).trans
      ((R_compatible Ω C hno hC (.sorted (hE.normalForm hw)) f g hfg).trans
      (R_instantiate_normal Ω C hno hC hD (hE.normalForm hw) hr n hnE hnN e (hgg ▸ hg) (haa ▸ ha) htC))
    exact hRT.symm ▸ (hrE ▸ hm)
  · have hmem := (R_candidate Ω C hno E f).upper hm
    have he : (E.subst f.images).normalForm = ((E.instantiate N).subst e.images).normalForm := by
      congr 1
      rw [← Expr.instantiate_subst,Expr.instantiate_liftSub]
      rfl
    have hnf := Expr.normalForm_converts ((ContextTower.HasType.subst hT e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hT' e.typed).weaklyNormalizing hw) (cT.subst e.images)
    rw [hRT,R_outside Ω C hno _ e (.inr htC)]
    exact (hnf ▸ he ▸ hmem)

end

universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- The actual observation interpretation, with arbitrary typed raw images and
all matching payload extensions. No component interface law is assumed. -/
noncomputable def componentInterface (hC : IsComponent (PrimaryEdge P) C) : ComponentInterface Ω hw C where
  Env := Environment (hw := hw) Ω C hno
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨Environment.ofImages σ hσ,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ _ hn := e.extend_exists hn
  R := R Ω C hno
  candidate e _ := R_candidate Ω C hno _ e
  conversion e ha hb hc := R_conversion Ω C hno ha hb hc e
  outside e _ ho := R_outside Ω C hno _ e ho
  weakening hd he hx := R_weakening Ω C hno he hd hx
  product_intro e hp hg ha h ht hb := product_intro Ω C hno hC e hp hg ha h ht hb
  specialization e hp hN hg ha h hh hn := specialization Ω C hno hC e hp hN hg ha h hh hn

end PureTypeSystem.ObservationValues

end OAI
