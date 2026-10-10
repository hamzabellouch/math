import OAI.Computability.TypeSystem.Typing

namespace OAI

namespace PureTypeSystem

universe u

namespace Expr

variable {S T U : Type u}

def mapSort (f : S → T) : Expr S → Expr T
  | var n => var n
  | sort s => sort (f s)
  | app M N => app (mapSort f M) (mapSort f N)
  | lam A M => lam (mapSort f A) (mapSort f M)
  | pi A B => pi (mapSort f A) (mapSort f B)

@[simp] theorem mapSort_id (M : Expr S) : M.mapSort id = M := by
  induction M <;> simp_all only [mapSort, id_eq]

@[simp] theorem mapSort_comp (M : Expr S) (f : S → T) (g : T → U) :
    (M.mapSort f).mapSort g = M.mapSort (g ∘ f) := by
  induction M <;> simp_all only [mapSort, Function.comp_apply]

@[simp] theorem mapSort_rename (M : Expr S) (f : S → T) (ρ : Nat → Nat) :
    (M.rename ρ).mapSort f = (M.mapSort f).rename ρ := by
  induction M generalizing ρ <;> simp_all only [mapSort, rename]

@[simp] theorem mapSort_liftSub (f : S → T) (σ : Nat → Expr S) :
    mapSort f ∘ liftSub σ = liftSub (mapSort f ∘ σ) := by
  funext n
  cases n <;> simp only [Function.comp_apply, liftSub, mapSort, mapSort_rename]

@[simp] theorem mapSort_subst (M : Expr S) (f : S → T) (σ : Nat → Expr S) :
    (M.subst σ).mapSort f = (M.mapSort f).subst (mapSort f ∘ σ) := by
  induction M generalizing σ <;>
    simp_all only [mapSort, subst, Function.comp_apply, mapSort_liftSub]

@[simp] theorem mapSort_single (f : S → T) (a : Expr S) :
    mapSort f ∘ single a = single (a.mapSort f) := by
  funext n
  cases n <;> rfl

@[simp] theorem mapSort_instantiate (b a : Expr S) (f : S → T) :
    (b.instantiate a).mapSort f = (b.mapSort f).instantiate (a.mapSort f) := by
  simp only [instantiate, mapSort_subst, mapSort_single]

end Expr

namespace Beta

variable {S T : Type u} {M N : Expr S}

theorem mapSort (h : Beta M N) (f : S → T) : Beta (M.mapSort f) (N.mapSort f) := by
  induction h with
  | head A b a =>
      simpa only [Expr.mapSort, Expr.mapSort_instantiate] using
        (Beta.head (A.mapSort f) (b.mapSort f) (a.mapSort f))
  | app_left _ ih => exact .app_left ih
  | app_right _ ih => exact .app_right ih
  | lam_domain _ ih => exact .lam_domain ih
  | lam_body _ ih => exact .lam_body ih
  | pi_domain _ ih => exact .pi_domain ih
  | pi_body _ ih => exact .pi_body ih

end Beta

namespace Reduces

variable {S T : Type u} {M N : Expr S}

theorem mapSort (h : Reduces M N) (f : S → T) : Reduces (M.mapSort f) (N.mapSort f) :=
  h.lift (Expr.mapSort f) (fun _ _ h => h.mapSort f)

end Reduces

namespace Converts

variable {S T : Type u} {M N : Expr S}

theorem mapSort (h : Converts M N) (f : S → T) : Converts (M.mapSort f) (N.mapSort f) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.mapSort f)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace Normal

variable {S T : Type u}

theorem mapSort {M : Expr S} (h : Normal M) (f : S → T) : Normal (M.mapSort f) := by
  induction M with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain).pi (ihB h.pi_body)
  | lam A b ihA ihb => exact (ihA h.lam_domain).lam (ihb h.lam_body)
  | app M a ihM iha =>
      have hM := ihM h.app_left
      have ha := iha h.app_right
      cases M with
      | lam D b => exact False.elim (h _ (.head D b a))
      | var n | sort s | app M b | pi D B =>
          intro N hN
          cases hN with
          | app_left hr => exact hM _ hr
          | app_right hr => exact ha _ hr

end Normal

namespace StronglyNormalizing

variable {S T : Type u}

theorem of_mapSort (f : S → T) {M : Expr S} (h : StronglyNormalizing (M.mapSort f)) :
    StronglyNormalizing M := by
  have aux : ∀ N : Expr T, StronglyNormalizing N →
      ∀ M : Expr S, M.mapSort f = N → StronglyNormalizing M := by
    intro N hN
    induction hN with
    | intro N hN ih =>
        intro M he
        subst N
        refine Acc.intro M ?_
        intro M' hM'
        exact ih (M'.mapSort f) (hM'.mapSort f) M' rfl
  exact aux _ h M rfl

end StronglyNormalizing

namespace WeaklyNormalizing

variable {S T : Type u}

theorem mapSort {M : Expr S} (h : WeaklyNormalizing M) (f : S → T) :
    WeaklyNormalizing (M.mapSort f) := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨N.mapSort f, Reduces.mapSort hr f, hn.mapSort f⟩

theorem of_retraction (f : S → T) (g : T → S) (hfg : Function.LeftInverse g f)
    {M : Expr S} (h : WeaklyNormalizing (M.mapSort f)) : WeaklyNormalizing M := by
  have he : g ∘ f = id := funext hfg
  simpa only [Expr.mapSort_comp, he, Expr.mapSort_id] using h.mapSort g

end WeaklyNormalizing

namespace HasType

variable {S T : Type u} {P Q : Specification S}

theorem monotone {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A)
    (ha : ∀ s t, P.axioms s t → Q.axioms s t)
    (hr : ∀ a b c, P.rule a b c → Q.rule a b c) : HasType Q Γ M A := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha => exact .application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA hc

theorem mapSort {Q : Specification T} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) (f : S → T)
    (ha : ∀ s t, P.axioms s t → Q.axioms (f s) (f t))
    (hr : ∀ a b c, P.rule a b c → Q.rule (f a) (f b) (f c)) :
    HasType Q (Γ.map (Expr.mapSort f)) (M.mapSort f) (A.mapSort f) := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => simpa only [List.map_cons, Expr.mapSort, Expr.mapSort_rename] using HasType.var ih
  | weaken _ _ ihM ihA =>
      simpa only [List.map_cons, Expr.mapSort_rename] using HasType.weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha =>
      simpa only [Expr.mapSort, Expr.mapSort_instantiate] using HasType.application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA (hc.mapSort f)

theorem has_axiom {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    ∃ s t, P.axioms s t := by
  induction h with
  | ax h => exact ⟨_, _, h⟩
  | var _ ih => exact ih
  | weaken _ _ ih _ => exact ih
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ ih _ => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType

namespace Specification

variable {S : Type u}

def restrict (P : Specification S) (A : Finset (S × S)) (R : Finset (S × S × S)) :
    Specification S where
  axioms s t := P.axioms s t ∧ (s,t) ∈ A
  rule a b c := P.rule a b c ∧ (a,b,c) ∈ R

def on (P : Specification S) (D : Set S) : Specification D where
  axioms s t := P.axioms s.val t.val
  rule a b c := P.rule a.val b.val c.val

end Specification

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem restrict_mono {A A' : Finset (S × S)} {R R' : Finset (S × S × S)}
    (h : HasType (P.restrict A R) Γ M T) (hA : A ⊆ A') (hR : R ⊆ R') :
    HasType (P.restrict A' R') Γ M T :=
  h.monotone (fun _ _ h => ⟨h.1, hA h.2⟩) (fun _ _ _ h => ⟨h.1, hR h.2⟩)

theorem finite_support (h : HasType P Γ M T) :
    ∃ A : Finset (S × S), ∃ R : Finset (S × S × S), HasType (P.restrict A R) Γ M T := by
  classical
  induction h with
  | ax h => exact ⟨{(_,_)}, ∅, .ax ⟨h, Finset.mem_singleton_self _⟩⟩
  | var _ ih =>
      obtain ⟨A, R, ht⟩ := ih
      exact ⟨A, R, .var ht⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨A, R, hM⟩ := ihM
      obtain ⟨A', R', hA⟩ := ihA
      exact ⟨A ∪ A', R ∪ R', .weaken
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hA.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | @product Γ D E a b c _ _ hr ihD ihE =>
      obtain ⟨A, R, hD⟩ := ihD
      obtain ⟨A', R', hE⟩ := ihE
      refine ⟨A ∪ A', insert (a,b,c) (R ∪ R'), .product
        (hD.restrict_mono Finset.subset_union_left
          (Finset.subset_union_left.trans (Finset.subset_insert _ _)))
        (hE.restrict_mono Finset.subset_union_right
          (Finset.subset_union_right.trans (Finset.subset_insert _ _))) ?_⟩
      exact ⟨hr, Finset.mem_insert_self _ _⟩
  | abstraction _ _ ihb ihPi =>
      obtain ⟨A, R, hb⟩ := ihb
      obtain ⟨A', R', hPi⟩ := ihPi
      exact ⟨A ∪ A', R ∪ R', .abstraction
        (hb.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hPi.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | application _ _ ihf iha =>
      obtain ⟨A, R, hf⟩ := ihf
      obtain ⟨A', R', ha⟩ := iha
      exact ⟨A ∪ A', R ∪ R', .application
        (hf.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (ha.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | conversion _ _ hc ihM ihT =>
      obtain ⟨A, R, hM⟩ := ihM
      obtain ⟨A', R', hT⟩ := ihT
      exact ⟨A ∪ A', R ∪ R', .conversion
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hT.restrict_mono Finset.subset_union_right Finset.subset_union_right) hc⟩

end HasType

namespace SystemWeaklyNormalizing

variable {S : Type u} {P : Specification S}

theorem on {D : Set S} (hw : SystemWeaklyNormalizing P) (d₀ : D) :
    SystemWeaklyNormalizing (P.on D) := by
  classical
  let f : S → D := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have hf : Function.LeftInverse f Subtype.val := by
    intro s
    apply Subtype.ext
    simp only [f, dite_eq_left s.property]
  intro Γ _ M hM
  obtain ⟨A, h | h⟩ := hM
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    exact WeaklyNormalizing.of_retraction Subtype.val f hf
      (hw _ ht.valid _ ⟨_, Or.inl ht⟩)
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    exact WeaklyNormalizing.of_retraction Subtype.val f hf
      (hw _ ht.valid _ ⟨_, Or.inr ht⟩)

end SystemWeaklyNormalizing

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- A non-strongly-normalizing typed term has a counterexample over a finite
subspecification. No normalization conclusion for that finite PTS is assumed. -/
theorem finite_counterexample (h : HasType P Γ M T) (hn : ¬ StronglyNormalizing M)
    (hw : SystemWeaklyNormalizing P) :
    ∃ D : Finset S, ∃ Γ' : List (Expr {s // s ∈ D}),
      ∃ M' T' : Expr {s // s ∈ D},
        HasType (P.on (D : Set S)) Γ' M' T' ∧ ¬ StronglyNormalizing M' ∧
          SystemWeaklyNormalizing (P.on (D : Set S)) := by
  classical
  obtain ⟨A, R, hr⟩ := h.finite_support
  let D := A.biUnion (fun a => {a.1, a.2}) ∪
    R.biUnion (fun r => {r.1, r.2.1, r.2.2})
  have ax_mem {s t : S} (h : (s,t) ∈ A) : s ∈ D ∧ t ∈ D := by
    constructor
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
  have rule_mem {a b c : S} (h : (a,b,c) ∈ R) : a ∈ D ∧ b ∈ D ∧ c ∈ D := by
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
  obtain ⟨s₀, t₀, h₀⟩ := hr.has_axiom
  let d₀ : {s // s ∈ D} := ⟨s₀, (ax_mem h₀.2).1⟩
  let f : S → {s // s ∈ D} := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have f_val {s : S} (h : s ∈ D) : (f s).val = s := by
    simp only [f, dite_eq_left h]
  have ha : ∀ s t, (P.restrict A R).axioms s t →
      (P.on (D : Set S)).axioms (f s) (f t) := by
    intro s t hst
    change P.axioms (f s).val (f t).val
    rw [f_val (ax_mem hst.2).1, f_val (ax_mem hst.2).2]
    exact hst.1
  have hp : ∀ a b c, (P.restrict A R).rule a b c →
      (P.on (D : Set S)).rule (f a) (f b) (f c) := by
    intro a b c habc
    change P.rule (f a).val (f b).val (f c).val
    rw [f_val (rule_mem habc.2).1, f_val (rule_mem habc.2).2.1,
      f_val (rule_mem habc.2).2.2]
    exact habc.1
  exact ⟨D, _, _, _, hr.mapSort f ha hp,
    fun hs => hn (StronglyNormalizing.of_mapSort f hs), hw.on d₀⟩

end HasType

end PureTypeSystem

end OAI
