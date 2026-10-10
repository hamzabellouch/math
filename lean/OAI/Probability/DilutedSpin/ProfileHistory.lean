import OAI.Probability.DilutedSpin.HistoryDistinct
import OAI.Probability.DilutedSpin.PatternComparison

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- Growth adds exactly one new positional leaf, not just one spin value. -/
theorem grow_leaf_cases (S : PrescribedTree n) (v : S.Internal) (b : (grow S v).Leaf) :
    b = newLeaf S v ∨ ∃ a, b = oldLeaf S v a := by
  classical
  let F : Option S.Leaf → (grow S v).Leaf := Option.elim' (newLeaf S v) (oldLeaf S v)
  have hinj : Function.Injective F := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (newLeaf_ne_oldLeaf S v _ h)
    · exact False.elim (newLeaf_ne_oldLeaf S v _ h.symm)
    · exact congrArg some (oldLeaf_injective S v h)
  have hcard : Fintype.card (Option S.Leaf) = Fintype.card (grow S v).Leaf := by
    simp only [Fintype.card_option,card_leaf,leaves_grow]
  have hs := ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj,hcard⟩).2
  obtain ⟨a,rfl⟩ := hs b
  cases a with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a,rfl⟩

/-- The available original positions and the already assigned colors cover
all current leaves. Previously fresh leaves are assigned, never made available. -/
structure HistoryCover (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (P : Finset C) (pos : C → S.Leaf) : Prop extends HistoryValid S U loc P pos where
  cover : ∀ b : S.Leaf, (∃ i ∈ U, b = loc i) ∨ ∃ c ∈ P, b = pos c

lemma HistoryCover.pick_old {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryCover S U loc P pos)
    {c : C} (hc : c ∉ P) {i : ι} (hi : i ∈ U) :
    HistoryCover S (U.erase i) loc (insert c P) (Function.update pos c (loc i)) := by
  refine ⟨h.toHistoryValid.pick_old hc hi,?_⟩
  intro b
  rcases h.cover b with ⟨j,hj,rfl⟩ | ⟨d,hd,rfl⟩
  · by_cases hji : j = i
    · subst j
      exact Or.inr ⟨c,Finset.mem_insert_self _ _,by simp only [Function.update_self]⟩
    · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩,rfl⟩
  · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,?_⟩
    simp only [Function.update_of_ne (fun he : d = c => hc (he ▸ hd))]

omit [DecidableEq ι] in
lemma HistoryCover.pick_fresh {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryCover S U loc P pos)
    {c : C} (hc : c ∉ P) (v : S.Internal) :
    HistoryCover (grow S v) U (fun i => oldLeaf S v (loc i)) (insert c P)
      (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v)) := by
  refine ⟨h.toHistoryValid.pick_fresh hc v,?_⟩
  intro b
  rcases grow_leaf_cases S v b with rfl | ⟨a,rfl⟩
  · exact Or.inr ⟨c,Finset.mem_insert_self _ _,by simp only [Function.update_self]⟩
  · rcases h.cover a with ⟨i,hi,rfl⟩ | ⟨d,hd,rfl⟩
    · exact Or.inl ⟨i,hi,rfl⟩
    · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,?_⟩
      simp only [Function.update_of_ne (fun he : d = c => hc (he ▸ hd))]

lemma anchorHistory_cover (S : PrescribedTree n) (anchor : S.Leaf) {k : ℕ} :
    HistoryCover S (Finset.univ.erase anchor) id ({none} : Finset (Option (Fin k))) (fun _ => anchor) := by
  classical
  refine ⟨anchorHistory_valid S anchor,?_⟩
  intro b
  by_cases h : b = anchor
  · exact Or.inr ⟨none,by simp,h⟩
  · exact Or.inl ⟨b,by simp [h],rfl⟩

omit [DecidableEq C] [DecidableEq ι] in
/-- Available-old sums equal unrestricted old-leaf sums for any observable
that vanishes on the protected references. No probability calculation occurs. -/
lemma HistoryCover.sum_available {S : PrescribedTree n} {U : Finset ι}
    {loc : ι → S.Leaf} {P : Finset C} {pos : C → S.Leaf}
    (h : HistoryCover S U loc P pos) (F : S.Leaf → ℝ)
    (hF : ∀ c ∈ P, F (pos c) = 0) :
    (∑ i ∈ U, F (loc i)) = ∑ b : S.Leaf, F b := by
  classical
  rw [← Finset.sum_image (fun i _ j _ hij => h.loc_inj hij)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  rcases h.cover b with ⟨i,hi,rfl⟩ | ⟨c,hc,rfl⟩
  · exact False.elim (hb (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  · exact hF c hc

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ} {C : Type} [Fintype C] [DecidableEq C]

abbrev SharingIndex (L : ℕ) (C : Type) := C × C × Fin L

def sharingProfile (S : PrescribedTree (L+1)) (pos : C → S.Leaf) : SharingIndex L C → Bool :=
  fun r => decide (r.2.2.val+1 ≤ splitDepth S (pos r.1) (pos r.2.1))

/-- Recover the complete split-depth matrix from interior sharing bits.
The terminal diagonal is known from colors, not from an endpoint mark. -/
def splitFromProfile (y : SharingIndex L C → Bool) (a b : C) : ℕ :=
  if a = b then L+1 else (Finset.univ.filter (fun d : Fin L => y (a,b,d))).card

omit [Fintype C] in
lemma splitFromProfile_eq (S : PrescribedTree (L+1)) (pos : C → S.Leaf)
    (hp : Function.Injective pos) (a b : C) :
    splitFromProfile (sharingProfile S pos) a b = splitDepth S (pos a) (pos b) := by
  unfold splitFromProfile
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    have hlt := splitDepth_lt_of_ne S (pos a) (pos b) (fun e => hab (hp e))
    have he : (Finset.univ.filter (fun d : Fin L => sharingProfile S pos (a,b,d))) =
        Finset.univ.filter (fun d : Fin L => d.val < splitDepth S (pos a) (pos b)) := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,sharingProfile,decide_eq_true_eq]
      omega
    rw [he,Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]

noncomputable def requirementMap (s : Finset (SharingIndex L C)) :
    Fin (Fintype.card s) → SharingIndex L C := fun j => ((Fintype.equivFin s).symm j).1

omit [Fintype C] [DecidableEq C] in
lemma monomial_sharing (s : Finset (SharingIndex L C)) (S : PrescribedTree (L+1))
    (pos : C → S.Leaf) :
    BooleanPolynomial.monomial s (sharingProfile S pos) =
      ∏ j : Fin (Fintype.card s),
        if (requirementMap s j).2.2.val+1 ≤
          splitDepth S (pos (requirementMap s j).1) (pos (requirementMap s j).2.1)
        then (1:ℝ) else 0 := by
  classical
  unfold BooleanPolynomial.monomial BooleanPolynomial.truth sharingProfile
  simp only [decide_eq_true_eq]
  rw [← Finset.prod_attach]
  simpa [requirementMap] using (Fintype.equivFin s).prod_comp (fun j =>
    if (requirementMap s j).2.2.val+1 ≤
      splitDepth S (pos (requirementMap s j).1) (pos (requirementMap s j).2.1) then (1:ℝ) else 0)

variable {Ω : Type} [Fintype Ω] {k : ℕ}

/-- Literal signed extension history with an arbitrary prescribed split-depth
weight. In particular indicator weights encode exact consistent constraints. -/
noncomputable def shapeHistory (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ)
    (spinColor : Option (Fin k) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchor : S.Leaf) (f : Sample Ω S → ℝ) : ℝ := by
  classical
  exact labeledHistory m (fun S pos f =>
    (S.sampleLaw T).expect (fun x => f x * ∏ c, spinColor c (S.pathAt (pos c) x)) *
      F (fun a b => splitDepth S (pos a) (pos b)))
    (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse S
    (Finset.univ.erase anchor) id (fun _ => anchor) f

/-- Full exact splitting constraints reduce to finitely many sharing
histories, using distinct geometric positions throughout every branch. -/
theorem shapeHistory_expansion (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ)
    (spinColor : Option (Fin k) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchor : S.Leaf) (f : Sample Ω S → ℝ) :
    shapeHistory T m F spinColor S anchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        constrainedHistory T m (fun j => (requirementMap s j).1)
          (fun j => (requirementMap s j).2.1) (fun j => (requirementMap s j).2.2.castSucc)
          spinColor S anchor f := by
  classical
  unfold shapeHistory constrainedHistory
  simp_rw [← labeledHistory_mul_left]
  rw [← labeledHistory_sum]
  apply labeledHistory_congr_distinct (P := ({none} : Finset (Option (Fin k))))
  · intro S pos g hp
    have he : (fun a b => splitDepth S (pos a) (pos b)) = splitFromProfile (sharingProfile S pos) := by
      funext a b
      exact (splitFromProfile_eq S pos hp a b).symm
    rw [he,BooleanPolynomial.expansion (fun y => F (splitFromProfile y)) (sharingProfile S pos)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [monomial_sharing]
    simp only [Fin.val_castSucc]
    ring
  · rw [List.nodup_reverse,List.nodup_ofFn]
    exact Option.some_injective _
  · intro c hc
    simp only [List.mem_reverse,List.mem_ofFn] at hc
    obtain ⟨j,rfl⟩ := hc
    simp
  · ext c
    cases c with
    | none => simp
    | some j => simp [List.mem_ofFn]
  · exact anchorHistory_valid S anchor

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
