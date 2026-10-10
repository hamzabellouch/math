import OAI.Combinatorics.ListHadwiger.SamplingBounds

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def cliqueBlowup (G : SimpleGraph V) (m : ℕ) : SimpleGraph (V × Fin m) where
  Adj u v := G.Adj u.1 v.1 ∨ (u.1 = v.1 ∧ u.2 ≠ v.2)
  symm := ⟨by
    intro u v h
    rcases h with h | ⟨h₁,h₂⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h₁.symm,h₂.symm⟩⟩
  loopless := ⟨by intro u; simp⟩

lemma stable_blowup_projection {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {m : ℕ} {S : Finset (V × Fin m)}
    (hS : Stable (cliqueBlowup G m) S) : Stable G (S.image Prod.fst) := by
  classical
  intro v hv w hw hadj
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
  exact hS u hu z hz (Or.inl hadj)

lemma stable_blowup_injOn {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {m : ℕ} {S : Finset (V × Fin m)}
    (hS : Stable (cliqueBlowup G m) S) : Set.InjOn Prod.fst (S : Set (V × Fin m)) := by
  intro u hu v hv huv
  apply Prod.ext huv
  by_contra hn
  exact hS u hu v hv (Or.inr ⟨huv,hn⟩)

lemma Dual.blowup {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (m : ℕ) :
    Dual (cliqueBlowup G m) (fun v => w v.1) := by
  classical
  refine ⟨fun v => hw.1 v.1,?_⟩
  intro S hS
  have hh := hw.2 (S.image Prod.fst) (stable_blowup_projection hS)
  rw [Finset.sum_image (stable_blowup_injOn hS)] at hh
  exact hh

lemma dual_sum_le_colors {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w)
    {Color : Type} [Fintype Color] (c : G.Coloring Color) :
    (∑ v, w v) ≤ Fintype.card Color := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ c w]
  calc
    _ ≤ ∑ _ : Color, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply hw.2
      intro v hv u hu hadj
      exact c.valid hadj ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hu).2.symm)
    _ = _ := by simp

lemma number_le_colorable {G : SimpleGraph V} {k : ℕ} (hc : G.Colorable k) :
    number G ≤ k := by
  classical
  obtain ⟨w,hw,heq⟩ := duality G
  rw [← heq]
  simpa only [Fintype.card_fin] using dual_sum_le_colors hw hc.some

theorem cliqueBlowup_chromatic_lower (G : SimpleGraph V) (m : ℕ) :
    (m : ℝ) * number G ≤ (cliqueBlowup G m).chromaticNumber.toNat := by
  classical
  obtain ⟨w,hw,heq⟩ := duality G
  have hh := dual_sum_le_colors (hw.blowup m)
    (cliqueBlowup G m).colorable_chromaticNumber_of_fintype.some
  rw [← heq]
  simpa only [Fintype.card_fin,Fintype.sum_prod_type,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum] using hh

lemma cliqueBlowup_colorable_rounded {G : SimpleGraph V} {μ : Finset V → ℝ}
    (hμ : Cover G μ) (m : ℕ) :
    (cliqueBlowup G m).Colorable (∑ I, ⌈(m : ℝ)*μ I⌉₊) := by
  classical
  let counts : Finset V → ℕ := fun I => ⌈(m : ℝ)*μ I⌉₊
  let Slots := Σ I : Finset V, Fin (counts I)
  let good (v : V) : Finset Slots := Finset.univ.filter (fun s => v ∈ s.1)
  have hcard (v : V) : (good v).card = ∑ I, if v ∈ I then counts I else 0 := by
    simp only [good,Finset.card_filter]
    change (∑ s : (Σ I : Finset V, Fin (counts I)), if v ∈ s.1 then 1 else 0) = _
    rw [Fintype.sum_sigma]

    apply Finset.sum_congr rfl
    intro I _
    by_cases hv : v ∈ I <;> simp [hv]
  have hlarge (v : V) : m ≤ (good v).card := by
    have hm : (m : ℝ) ≤ ∑ I, if v ∈ I then ((counts I : ℕ) : ℝ) else 0 := by
      calc
        (m : ℝ) ≤ (m : ℝ)*(∑ I, if v ∈ I then μ I else 0) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hμ.2.2 v) (Nat.cast_nonneg m)
        _ = ∑ I, if v ∈ I then (m : ℝ)*μ I else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro I _
          split_ifs <;> simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · exact Nat.le_ceil _
          · exact le_rfl
    rw [hcard]
    exact_mod_cast hm
  have hinj (v : V) : Nonempty (Fin m ↪ good v) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hlarge v)
  let e : (v : V) → Fin m ↪ good v := fun v => (hinj v).some
  let c : V × Fin m → Slots := fun v => (e v.1 v.2).val
  have hc : ∀ {v w : V × Fin m}, (cliqueBlowup G m).Adj v w → c v ≠ c w := by
    intro v w hadj heq
    have hv : v.1 ∈ (c v).1 := (Finset.mem_filter.mp (e v.1 v.2).property).2
    have hw : w.1 ∈ (c v).1 := by
      rw [heq]
      exact (Finset.mem_filter.mp (e w.1 w.2).property).2
    have stable : Stable G (c v).1 := by
      by_contra hn
      have hzero : counts (c v).1 = 0 := by simp [counts,hμ.2.1 _ hn]
      have hslot := (c v).2.isLt
      exact Nat.not_lt_zero _ (by simpa only [hzero] using hslot)
    rcases hadj with hadj | ⟨hfst,hsnd⟩
    · exact stable _ hv _ hw hadj
    · have hwv : w = (v.1,w.2) := Prod.ext hfst.symm rfl
      have he : e v.1 v.2 = e v.1 w.2 := by
        apply Subtype.ext
        change c v = c (v.1,w.2)
        rw [← hwv]
        exact heq
      exact hsnd ((e v.1).injective he)
  have hchoose := (SimpleGraph.Coloring.mk c hc).colorable
  simpa only [Slots,Fintype.card_sigma,Fintype.card_fin,counts] using hchoose

theorem cliqueBlowup_chromatic_upper (G : SimpleGraph V) (m : ℕ) :
    ((cliqueBlowup G m).chromaticNumber.toNat : ℝ) ≤
      (m : ℝ)*number G + Fintype.card (Finset V) := by
  classical
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  have hcolor := cliqueBlowup_colorable_rounded hμ m
  have hn := ENat.toNat_le_of_le_natCast hcolor.chromaticNumber_le
  have hnr : ((cliqueBlowup G m).chromaticNumber.toNat : ℝ) ≤
      ∑ I, (⌈(m : ℝ)*μ I⌉₊ : ℝ) := by exact_mod_cast hn
  apply hnr.trans
  calc
    _ ≤ ∑ I, ((m : ℝ)*μ I + 1) := by
      apply Finset.sum_le_sum
      intro I _
      exact (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) (hμ.1 I))).le
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      change (m : ℝ) * cost μ + _ = _
      rw [heq]
      simp

end LinearListHadwiger.Fractional

namespace LinearListHadwiger
namespace FixedDecomposition
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

inductive Tree (G : SimpleGraph V) (k : ℕ) : Finset V → Type
  | leaf {S} (stop : S.card ≤ 2*k ∨ KConnectedOn G S k) : Tree G k S
  | branch {S A Z B} (split : SeparatorSplit G S A Z B) (small : Z.card < k)
      (left : Tree G k (A ∪ Z)) (right : Tree G k (B ∪ Z)) : Tree G k S

theorem exists_tree (S : Finset V) : Nonempty (Tree G k S) := by
  classical
  induction S using Finset.strongInductionOn with | _ S ih =>
  by_cases hs : S.card ≤ 2*k
  · exact ⟨Tree.leaf (Or.inl hs)⟩
  by_cases hc : KConnectedOn G S k
  · exact ⟨Tree.leaf (Or.inr hc)⟩
  obtain ⟨A,Z,B,hZ,hsplit⟩ := exists_separator G S (by omega : k < S.card) hc
  exact ⟨Tree.branch hsplit hZ (ih _ hsplit.left_union_ssubset).some
    (ih _ hsplit.swap.left_union_ssubset).some⟩

def Tree.leaves {S : Finset V} : Tree G k S → List (Finset V)
  | .leaf _ => [S]
  | .branch _ _ l r => l.leaves ++ r.leaves

def Tree.separators {S : Finset V} : Tree G k S → List (Finset V)
  | .leaf _ => []
  | @Tree.branch _ _ _ _ _ _ Z _ _ _ l r => Z :: (l.separators ++ r.separators)

def budget (k u : ℕ) : ℕ := if u ≤ 2*k then 1 else (u-k)^2

lemma budget_branch {u a b z : ℕ} (hu : 2*k < u) (hz : z < k)
    (ha : a < u) (hb : b < u) (hsum : a+b = u+z) :
    budget k a + budget k b + 1 ≤ budget k u := by
  unfold budget
  rw [ite_eq_right (by omega : ¬u ≤ 2*k)]
  split_ifs with hka hkb hkb
  · have hp : 2 ≤ u-k := by omega
    nlinarith
  · have hp : 2 ≤ u-k := by omega
    have hbp : b-k < u-k := by omega
    nlinarith
  · have hp : 2 ≤ u-k := by omega
    have hap : a-k < u-k := by omega
    nlinarith
  · have hsum' : (a-k)+(b-k) < u-k := by omega
    have ha0 : 0 < a-k := by omega
    have hb0 : 0 < b-k := by omega
    nlinarith [sq_nonneg ((a-k : ℕ) : ℤ),sq_nonneg ((b-k : ℕ) : ℤ)]

lemma Tree.leaf_subset {S U : Finset V} (d : Tree G k S) (hU : U ∈ d.leaves) :
    U ⊆ S := by
  induction d with
  | leaf _ =>
    have he : U = _ := List.mem_singleton.mp hU
    exact he ▸ Finset.Subset.refl _
  | branch hs hz l r ihl ihr =>
    rcases List.mem_append.mp hU with hl | hr
    · exact (ihl hl).trans hs.left_union_subset
    · exact (ihr hr).trans hs.swap.left_union_subset

lemma Tree.separator_subset {S Z : Finset V} (d : Tree G k S)
    (hZ : Z ∈ d.separators) : Z ⊆ S := by
  induction d with
  | leaf _ => simp [Tree.separators] at hZ
  | @branch S A T B hs hz l r ihl ihr =>
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact Finset.subset_union_right.trans hs.left_union_subset
    · rcases List.mem_append.mp hZ with hl | hr
      · exact (ihl hl).trans hs.left_union_subset
      · exact (ihr hr).trans hs.swap.left_union_subset

lemma Tree.leaf_stop {S U : Finset V} (d : Tree G k S) (hU : U ∈ d.leaves) :
    U.card ≤ 2*k ∨ KConnectedOn G U k := by
  induction d with
  | leaf h =>
    have he : U = _ := List.mem_singleton.mp hU
    exact he ▸ h
  | branch hs hz l r ihl ihr =>
    rcases List.mem_append.mp hU with hl | hr
    · exact ihl hl
    · exact ihr hr

lemma Tree.separator_small {S Z : Finset V} (d : Tree G k S)
    (hZ : Z ∈ d.separators) : Z.card < k := by
  induction d with
  | leaf _ => simp [Tree.separators] at hZ
  | branch hs hz l r ihl ihr =>
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact hz
    · rcases List.mem_append.mp hZ with hl | hr
      · exact ihl hl
      · exact ihr hr

theorem exists_bounded_tree (S : Finset V) :
    ∃ d : Tree G k S, d.leaves.length + d.separators.length ≤ budget k S.card := by
  classical
  induction S using Finset.strongInductionOn with | _ S ih =>
  by_cases hs : S.card ≤ 2*k
  · refine ⟨Tree.leaf (Or.inl hs),?_⟩
    simp [Tree.leaves,Tree.separators,budget,hs]
  by_cases hc : KConnectedOn G S k
  · refine ⟨Tree.leaf (Or.inr hc),?_⟩
    simp only [Tree.leaves,Tree.separators,List.length_singleton,List.length_nil,Nat.add_zero]
    unfold budget
    rw [ite_eq_right hs]
    have hp : 1 ≤ S.card-k := by omega
    nlinarith
  obtain ⟨A,Z,B,hZ,hsp⟩ := exists_separator G S (by omega : k < S.card) hc
  obtain ⟨l,hl⟩ := ih _ hsp.left_union_ssubset
  obtain ⟨r,hr⟩ := ih _ hsp.swap.left_union_ssubset
  refine ⟨Tree.branch hsp hZ l r,?_⟩
  have hcard : (A ∪ Z).card + (B ∪ Z).card = S.card + Z.card := by
    rw [Finset.card_union_of_disjoint hsp.left_sep,
      Finset.card_union_of_disjoint hsp.sep_right.symm,
      ← hsp.union_eq,Finset.card_union_of_disjoint hsp.left_union_disjoint,
      Finset.card_union_of_disjoint hsp.left_sep]
    omega
  have hb := budget_branch (by omega : 2*k < S.card) hZ
    (Finset.card_lt_card hsp.left_union_ssubset)
    (Finset.card_lt_card hsp.swap.left_union_ssubset) hcard
  simp only [Tree.leaves,Tree.separators,List.length_append,List.length_cons]
  omega

lemma budget_le_square (k u : ℕ) : budget k u ≤ (u+1)^2 := by
  unfold budget
  split_ifs
  · nlinarith
  · have : u-k ≤ u := Nat.sub_le _ _
    nlinarith

lemma reachable_preserves {W : Type} {H : SimpleGraph W} {P : W → Prop}
    (hstep : ∀ u v, H.Adj u v → P u → P v) {u v : W}
    (hr : H.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hstep _ _ h hu)

lemma confine_split {W : Type} [DecidableEq W] {H : SimpleGraph W}
    (π : W → V) (hπ : ∀ u v, H.Adj u v → G.Adj (π u) (π v) ∨ π u = π v)
    {S A Z B : Finset V} (hs : SeparatorSplit G S A Z B)
    {T : Finset W} {j : ℕ} (hT : KConnectedOn H T j)
    (hTS : ∀ u ∈ T, π u ∈ S)
    (hZ : (T.filter (fun u => π u ∈ Z)).card < j) :
    (∀ u ∈ T, π u ∈ A ∪ Z) ∨ (∀ u ∈ T, π u ∈ B ∪ Z) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨u,hu,huAZ⟩,v,hv,hvBZ⟩ := hn
  have hmem (w : W) (hw : w ∈ T) : π w ∈ A ∨ π w ∈ Z ∨ π w ∈ B := by
    have hh := hTS w hw
    rw [← hs.union_eq] at hh
    simpa only [Finset.mem_union,or_assoc] using hh
  have huB : π u ∈ B := by have := hmem u hu; simp only [Finset.mem_union] at huAZ; tauto
  have hvA : π v ∈ A := by have := hmem v hv; simp only [Finset.mem_union] at hvBZ; tauto
  let R := T.filter (fun w => π w ∈ Z)
  have huR : u ∈ T \ R := by
    refine Finset.mem_sdiff.mpr ⟨hu,?_⟩
    simpa only [R,Finset.mem_filter,hu,true_and] using
      (show π u ∉ Z from fun hz => huAZ (Finset.mem_union_right _ hz))
  have hvR : v ∈ T \ R := by
    refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
    simpa only [R,Finset.mem_filter,hv,true_and] using
      (show π v ∉ Z from fun hz => hvBZ (Finset.mem_union_right _ hz))
  have hc := hT.2 R (Finset.filter_subset _ _) hZ
  have hstep : ∀ a b : (↑(T \ R) : Set W),
      (H.induce (↑(T \ R) : Set W)).Adj a b → π a.val ∈ A → π b.val ∈ A := by
    intro a b hab ha
    have hbT := (Finset.mem_sdiff.mp b.property).1
    have hbZ : π b.val ∉ Z := by
      intro hz
      exact (Finset.mem_sdiff.mp b.property).2 (Finset.mem_filter.mpr ⟨hbT,hz⟩)
    rcases hmem b hbT with hb | hb | hb
    · exact hb
    · exact (hbZ hb).elim
    · rcases hπ a b hab with hedge | heq
      · exact (hs.anticomplete _ ha _ hb hedge).elim
      · exact heq ▸ ha
  have huA := reachable_preserves hstep (hc.preconnected ⟨v,hvR⟩ ⟨u,huR⟩) hvA
  exact Finset.disjoint_left.mp hs.left_right huA huB

lemma Tree.confine {W : Type} [DecidableEq W] {H : SimpleGraph W}
    {S : Finset V} (d : Tree G k S)
    (π : W → V) (hπ : ∀ u v, H.Adj u v → G.Adj (π u) (π v) ∨ π u = π v)
    {T : Finset W} {j : ℕ} (hT : KConnectedOn H T j)
    (hTS : ∀ u ∈ T, π u ∈ S)
    (hZ : ∀ Z ∈ d.separators, (T.filter (fun u => π u ∈ Z)).card < j) :
    ∃ L ∈ d.leaves, ∀ u ∈ T, π u ∈ L := by
  induction d with
  | leaf _ => exact ⟨_,by simp [Tree.leaves],hTS⟩
  | @branch S A Z B hs hz l r ihl ihr =>
    rcases confine_split π hπ hs hT hTS (hZ Z (by simp [Tree.separators])) with hl | hr
    · obtain ⟨L,hL,hTL⟩ := ihl hl (fun Z hZ' => hZ Z (by simp [Tree.separators,hZ']))
      exact ⟨L,List.mem_append_left _ hL,hTL⟩
    · obtain ⟨L,hL,hTL⟩ := ihr hr (fun Z hZ' => hZ Z (by simp [Tree.separators,hZ']))
      exact ⟨L,List.mem_append_right _ hL,hTL⟩

end FixedDecomposition
end LinearListHadwiger

namespace LinearListHadwiger.FixedDecomposition
open Fractional
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

lemma card_finset_subtype_le {V : Type} [Fintype V] [DecidableEq V] (A : Finset V) :
    Fintype.card (Finset (↑A : Set V)) ≤ Fintype.card (Finset V) := by
  exact Fintype.card_le_of_injective
    (fun s : Finset (↑A : Set V) => s.map (⟨Subtype.val,Subtype.val_injective⟩ : (↑A : Set V) ↪ V))
    (by intro s t h; exact Finset.map_injective _ h)

lemma lifted_separator_card {V : Type} [Fintype V] [DecidableEq V] {A Z : Finset V} {m : ℕ}
    (T : Finset ((↑A : Set V) × Fin m)) :
    (T.filter (fun u => u.1.val ∈ Z)).card ≤ (A ∩ Z).card*m := by
  classical
  let f : (↑A : Set V) × Fin m → V × Fin m := fun u => (u.1.val,u.2)
  have hf : Function.Injective f := by
    intro u v h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun z : V × Fin m => z.2) h
  calc
    _ ≤ ((A ∩ Z).product (Finset.univ : Finset (Fin m))).card := by
      apply Finset.card_le_card_of_injOn f
      · intro u hu
        exact Finset.mem_product.mpr ⟨Finset.mem_inter.mpr
          ⟨u.1.property,(Finset.mem_filter.mp hu).2⟩,Finset.mem_univ _⟩
      · exact hf.injOn
    _ = _ := by simp

lemma cliqueBlowup_leaf_hom {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A L : Finset V} {m : ℕ}
    (T : Finset ((↑A : Set V) × Fin m))
    (hTL : ∀ u ∈ T, u.1.val ∈ L) :
    Nonempty (((cliqueBlowup (G.induce (↑A : Set V)) m).induce (↑T : Set _)) →g
      cliqueBlowup (G.induce (↑(A ∩ L) : Set V)) m) := by
  let f : (↑T : Set ((↑A : Set V) × Fin m)) → (↑(A ∩ L) : Set V) × Fin m :=
    fun u => (⟨u.val.1.val,Finset.mem_inter.mpr ⟨u.val.1.property,hTL _ u.property⟩⟩,u.val.2)
  refine ⟨⟨f,?_⟩⟩
  intro u v huv
  change G.Adj u.val.1.val v.val.1.val ∨
    (u.val.1 = v.val.1 ∧ u.val.2 ≠ v.val.2) at huv
  change G.Adj u.val.1.val v.val.1.val ∨
    ((f u).1 = (f v).1 ∧ u.val.2 ≠ v.val.2)
  rcases huv with h | ⟨h,h'⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_,h'⟩
    apply Subtype.ext
    exact congrArg (fun x : (↑A : Set V) => x.val) h

theorem fractional_le_leaves_add_separator {S A : Finset V} (d : Tree G k S)
    (hAS : A ⊆ S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleaf : ∀ L ∈ d.leaves, number (G.induce (↑(A ∩ L) : Set V)) ≤ a)
    (hsep : ∀ Z ∈ d.separators, ((A ∩ Z).card : ℝ) ≤ b) :
    number (G.induce (↑A : Set V)) ≤ a+6*b := by
  classical
  by_contra hn
  have hgap : 0 < number (G.induce (↑A : Set V))-(a+6*b) := by linarith
  obtain ⟨m,hm⟩ := exists_nat_gt ((12+(Fintype.card (Finset V) : ℝ))/
    (number (G.induce (↑A : Set V))-(a+6*b)))
  have hmbig : 12+(Fintype.card (Finset V) : ℝ) <
      (m : ℝ)*(number (G.induce (↑A : Set V))-(a+6*b)) :=
    (div_lt_iff₀ hgap).mp hm
  let F := cliqueBlowup (G.induce (↑A : Set V)) m
  let j := ⌈(m : ℝ)*b⌉₊ + 1
  have hj : 1 ≤ j := by simp [j]
  have hjlow : (m : ℝ)*b < j := by
    have := Nat.le_ceil ((m : ℝ)*b)
    dsimp [j]
    push_cast
    linarith
  have hjup : (j : ℝ) < (m : ℝ)*b+2 := by
    have := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hb)
    dsimp [j]
    push_cast
    linarith

  have hlower := cliqueBlowup_chromatic_lower (G.induce (↑A : Set V)) m
  have hlargeR : (6*j : ℕ) < F.chromaticNumber.toNat := by
    have : (6 : ℝ)*j < (F.chromaticNumber.toNat : ℝ) := by
      dsimp [F]
      nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) ha, (show (0:ℝ) ≤ Fintype.card (Finset V) from Nat.cast_nonneg _)]
    exact_mod_cast this
  obtain ⟨T,hT,hχ⟩ := ordinary_connectivity_extraction F hj hlargeR
  let π : (↑A : Set V) × Fin m → V := fun u => u.1.val
  have hπ : ∀ u v, F.Adj u v → G.Adj (π u) (π v) ∨ π u = π v := by
    intro u v h
    rcases h with h | ⟨h,h'⟩
    · exact Or.inl h
    · exact Or.inr (congrArg Subtype.val h)
  have htests : ∀ Z ∈ d.separators, (T.filter (fun u => π u ∈ Z)).card < j := by
    intro Z hZ
    have hc := lifted_separator_card (Z := Z) T
    have hcr : ((T.filter (fun u => π u ∈ Z)).card : ℝ) ≤
      ((A ∩ Z).card : ℝ)*m := by exact_mod_cast hc
    have hrr : ((T.filter (fun u => π u ∈ Z)).card : ℝ) < j := by
      nlinarith [mul_le_mul_of_nonneg_right (hsep Z hZ) (Nat.cast_nonneg m)]
    exact_mod_cast hrr
  obtain ⟨L,hL,hTL⟩ := d.confine π hπ hT (fun u _ => hAS u.1.property) htests
  obtain ⟨hom⟩ := cliqueBlowup_leaf_hom (G := G) T hTL
  have hcolor := (cliqueBlowup (G.induce (↑(A ∩ L) : Set V)) m).colorable_chromaticNumber_of_fintype.of_hom hom
  have hχup := (ordinary_chromatic_le_iff (F.induce (↑T : Set _)) _).mpr hcolor
  have hχupR : ((F.induce (↑T : Set _)).chromaticNumber.toNat : ℝ) ≤
      ((cliqueBlowup (G.induce (↑(A ∩ L) : Set V)) m).chromaticNumber.toNat : ℝ) := by
    exact_mod_cast hχup
  have hu := cliqueBlowup_chromatic_upper (G.induce (↑(A ∩ L) : Set V)) m
  have hcost := card_finset_subtype_le (A ∩ L)
  have hcostR : (Fintype.card (Finset (↑(A ∩ L) : Set V)) : ℝ) ≤
      Fintype.card (Finset V) := by exact_mod_cast hcost
  have hχR : (F.chromaticNumber.toNat : ℝ)-6*j ≤
      ((F.induce (↑T : Set _)).chromaticNumber.toNat : ℝ) := by
    have he : (F.chromaticNumber.toNat-6*j : ℕ) + 6*j = F.chromaticNumber.toNat :=
      Nat.sub_add_cancel hlargeR.le
    have heR : ((F.chromaticNumber.toNat-6*j : ℕ) : ℝ) + 6*j = F.chromaticNumber.toNat := by
      exact_mod_cast he
    have hh : ((F.chromaticNumber.toNat-6*j : ℕ) : ℝ) ≤
      ((F.induce (↑T : Set _)).chromaticNumber.toNat : ℝ) := by exact_mod_cast hχ
    linarith
  have hla := mul_le_mul_of_nonneg_left (hleaf L hL) (Nat.cast_nonneg m)
  dsimp [F] at hχR hχupR
  have hh : (m : ℝ)*number (G.induce (↑A : Set V)) ≤
      (m : ℝ)*a + Fintype.card (Finset V) + 6*j := by
    linarith only [hlower,hχR,hχupR,hu,hcostR,hla]
  nlinarith only [hh,hmbig,hjup]

end LinearListHadwiger.FixedDecomposition

end OAI
