import OAI.Combinatorics.FiniteCircle.AnchorRecovery

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem matching_segments_card {α : Type*} {x y : List α} {q : ℕ}
    (A : WordMatching x y q) (a b n : ℕ) (ha : a+n ≤ x.length) (hb : b+n ≤ y.length) :
    (Finset.univ.filter (fun k : Fin q =>
      a ≤ (A.left k).val ∧ (A.left k).val < a+n ∧
      b ≤ (A.right k).val ∧ (A.right k).val < b+n)).card  ≤
      lcs (segment x a n) (segment y b n) := by
  classical
  let S := Finset.univ.filter (fun k : Fin q =>
    a ≤ (A.left k).val ∧ (A.left k).val < a+n ∧
    b ≤ (A.right k).val ∧ (A.right k).val < b+n)
  let e := S.orderEmbOfFin rfl
  have hmem (k : Fin S.card) : a ≤ (A.left (e k)).val ∧ (A.left (e k)).val < a+n ∧
      b ≤ (A.right (e k)).val ∧ (A.right (e k)).val < b+n :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl k)).2
  let f : Fin S.card → Fin (segment x a n).length := fun k =>
    ⟨(A.left (e k)).val-a, by rw [length_segment ha]; have := hmem k; omega⟩
  let g : Fin S.card → Fin (segment y b n).length := fun k =>
    ⟨(A.right (e k)).val-b, by rw [length_segment hb]; have := hmem k; omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hh := A.left.strictMono (e.strictMono hij)
    have hi := hmem i
    change (A.left (e i)).val-a  <  (A.left (e j)).val-a
    omega
  have hg : StrictMono g := by
    intro i j hij
    have hh := A.right.strictMono (e.strictMono hij)
    have hi := hmem i
    change (A.right (e i)).val-b  <  (A.right (e j)).val-b
    omega
  apply WordMatching.le_lcs (q:=S.card)
  refine ⟨OrderEmbedding.ofStrictMono f hf,OrderEmbedding.ofStrictMono g hg,?_⟩
  intro k
  have hka : a+((A.left (e k)).val-a)=(A.left (e k)).val := by have := hmem k; omega
  have hkb : b+((A.right (e k)).val-b)=(A.right (e k)).val := by have := hmem k; omega
  change (segment x a n).get (f k) = (segment y b n).get (g k)
  simpa only [f,g,List.get_eq_getElem, segment,
    List.getElem_take,List.getElem_drop,hka,hkb] using A.letters (e k)

theorem WordMatching.interval_card_loss {α : Type*} {x y : List α} {q w i a t : ℕ}
    (A : WordMatching x y q) (hw : 0 < w) (ha : i*w ≤ a) (ht : a+t ≤ (i+1)*w) :
    t  ≤  (Finset.univ.filter (fun k : Fin q =>  a ≤ (A.left k).val ∧ (A.left k).val < a+t)).card +
      A.sourceLoss w i := by
  classical
  let S := A.sourceBlock w i
  let B := Finset.Ico (i*w) ((i+1)*w)
  let T := S.image (fun k =>  (A.left k).val)
  let K := Finset.univ.filter (fun k : Fin q =>  a ≤ (A.left k).val ∧ (A.left k).val < a+t)
  let I := Finset.Ico a (a+t)
  have hinj : Function.Injective (fun k : Fin q =>  (A.left k).val) :=
    fun k l h =>  A.left.injective (Fin.ext h)
  have hT : T⊆B := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hd := (A.mem_sourceBlock w i k).mp hk
    have hl := Nat.mod_lt (A.left k).val hw
    have he := Nat.mod_add_div (A.left k).val w
    rw [hd, Nat.mul_comm w i] at he
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · rw [Nat.add_mul, one_mul]; omega
  have hBcard : B.card=w := by simp [B,Nat.add_mul]
  have hTcard : T.card=S.card := Finset.card_image_of_injective S hinj
  have hI : I ⊆ B := by
    intro j hj
    obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hj
    exact Finset.mem_Ico.mpr ⟨ha.trans h1,h2.trans_le ht⟩
  have hsub : I ⊆ K.image (fun k =>  (A.left k).val) ∪ (B\T) := by
    intro j hj
    by_cases hjT : j∈T
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hjT
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_Ico.mp hj⟩,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hI hj,hjT⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_image_of_injective K hinj,Finset.card_sdiff_of_subset hT,hBcard,hTcard] at hc
  simpa only [I,Nat.card_Ico,Nat.add_sub_cancel_left,WordMatching.sourceLoss,S,K] using hc

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem gap_right_le {w i : ℕ} (A : WordMatching x y q)
    {k l : Fin q} (hk : k∈A.sourceBlock w i) (hl : l∈A.sourceBlock w i) (hkl : k ≤ l) :
    (A.right l).val + (A.left k).val  ≤
      (A.right k).val + (A.left l).val + A.spanLoss w i := by
  let S := Finset.Icc k l
  have hS : S.Nonempty := ⟨k,Finset.mem_Icc.mpr ⟨le_rfl,hkl⟩⟩
  have hconv : ConvexIndices S := by
    intro a ha b hb c hac hcb
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1.trans hac,hcb.trans (Finset.mem_Icc.mp hb).2⟩
  have hsub : S ⊆ A.sourceBlock w i := by
    intro j hj
    exact A.sourceBlock_convex w i k hk l hl j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have he : A.rightSpan S=Finset.Icc (A.right k) (A.right l) := by
    ext j
    simp only [rightSpan,Finset.mem_filter,Finset.mem_univ,true_and,S,Finset.mem_Icc]
    constructor
    · rintro ⟨a,ha,b,hb,haj,hjb⟩
      exact ⟨(A.right.monotone ha.1).trans haj,hjb.trans (A.right.monotone hb.2)⟩
    · intro hj
      exact ⟨k,⟨le_rfl,hkl⟩,l,⟨hkl,le_rfl⟩,hj.1,hj.2⟩
  have hv := A.right_span_holes_le_spanLoss hconv hsub
  rw [he,Fin.card_Icc,Fin.card_Icc] at hv
  have hleft := A.symm.card_le_rightSpan S
  have heleft : A.symm.rightSpan S=Finset.Icc (A.left k) (A.left l) := by
    ext j
    simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and, S, Finset.mem_Icc]
    change (∃ a, (k ≤ a ∧ a ≤ l) ∧ ∃ b, (k ≤ b ∧ b ≤ l) ∧ A.left a ≤ j ∧ j ≤ A.left b) ↔ _
    constructor
    · rintro ⟨a,ha,b,hb,haj,hjb⟩
      exact ⟨(A.left.monotone ha.1).trans haj,hjb.trans (A.left.monotone hb.2)⟩
    · intro hj
      exact ⟨k,⟨le_rfl,hkl⟩,l,⟨hkl,le_rfl⟩,hj.1,hj.2⟩
  rw [heleft,Fin.card_Icc,Fin.card_Icc] at hleft
  have h1 := A.left.monotone hkl
  have h2 := A.right.monotone hkl
  omega

end WordMatching

theorem segment_encode_block {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (x : List α) (i : Fin x.length) (s n : ℕ) (hs : s+n ≤ w) :
    segment (encode c x) (i.val*w+s) n = interval c (x.get i) s n := by
  have ha : i.val*w+s+n ≤ (encode c x).length := by rw [length_encode]; nlinarith [i.isLt]
  apply List.ext_getElem
  · rw [length_segment ha]
    simp only [interval,List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro j hj hk
    have hjn : j < n := by simpa only [length_segment ha] using hj
    have hjw : s+j < w := by omega
    have hh := get_encode_block c x i ⟨s+j,hjw⟩
    simpa only [segment,interval,List.getElem_take,List.getElem_drop,List.getElem_ofFn,
      List.get_eq_getElem,Nat.add_assoc] using hh

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem offset_interior_labels (hw : 0 < w) {δ : ℝ} (hδ : δ ≤ 1)
    (hc : OffsetLocal δ c) (A : WordMatching (encode c x) (encode c y) q)
    (k : Fin q) (i : Fin x.length) (j : Fin y.length)
    (hi : (A.left k).val/w=i.val) (hj : (A.right k).val/w=j.val)
    (hp : w/8 ≤ (A.left k).val%w) (hp' : (A.left k).val%w+w/8 ≤ w)
    (hloss : (A.sourceLoss w i+A.spanLoss w i : ℕ)  <  δ*(w/8 : ℕ)) :
    x.get i=y.get j := by
  classical
  let u := w/8
  let p := (A.left k).val%w
  let r := (A.right k).val%w
  let U := A.sourceLoss w i
  let V := A.spanLoss w i
  have hloss' : ((U+V : ℕ) : ℝ) < δ*u := hloss
  have hUV : U+V < u := by
    have hnon : (0 : ℝ) ≤ u := by positivity
    have hh : (U+V : ℝ) < u := by push_cast at hloss'; nlinarith
    exact_mod_cast hh
  have hV : V < u := by omega
  have hup : u ≤ p := hp
  have hpu : p+u ≤ w := hp'
  have hpl : p < w := Nat.mod_lt _ hw
  have hrl : r < w := Nat.mod_lt _ hw
  have hleft : (A.left k).val=i.val*w+p := by
    have hh := Nat.mod_add_div (A.left k).val w
    rw [hi] at hh
    dsimp [p]
    nlinarith
  have hright : (A.right k).val=j.val*w+r := by
    have hh := Nat.mod_add_div (A.right k).val w
    rw [hj] at hh
    dsimp [r]
    nlinarith
  have hk : k∈A.sourceBlock w i := (A.mem_sourceBlock w i k).mpr hi
  have bound {a b t : ℕ} (hat : a+t ≤ w) (hbt : b+t ≤ w) :
      (Finset.univ.filter (fun z : Fin q =>
        i.val*w+a ≤ (A.left z).val ∧ (A.left z).val < i.val*w+a+t ∧
        j.val*w+b ≤ (A.right z).val ∧ (A.right z).val < j.val*w+b+t)).card  ≤
        lcs (interval c (x.get i) a t) (interval c (y.get j) b t) := by
    have hai : i.val*w+a+t ≤ (encode c x).length := by rw [length_encode]; nlinarith [i.isLt]
    have hbj : j.val*w+b+t ≤ (encode c y).length := by rw [length_encode]; nlinarith [j.isLt]
    simpa only [segment_encode_block c x i a t hat,segment_encode_block c y j b t hbt] using
      matching_segments_card A (i.val*w+a) (j.val*w+b) t hai hbj
  by_contra hne
  by_cases hf : r+u ≤ w
  · let a := i.val*w+p
    let b := j.val*w+r
    let t := u-V
    let K := Finset.univ.filter (fun z : Fin q =>  a ≤ (A.left z).val ∧ (A.left z).val < a+t)
    have ha : i.val*w ≤ a := by dsimp [a]; omega
    have hat : a+t ≤ (i.val+1)*w := by dsimp [a,t]; nlinarith [Nat.sub_le u V]
    have hcard : t ≤ K.card+U := A.interval_card_loss hw ha hat
    have hsub : K ⊆ Finset.univ.filter (fun z : Fin q =>
        i.val*w+p ≤ (A.left z).val ∧ (A.left z).val < i.val*w+p+u ∧
        j.val*w+r ≤ (A.right z).val ∧ (A.right z).val < j.val*w+r+u) := by
      intro z hz
      have hpos : a ≤ (A.left z).val ∧ (A.left z).val < a+t := (Finset.mem_filter.mp hz).2
      have hzi : (A.left z).val/w=i.val :=
        Nat.div_eq_of_lt_le (ha.trans hpos.1) (hpos.2.trans_le hat)
      have hkz : k ≤ z := A.left.le_iff_le.mp (by change (A.left k).val ≤ (A.left z).val; simpa only [hleft] using hpos.1)
      have hg := A.gap_right_le hk ((A.mem_sourceBlock w i z).mpr hzi) hkz
      have hmono := A.right.monotone hkz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_,?_,?_⟩ <;> dsimp [a,b,t] at * <;> omega
    have hb := (Finset.card_le_card hsub).trans (bound hpu hf)
    have hlocal := hc (x.get i) (y.get j) hne p r hpu hf
    have hs : (u : ℝ) ≤ (lcs (interval c (x.get i) p u) (interval c (y.get j) r u):ℝ)+U+V := by
      have hc' : u ≤ lcs (interval c (x.get i) p u) (interval c (y.get j) r u)+U+V := by dsimp [t] at hcard; omega
      exact_mod_cast hc'
    change _ ≤ (1-δ)*(u : ℝ) at hlocal
    push_cast at hloss'
    nlinarith only [hs,hlocal,hloss']
  · let a := i.val*w+(p+1-(u-V))
    let t := u-V
    have hrfit : u ≤ r+1 := by dsimp [u] at *; omega
    have hpfit : u ≤ p+1 := by omega
    have hps : p+1-u+u ≤ w := by omega
    have hrs : r+1-u+u ≤ w := by omega
    let K := Finset.univ.filter (fun z : Fin q =>  a ≤ (A.left z).val ∧ (A.left z).val < a+t)
    have ha : i.val*w ≤ a := by dsimp [a]; omega
    have hat : a+t ≤ (i.val+1)*w := by
      dsimp [a,t]
      rw [Nat.add_mul, one_mul]
      omega
    have hcard : t ≤ K.card+U := A.interval_card_loss hw ha hat
    have hsub : K ⊆ Finset.univ.filter (fun z : Fin q =>
        i.val*w+(p+1-u) ≤ (A.left z).val ∧ (A.left z).val < i.val*w+(p+1-u)+u ∧
        j.val*w+(r+1-u) ≤ (A.right z).val ∧ (A.right z).val < j.val*w+(r+1-u)+u) := by
      intro z hz
      have hpos : a ≤ (A.left z).val ∧ (A.left z).val < a+t := (Finset.mem_filter.mp hz).2
      have hzi : (A.left z).val/w=i.val :=
        Nat.div_eq_of_lt_le (ha.trans hpos.1) (hpos.2.trans_le hat)
      have hzk : z ≤ k := A.left.le_iff_le.mp (by change (A.left z).val ≤ (A.left k).val; dsimp [a,t] at hpos; omega)
      have hg := A.gap_right_le ((A.mem_sourceBlock w i z).mpr hzi) hk hzk
      have hmono := A.right.monotone hzk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_,?_,?_⟩ <;> dsimp [a,t] at * <;> omega
    have hb := (Finset.card_le_card hsub).trans (bound hps hrs)
    have hlocal := hc (x.get i) (y.get j) hne (p+1-u) (r+1-u) hps hrs
    have hs : (u : ℝ) ≤ (lcs (interval c (x.get i) (p+1-u) u) (interval c (y.get j) (r+1-u) u):ℝ)+U+V := by
      have hc' : u ≤ lcs (interval c (x.get i) (p+1-u) u) (interval c (y.get j) (r+1-u) u)+U+V := by dsimp [t] at hcard; omega
      exact_mod_cast hc'
    change _ ≤ (1-δ)*(u : ℝ) at hlocal
    push_cast at hloss'
    nlinarith only [hs,hlocal,hloss']

end WordMatching

theorem monotone_assignment_deficit {α : Type*} {x y : List α}
    (S : Finset ℕ) (hS : S ⊆ Finset.range x.length) (f : ℕ → ℕ)
    (hf : ∀ i ∈ S, f i < y.length)
    (hm : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → f i ≤ f j)
    (hl : ∀ i (hi : i ∈ S), x[i]'(Finset.mem_range.mp (hS hi)) = y[f i]'(hf i hi)) :
    deficit x y ≤ 2 * (x.length - S.card) +
      (S.filter (fun i => i+1 ∈ S ∧ f i = f (i+1))).card := by
  classical
  let D := S.filter (fun i => ∃ j ∈ S, j < i ∧ f j = f i)
  let T := S \ D
  let B := Finset.range x.length \ S
  let J := S.filter (fun i => i+1 ∈ S ∧ f i = f (i+1))
  have hD : D ⊆ S := Finset.filter_subset _ _
  have hT : T ⊆ S := Finset.sdiff_subset
  have hdpos : ∀ i ∈ D, 0 < i := by
    intro i hi
    obtain ⟨j,_,hj,_⟩ := (Finset.mem_filter.mp hi).2
    omega
  have hpred : D.image (fun i => i-1) ⊆ B ∪ J := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hip := hdpos i hi
    have hil := Finset.mem_range.mp (hS (hD hi))
    by_cases hh : i-1 ∈ S
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hh,?_,?_⟩
      · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hD hi
      · obtain ⟨j,hj,hji,hfj⟩ := (Finset.mem_filter.mp hi).2
        have h1 := hm j hj (i-1) hh (by omega)
        have h2 := hm (i-1) hh i (hD hi) (by omega)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
          (show f (i-1) = f i by omega)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_range.mpr (by omega),hh⟩)
  have hdinj : Set.InjOn (fun i : ℕ => i-1) D := by
    intro i hi j hj hij
    have := hdpos i hi
    have := hdpos j hj
    dsimp only at hij
    omega
  have hdc : D.card ≤ B.card + J.card := by
    have hh := (Finset.card_le_card hpred).trans (Finset.card_union_le B J)
    rwa [Finset.card_image_of_injOn hdinj] at hh
  have htmat : T.card ≤ lcs x y := by
    let e := T.orderEmbOfFin rfl
    have he (k : Fin T.card) : e k ∈ T := T.orderEmbOfFin_mem rfl k
    let g : Fin T.card → Fin x.length := fun k =>
      ⟨e k,Finset.mem_range.mp (hS (hT (he k)))⟩
    let h : Fin T.card → Fin y.length := fun k => ⟨f (e k),hf _ (hT (he k))⟩
    have hg : StrictMono g := fun i j hij => e.strictMono hij
    have hh : StrictMono h := by
      intro i j hij
      have heij := e.strictMono hij
      have hm' := hm (e i) (hT (he i)) (e j) (hT (he j)) heij.le
      have hneq : f (e i) ≠ f (e j) := by
        intro heq
        have hn := (Finset.mem_sdiff.mp (he j)).2
        exact hn (Finset.mem_filter.mpr ⟨hT (he j),e i,hT (he i),heij,heq⟩)
      change f (e i) < f (e j)
      exact lt_of_le_of_ne hm' hneq
    let A : WordMatching x y T.card :=
      { left := OrderEmbedding.ofStrictMono g hg
        right := OrderEmbedding.ofStrictMono h hh
        letters := fun k => hl (e k) (hT (he k)) }
    exact A.le_lcs
  have htc : T.card = S.card - D.card := Finset.card_sdiff_of_subset hD
  have hbc : B.card = x.length - S.card := by rw [Finset.card_sdiff_of_subset hS,Finset.card_range]
  dsimp only [deficit]
  dsimp only [J] at hdc
  omega

end FiniteCircle

end OAI
