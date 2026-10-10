import OAI.Combinatorics.FiniteCircle.Matching

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def taggedRow {J β : Type*} (js : List J) (W : J → List β) : List (J × β) :=
  js.flatMap (fun j => (W j).map (fun b => (j,b)))

@[simp] theorem taggedRow_nil {J β : Type*} (W : J → List β) : taggedRow [] W = [] := rfl
@[simp] theorem taggedRow_cons {J β : Type*} (j : J) (js : List J) (W : J → List β) :
    taggedRow (j::js) W = (W j).map (fun b => (j,b)) ++ taggedRow js W := rfl

theorem filter_map_tag {J β : Type*} [DecidableEq J] (j k : J) (x : List β) :
    ((x.map (fun b => (k,b))).filter (fun z => decide (z.1 = j))) =
      if k = j then x.map (fun b => (j,b)) else [] := by
  by_cases h : k = j
  · subst k
    simp [List.filter_map, Function.comp_def]
  · simp [List.filter_map, Function.comp_def, h]

theorem filter_taggedRow {J β : Type*} [DecidableEq J] (js : List J)
    (hn : js.Nodup) (W : J → List β) (j : J) :
    ((taggedRow js W).filter (fun z => decide (z.1 = j))) =
      if j ∈ js then (W j).map (fun b => (j,b)) else [] := by
  induction js with
  | nil => simp
  | cons k js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [taggedRow_cons, List.filter_append, filter_map_tag, ih hn'.2]
    by_cases h : k = j
    · subst k
      simp [hn'.1]
    · by_cases hj : j ∈ js <;> simp [h, hj, Ne.symm h]

theorem sum_filter_tag_length {J β : Type*} [Fintype J] [DecidableEq J]
    (x : List (J × β)) :
    ∑ j : J, (x.filter (fun z => decide (z.1 = j))).length = x.length := by
  induction x with
  | nil => simp
  | cons a x ih =>
    have he (j : J) : ((a::x).filter (fun z => decide (z.1 = j))).length =
        (if a.1 = j then 1 else 0) + (x.filter (fun z => decide (z.1 = j))).length := by
      by_cases h : a.1 = j <;> simp [h, Nat.add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

theorem length_taggedRow {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W : J → List β) :
    (taggedRow js W).length = ∑ j : J, (W j).length := by
  rw [← sum_filter_tag_length (taggedRow js W)]
  congr 1
  funext j
  rw [filter_taggedRow js hn W j, ite_eq_left (hall j), List.length_map]

theorem lcs_taggedRow_le {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W U : J → List β) :
    lcs (taggedRow js W) (taggedRow js U) ≤ ∑ j : J, lcs (W j) (U j) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists (taggedRow js W) (taggedRow js U)
  rw [← hz, ← sum_filter_tag_length z]
  apply Finset.sum_le_sum
  intro j _
  have hx' := hx.filter (fun z => decide (z.1 = j))
  have hy' := hy.filter (fun z => decide (z.1 = j))
  rw [filter_taggedRow js hn W j, ite_eq_left (hall j)] at hx'
  rw [filter_taggedRow js hn U j, ite_eq_left (hall j)] at hy'
  have hh := le_lcs hx' hy'
  rw [lcs_map_eq (fun b : β => (j,b)) (fun _ _ h => congrArg Prod.snd h)] at hh
  exact hh

theorem get_segment {β : Type*} (x : List β) {s n : ℕ} (hs : s+n ≤ x.length)
    (i : Fin (segment x s n).length) :
    (segment x s n).get i = x.get ⟨s+i.val, by
      have hi := i.isLt
      simp only [length_segment hs] at hi
      omega⟩ := by
  change ((x.drop s).take n)[i.val] = _
  simp only [List.getElem_take, List.getElem_drop, List.get_eq_getElem]

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

def onSegments (A : WordMatching x y q) (S : Finset (Fin q))
    {s n t m : ℕ} (hs : s+n ≤ x.length) (ht : t+m ≤ y.length)
    (hleft : ∀ i ∈ S, s ≤ (A.left i).val ∧ (A.left i).val < s+n)
    (hright : ∀ i ∈ S, t ≤ (A.right i).val ∧ (A.right i).val < t+m) :
    WordMatching (segment x s n) (segment y t m) S.card := by
  let f : Fin S.card → Fin (segment x s n).length := fun i =>
    ⟨(A.left (S.orderEmbOfFin rfl i)).val-s, by
      rw [length_segment hs]
      have hh := hleft _ (S.orderEmbOfFin_mem rfl i)
      omega⟩
  let g : Fin S.card → Fin (segment y t m).length := fun i =>
    ⟨(A.right (S.orderEmbOfFin rfl i)).val-t, by
      rw [length_segment ht]
      have hh := hright _ (S.orderEmbOfFin_mem rfl i)
      omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hh : (A.left (S.orderEmbOfFin rfl i)).val < (A.left (S.orderEmbOfFin rfl j)).val :=
      A.left.strictMono ((S.orderEmbOfFin rfl).strictMono hij)
    have hi := hleft _ (S.orderEmbOfFin_mem rfl i)
    change (A.left (S.orderEmbOfFin rfl i)).val-s < (A.left (S.orderEmbOfFin rfl j)).val-s
    omega
  have hg : StrictMono g := by
    intro i j hij
    have hh : (A.right (S.orderEmbOfFin rfl i)).val < (A.right (S.orderEmbOfFin rfl j)).val :=
      A.right.strictMono ((S.orderEmbOfFin rfl).strictMono hij)
    have hi := hright _ (S.orderEmbOfFin_mem rfl i)
    change (A.right (S.orderEmbOfFin rfl i)).val-t < (A.right (S.orderEmbOfFin rfl j)).val-t
    omega
  refine ⟨OrderEmbedding.ofStrictMono f hf, OrderEmbedding.ofStrictMono g hg, ?_⟩
  intro i
  change (segment x s n).get (f i) = (segment y t m).get (g i)
  rw [get_segment x hs, get_segment y ht]
  have hi := hleft _ (S.orderEmbOfFin_mem rfl i)
  have hj := hright _ (S.orderEmbOfFin_mem rfl i)
  convert A.letters (S.orderEmbOfFin rfl i) using 1
  · congr 1
    apply Fin.ext
    change s+((A.left (S.orderEmbOfFin rfl i)).val-s) = _
    omega
  · congr 1
    apply Fin.ext
    change t+((A.right (S.orderEmbOfFin rfl i)).val-t) = _
    omega

theorem card_onSegments_le (A : WordMatching x y q) (S : Finset (Fin q))
    {s n t m : ℕ} (hs : s+n ≤ x.length) (ht : t+m ≤ y.length)
    (hleft : ∀ i ∈ S, s ≤ (A.left i).val ∧ (A.left i).val < s+n)
    (hright : ∀ i ∈ S, t ≤ (A.right i).val ∧ (A.right i).val < t+m) :
    S.card ≤ lcs (segment x s n) (segment y t m) :=
  (A.onSegments S hs ht hleft hright).le_lcs

end WordMatching

theorem position_decomposition (x t L : ℕ) :
    x = (x/(t*L))*(t*L) + ((x/L)%t)*L + x%L := by
  have h1 := Nat.mod_add_div (x/L) t
  have h2 := Nat.mod_add_div x L
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm L t] at h1
  nlinarith

theorem split_positions_gap {t L i x₁ x₂ y₁ y₂ : ℕ} (ht : 2 ≤ t) (hL : 0 < L)
    (hx₁ : x₁/(t*L) = i) (hx₂ : x₂/(t*L) = i)
    (hy : y₁/(t*L) < y₂/(t*L)) (hx : x₁ ≤ x₂)
    (hxy : y₁ ≤ y₂)
    (htag₁ : (x₁/L)%t = (y₁/L)%t) (htag₂ : (x₂/L)%t = (y₂/L)%t) :
    (t-2)*L + (x₂+1-x₁) ≤ y₂+1-y₁ := by
  have ex₁ := position_decomposition x₁ t L
  have ex₂ := position_decomposition x₂ t L
  have ey₁ := position_decomposition y₁ t L
  have ey₂ := position_decomposition y₂ t L
  rw [hx₁, htag₁] at ex₁
  rw [hx₂, htag₂] at ex₂
  have hb := Nat.mul_le_mul_right (t*L) (show y₁/(t*L)+1 ≤ y₂/(t*L) by omega)
  have hrx₂ := Nat.mod_lt x₂ hL
  have hry₁ := Nat.mod_lt y₁ hL
  have hT : (t-2)*L+2*L = t*L := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hgap : (t-2)*L+x₂+y₁ ≤ y₂+x₁ := by nlinarith [Nat.zero_le (x₁%L), Nat.zero_le (y₂%L)]
  omega

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

def singleTargetRow (A : WordMatching x y q) (W i : ℕ) : Prop :=
  ∃ j : ℕ, ∀ k ∈ A.sourceBlock W i, (A.right k).val/W = j

theorem spanLoss_of_split (A : WordMatching x y q) {t L i : ℕ}
    (ht : 2 ≤ t) (hL : 0 < L) (tag : β → ℕ)
    (hx : ∀ k : Fin x.length, tag (x.get k) = (k.val/L)%t)
    (hy : ∀ k : Fin y.length, tag (y.get k) = (k.val/L)%t)
    (hsplit : ¬A.singleTargetRow (t*L) i) :
    (t-2)*L ≤ A.spanLoss (t*L) i := by
  classical
  let S := A.sourceBlock (t*L) i
  have hS : S.Nonempty := by
    by_contra he
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hsplit
    exact ⟨0, fun k hk => False.elim (by change k ∈ S at hk; simp [he] at hk)⟩
  let a := S.min' hS
  let b := S.max' hS
  have ha : a ∈ S := S.min'_mem hS
  have hb : b ∈ S := S.max'_mem hS
  have hab : a ≤ b := S.min'_le b hb
  have hleft : (A.left a).val ≤ (A.left b).val := A.left.monotone hab
  have hright : (A.right a).val ≤ (A.right b).val := A.right.monotone hab
  have hrow : (A.right a).val/(t*L) < (A.right b).val/(t*L) := by
    by_contra hn
    have he : (A.right a).val/(t*L) = (A.right b).val/(t*L) := by
      have hh := Nat.div_le_div_right (c := t*L) hright
      omega
    apply hsplit
    refine ⟨(A.right a).val/(t*L), fun k hk => ?_⟩
    have hlo := Nat.div_le_div_right (c := t*L) (show (A.right a).val ≤ (A.right k).val from
      A.right.monotone (S.min'_le k hk))
    have hhi := Nat.div_le_div_right (c := t*L) (show (A.right k).val ≤ (A.right b).val from
      A.right.monotone (S.le_max' k hk))
    omega
  have htag (k : Fin q) : ((A.left k).val/L)%t = ((A.right k).val/L)%t := by
    rw [← hx, ← hy, A.letters]
  have hgap := split_positions_gap ht hL ((A.mem_sourceBlock (t*L) i a).mp ha)
    ((A.mem_sourceBlock (t*L) i b).mp hb) hrow hleft hright (htag a) (htag b)
  have hcard := A.symm.card_le_rightSpan S
  have hsx := A.symm.rightSpan_eq_Icc hS
  have hsy := A.rightSpan_eq_Icc hS
  rw [hsx, Fin.card_Icc] at hcard
  change (t-2)*L ≤ (A.rightSpan S).card - S.card
  rw [hsy, Fin.card_Icc]
  change S.card ≤ (A.left b).val+1-(A.left a).val at hcard
  change (t-2)*L ≤ (A.right b).val+1-(A.right a).val-S.card
  omega

theorem sourceLoss_of_single (A : WordMatching x y q) {W N i : ℕ}
    (hW : 0 < W) (hx : x.length = W*N) (hy : y.length = W*N) (hi : i < N)
    (hS : (A.sourceBlock W i).Nonempty) (hsingle : A.singleTargetRow W i) :
    ∃ j : Fin N, deficit (segment x (i*W) W) (segment y (j.val*W) W) ≤ A.sourceLoss W i := by
  obtain ⟨j, hj⟩ := hsingle
  obtain ⟨k, hk⟩ := hS
  have hjN : j < N := by
    have hkj := hj k hk
    have hkp := (A.right k).isLt
    simp only [hy] at hkp
    rw [← hkj]
    exact (Nat.div_lt_iff_lt_mul hW).mpr (by nlinarith)
  have hxi : i*W+W ≤ x.length := by rw [hx]; nlinarith
  have hyj : j*W+W ≤ y.length := by rw [hy]; nlinarith
  have hc := A.card_onSegments_le (A.sourceBlock W i) hxi hyj
    (fun k hk => by
      have hh := (A.mem_sourceBlock W i k).mp hk
      have h1 := Nat.mod_add_div (A.left k).val W
      have h2 := Nat.mod_lt (A.left k).val hW
      rw [hh] at h1
      constructor <;> nlinarith [Nat.zero_le ((A.left k).val%W)])
    (fun k hk => by
      have hh := hj k hk
      have h1 := Nat.mod_add_div (A.right k).val W
      have h2 := Nat.mod_lt (A.right k).val hW
      rw [hh] at h1
      constructor <;> nlinarith [Nat.zero_le ((A.right k).val%W)])
  refine ⟨⟨j, hjN⟩, ?_⟩
  simpa only [deficit, length_segment hxi, sourceLoss] using Nat.sub_le_sub_left hc W

end WordMatching

theorem row_separation {β : Type*} {x y : List β} {N t L : ℕ} (hL : 0 < L) (ht : 4 ≤ t)
    (hx : x.length = (t*L)*N) (hy : y.length = (t*L)*N)
    (tag : β → ℕ)
    (htagx : ∀ k : Fin x.length, tag (x.get k) = (k.val/L)%t)
    (htagy : ∀ k : Fin y.length, tag (y.get k) = (k.val/L)%t)
    (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hrows : ∀ i j : Fin N, ρ*(t*L) ≤
      (deficit (segment x (i.val*(t*L)) (t*L)) (segment y (j.val*(t*L)) (t*L)) : ℝ)) :
    ρ/2 * x.length ≤ (deficit x y : ℝ) := by
  classical
  have hW : 0 < t*L := by positivity
  obtain ⟨A⟩ := exists_lcs_matching x y
  have hper (i : Fin N) : ρ*(t*L) ≤ (A.sourceLoss (t*L) i : ℝ)+(A.spanLoss (t*L) i : ℝ) := by
    by_cases hS : (A.sourceBlock (t*L) i).Nonempty
    · by_cases hsingle : A.singleTargetRow (t*L) i
      · obtain ⟨j, hj⟩ := A.sourceLoss_of_single hW hx hy i.isLt hS hsingle
        have hh : (deficit (segment x (i.val*(t*L)) (t*L)) (segment y (j.val*(t*L)) (t*L)) : ℝ) ≤ A.sourceLoss (t*L) i := by exact_mod_cast hj
        exact (hrows i j).trans (hh.trans (le_add_of_nonneg_right (by positivity)))
      · have hh := A.spanLoss_of_split (by omega) hL tag htagx htagy hsingle
        have hh' : ((t-2 : ℕ) : ℝ)*L ≤ A.spanLoss (t*L) i := by exact_mod_cast hh
        have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
        rw [Nat.cast_sub (by omega : 2 ≤ t), Nat.cast_ofNat] at hh'
        have hlt : (0 : ℝ) ≤ t*L := by positivity
        have hρ' := mul_le_mul_of_nonneg_right hρ hlt
        nlinarith [Nat.cast_nonneg (α := ℝ) (A.sourceLoss (t*L) i)]
    · have he : A.sourceBlock (t*L) i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hu : A.sourceLoss (t*L) i = t*L := by simp [WordMatching.sourceLoss, he]
      rw [hu, Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_right hρ (show (0 : ℝ) ≤ t*L by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) (A.spanLoss (t*L) i)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hper i)
  rw [Finset.sum_add_distrib] at hsum
  have hU := A.sum_sourceLoss hW hx
  have hV := A.sum_spanLoss_le hW hx hy
  have hUr : (∑ i : Fin N, (A.sourceLoss (t*L) i : ℝ)) = deficit x y := by
    exact_mod_cast (show (∑ i : Fin N, A.sourceLoss (t*L) i) = deficit x y by simpa only [deficit, hx] using hU)
  have hVr : (∑ i : Fin N, (A.spanLoss (t*L) i : ℝ)) ≤ deficit x y := by
    exact_mod_cast (show (∑ i : Fin N, A.spanLoss (t*L) i) ≤ deficit x y by simpa only [deficit, hx] using hV)
  rw [hUr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hx, Nat.cast_mul, Nat.cast_mul]
  nlinarith

theorem length_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) (L : ℕ)
    (hl : ∀ a ∈ xs, (f a).length = L) : (xs.flatMap f).length = xs.length*L := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hl a (by simp), ih (fun a ha => hl a (by simp [ha]))]
    nlinarith

theorem segment_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) (L : ℕ)
    (hl : ∀ a ∈ xs, (f a).length = L) (i : Fin xs.length) :
    segment (xs.flatMap f) (i.val*L) L = f (xs.get i) := by
  have he : xs = xs.take i.val ++ xs[i.val] :: xs.drop (i.val+1) := by
    conv_lhs => rw [← List.take_append_drop i.val xs, List.drop_eq_getElem_cons i.isLt]
  have hp : ((xs.take i.val).flatMap f).length = i.val*L := by
    rw [length_flatMap_uniform _ f L (fun a ha => hl a (List.mem_of_mem_take ha)),
      List.length_take_of_le i.isLt.le]
  have hi := hl (xs.get i) (xs.get_mem i)
  have hf := congrArg (fun ys => ys.flatMap f) he
  rw [List.flatMap_append, List.flatMap_cons] at hf
  rw [hf]
  unfold segment
  rw [← hp, List.drop_left, List.take_append_of_le_length (by simpa only [List.get_eq_getElem] using hi.ge)]
  simpa only [List.get_eq_getElem] using List.take_of_length_le (by simpa only [List.get_eq_getElem] using hi.le)

theorem get_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) {L : ℕ}
    (hL : 0 < L) (hl : ∀ a ∈ xs, (f a).length = L)
    (k : Fin (xs.flatMap f).length) :
    ∃ (i : Fin xs.length) (b : Fin (f (xs.get i)).length),
      i.val = k.val/L ∧ b.val = k.val%L ∧ (xs.flatMap f).get k = (f (xs.get i)).get b := by
  have hk : k.val < xs.length*L := by simpa only [length_flatMap_uniform xs f L hl] using k.isLt
  let i : Fin xs.length := ⟨k.val/L, (Nat.div_lt_iff_lt_mul hL).mpr hk⟩
  have hi := hl (xs.get i) (xs.get_mem i)
  let b : Fin (f (xs.get i)).length := ⟨k.val%L, by rw [hi]; exact Nat.mod_lt _ hL⟩
  refine ⟨i, b, rfl, rfl, ?_⟩
  have hs : i.val*L+L ≤ (xs.flatMap f).length := by
    rw [length_flatMap_uniform xs f L hl]
    have h := Nat.mul_le_mul_right L i.isLt
    nlinarith
  have he := segment_flatMap_uniform xs f L hl i
  let b' : Fin (segment (xs.flatMap f) (i.val*L) L).length :=
    ⟨b.val, by rw [he]; exact b.isLt⟩
  have hg := get_segment (xs.flatMap f) hs b'
  have hpos : i.val*L+b'.val = k.val := by
    change k.val/L*L+k.val%L = k.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod k.val L
  have hg' : (segment (xs.flatMap f) (i.val*L) L).get b' = (xs.flatMap f).get k := by
    convert hg using 1
    congr 1
    exact Fin.ext hpos.symm
  rw [← hg']
  simp only [List.get_eq_getElem]
  simp only [he]
  rfl

theorem tag_get_taggedRow {J β : Type*} [DecidableEq J] (js : List J) (hn : js.Nodup)
    (W : J → List β) {L : ℕ} (hL : 0 < L) (hl : ∀ j ∈ js, (W j).length = L)
    (k : Fin (taggedRow js W).length) :
    js.idxOf ((taggedRow js W).get k).1 = k.val/L := by
  obtain ⟨i,b,hi,_,he⟩ := get_flatMap_uniform js (fun j => (W j).map (fun z => (j,z))) hL
    (fun j hj => by simp [hl j hj]) k
  change (taggedRow js W).get k = _ at he
  rw [he]
  simp only [List.get_eq_getElem, List.getElem_map]
  rw [hn.idxOf_getElem]
  exact hi

theorem tag_get_rows {J β : Type*} [DecidableEq J] (js : List J) (hn : js.Nodup)
    (W : ℕ → J → List β) {L N : ℕ} (hL : 0 < L) (ht : 0 < js.length)
    (hl : ∀ a < N, ∀ j ∈ js, (W a j).length = L)
    (k : Fin ((List.range N).flatMap (fun a => taggedRow js (W a))).length) :
    js.idxOf (((List.range N).flatMap (fun a => taggedRow js (W a))).get k).1 =
      (k.val/L)%js.length := by
  have hr (a : ℕ) (ha : a ∈ List.range N) : (taggedRow js (W a)).length = js.length*L := by
    apply length_flatMap_uniform
    intro j hj
    simp [hl a (List.mem_range.mp ha) j hj]
  obtain ⟨i,b,_,hb,he⟩ := get_flatMap_uniform (List.range N) (fun a => taggedRow js (W a))
    (Nat.mul_pos ht hL) hr k
  rw [he, tag_get_taggedRow js hn _ hL (hl _ (by simpa using i.isLt)), hb]
  rw [Nat.mul_comm js.length L, Nat.mod_mul_right_div_self]

end FiniteCircle

end OAI
