import OAI.Combinatorics.FiniteCircle.BlockMatching

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem zip_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zip, List.getElem_ofFn]

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem localIndices_letters (hw : 0 < w) (A : WordMatching (encode c x) (encode c y) q)
    {i : Fin x.length} {j : Fin y.length} {S : Finset (Fin q)}
    (hS : S ⊆ A.blockPair w i j) :
    ∀ z ∈ (A.localIndices hw S).zip (A.symm.localIndices hw S),
      c (x.get i) z.1 = c (y.get j) z.2 := by
  intro z hz
  rw [localIndices, localIndices, zip_ofFn] at hz
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
  let p := S.orderEmbOfFin rfl k
  have hp := hS (S.orderEmbOfFin_mem rfl k)
  obtain ⟨hl, hr⟩ := Finset.mem_inter.mp hp
  have hi := (A.mem_sourceBlock w i p).mp hl
  have hj := (A.symm.mem_sourceBlock w j p).mp hr
  have he := A.letters p
  rw [get_encode hw, get_encode hw] at he
  convert he using 1 <;> congr 2
  · apply Fin.ext
    exact hi.symm
  · apply Fin.ext
    exact hj.symm

theorem anchor_on_blockPair (hw : 0 < w) {ε : ℝ} (hlocal : AnchorLocal ε c)
    (A : WordMatching (encode c x) (encode c y) q)
    (i : Fin x.length) (j : Fin y.length)
    (hcard : w ≤ 4*(A.blockPair w i j).card)
    (hU : (A.sourceLoss w i : ℝ) ≤ ε*w)
    (hV : (A.spanLoss w i : ℝ) ≤ ε*w) :
    x.get i = y.get j ∧ ∃ k ∈ A.blockPair w i j, (A.left k).val%w = (A.right k).val%w := by
  let S := A.blockPair w i j
  have hS : S ⊆ A.sourceBlock w i := Finset.inter_subset_left
  have hT : S ⊆ A.symm.sourceBlock w j := Finset.inter_subset_right
  have hconv : ConvexIndices S := A.blockPair_convex w i j
  have hbound : (w : ℝ)/4 ≤ (A.localIndices hw S).length := by
    rw [localIndices_length]
    have hc : (w : ℝ) ≤ 4*(S.card : ℝ) := by exact_mod_cast hcard
    linarith
  have hleft : ((indexSpan (A.localIndices hw S) - (A.localIndices hw S).length : ℕ) : ℝ) ≤ ε*w := by
    rw [A.localIndices_span hw hS, localIndices_length]
    have hh : (((A.symm.rightSpan S).card - S.card : ℕ) : ℝ) ≤ A.sourceLoss w i := by
      exact_mod_cast A.left_span_holes_le_sourceLoss hw hconv hS
    exact hh.trans hU
  have hright : ((indexSpan (A.symm.localIndices hw S) - (A.symm.localIndices hw S).length : ℕ) : ℝ) ≤ ε*w := by
    rw [A.symm.localIndices_span hw hT, localIndices_length]
    have hh : (((A.rightSpan S).card - S.card : ℕ) : ℝ) ≤ A.spanLoss w i := by
      exact_mod_cast A.right_span_holes_le_spanLoss hconv hS
    exact hh.trans hV
  obtain ⟨hlabels, k, hk⟩ := hlocal (x.get i) (y.get j) _ _
    (A.localIndices_sorted hw hS) (A.symm.localIndices_sorted hw hT) (by simp)
    hbound hleft hright (A.localIndices_letters hw (by rfl))
  refine ⟨hlabels, ?_⟩
  rw [localIndices, localIndices, zip_ofFn] at hk
  obtain ⟨p, hp⟩ := List.mem_ofFn.mp hk
  refine ⟨S.orderEmbOfFin rfl p, S.orderEmbOfFin_mem rfl p, ?_⟩
  have hl := congrArg (fun z : Fin w × Fin w => z.1.val) hp
  have hr := congrArg (fun z : Fin w × Fin w => z.2.val) hp
  exact hl.trans hr.symm

theorem good_block_anchor (hw : 0 < w) {ε : ℝ} (hε : ε ≤ 1/10)
    (hlocal : AnchorLocal ε c) (A : WordMatching (encode c x) (encode c y) q)
    (i : Fin x.length) (hU : (A.sourceLoss w i : ℝ) ≤ ε*w)
    (hV : (A.spanLoss w i : ℝ) ≤ ε*w) :
    ∃ j : Fin y.length, x.get i = y.get j ∧
      ∃ k ∈ A.blockPair w i j, (A.left k).val%w = (A.right k).val%w := by
  have hc := A.sourceBlock_card_le hw i
  have hs := A.card_le_rightSpan (A.sourceBlock w i)
  have hcardU : A.sourceLoss w i + (A.sourceBlock w i).card = w := Nat.sub_add_cancel hc
  have hcardV : A.spanLoss w i + (A.sourceBlock w i).card = (A.rightSpan (A.sourceBlock w i)).card :=
    Nat.sub_add_cancel hs
  have hU' : (A.sourceLoss w i : ℝ) ≤ (w : ℝ)/10 := by nlinarith
  have hV' : (A.spanLoss w i : ℝ) ≤ (w : ℝ)/10 := by nlinarith
  have hsmall : (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w := by
    apply Nat.cast_le (α := ℝ) |>.mp
    have h1 : (A.spanLoss w i : ℝ) + (A.sourceBlock w i).card = (A.rightSpan (A.sourceBlock w i)).card := by exact_mod_cast hcardV
    have h2 : ((A.sourceBlock w i).card : ℝ) ≤ w := by exact_mod_cast hc
    push_cast
    linarith
  have hlarge : 3*w < 4*(A.sourceBlock w i).card := by
    apply Nat.cast_lt (α := ℝ) |>.mp
    have h1 : (A.sourceLoss w i : ℝ) + (A.sourceBlock w i).card = w := by exact_mod_cast hcardU
    have hp : (0 : ℝ) < w := by exact_mod_cast hw
    push_cast
    linarith
  obtain ⟨j, hj, hcard⟩ := A.exists_large_blockPair hw hsmall hlarge
  have hjlt : j < y.length := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [length_encode, Nat.mul_comm] using (A.right k).isLt
  exact ⟨⟨j, hjlt⟩, A.anchor_on_blockPair hw hlocal i ⟨j, hjlt⟩ hcard hU hV⟩

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem mod_injectiveOn (A : WordMatching x y q) {w i : ℕ} :
    Set.InjOn (fun k : Fin q => (A.left k).val%w) (↑(A.sourceBlock w i) : Set (Fin q)) := by
  intro k hk l hl he
  change (A.left k).val%w = (A.left l).val%w at he
  apply A.left.injective
  apply Fin.ext
  have h1 := Nat.mod_add_div (A.left k).val w
  have h2 := Nat.mod_add_div (A.left l).val w
  rw [(A.mem_sourceBlock w i k).mp hk, he] at h1
  rw [(A.mem_sourceBlock w i l).mp hl] at h2
  omega

theorem block_before_card_le (A : WordMatching x y q) {w i : ℕ}
    {k : Fin q} (hk : k ∈ A.sourceBlock w i) :
    ((A.sourceBlock w i).filter (fun l => l < k)).card ≤ (A.left k).val%w := by
  let T := (A.sourceBlock w i).filter (fun l => l < k)
  let f := fun l : Fin q => (A.left l).val%w
  have hinj : Set.InjOn f (↑T : Set (Fin q)) := A.mod_injectiveOn.mono (by
    intro l hl; exact (Finset.mem_filter.mp hl).1)
  have hsub : T.image f ⊆ Finset.Iio ((A.left k).val%w) := by
    intro j hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hl, hlt⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_Iio.mpr (A.mod_strictMono_on_block hl hk hlt)
  rw [← Finset.card_image_of_injOn hinj]
  simpa only [Nat.card_Iio] using Finset.card_le_card hsub

theorem block_after_card_le (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {k : Fin q} (hk : k ∈ A.sourceBlock w i) :
    ((A.sourceBlock w i).filter (fun l => k < l)).card ≤ w - (A.left k).val%w - 1 := by
  let T := (A.sourceBlock w i).filter (fun l => k < l)
  let f := fun l : Fin q => (A.left l).val%w
  have hinj : Set.InjOn f (↑T : Set (Fin q)) := A.mod_injectiveOn.mono (by
    intro l hl; exact (Finset.mem_filter.mp hl).1)
  have hsub : T.image f ⊆ Finset.Ioo ((A.left k).val%w) w := by
    intro j hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hl, hlt⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_Ioo.mpr ⟨A.mod_strictMono_on_block hk hl hlt, Nat.mod_lt _ hw⟩
  rw [← Finset.card_image_of_injOn hinj]
  simpa only [Nat.card_Ioo] using Finset.card_le_card hsub

theorem two_anchors_source_loss (A : WordMatching x y q) {w i j t : ℕ} (hw : 0 < w)
    (hij : i < j) {k l : Fin q} (hk : k ∈ A.blockPair w i t) (hl : l ∈ A.blockPair w j t)
    (hkmod : (A.left k).val%w = (A.right k).val%w)
    (hlmod : (A.left l).val%w = (A.right l).val%w) :
    w ≤ A.sourceLoss w i + A.sourceLoss w j := by
  obtain ⟨hki, hkt⟩ := Finset.mem_inter.mp hk
  obtain ⟨hlj, hlt⟩ := Finset.mem_inter.mp hl
  let T := (A.sourceBlock w i).filter (fun v => k ≤ v)
  let U := (A.sourceBlock w j).filter (fun v => v ≤ l)
  have hdis : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    exact (lt_irrefl v) (A.sourceBlock_order hij (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hu).1)
  have hmaps : Set.MapsTo A.right (↑(T ∪ U) : Set (Fin q))
      (↑(Finset.Icc (A.right k) (A.right l)) : Set (Fin y.length)) := by
    intro v hv
    change A.right v ∈ Finset.Icc (A.right k) (A.right l)
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hv, hkv⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_Icc.mpr ⟨A.right.monotone hkv,
        A.right.monotone (A.sourceBlock_order hij hv hlj).le⟩
    · obtain ⟨hv, hvl⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_Icc.mpr ⟨A.right.monotone (A.sourceBlock_order hij hki hv).le,
        A.right.monotone hvl⟩
  have hc := Finset.card_le_card_of_injOn A.right hmaps A.right.injective.injOn
  rw [Finset.card_union_of_disjoint hdis, Fin.card_Icc] at hc
  have hb := A.block_before_card_le hki
  have ha := A.block_after_card_le hw hlj
  have hTi : T.card + ((A.sourceBlock w i).filter (fun v => v < k)).card = (A.sourceBlock w i).card := by
    simpa only [not_le] using Finset.card_filter_add_card_filter_not (s := A.sourceBlock w i) (p := fun v => k ≤ v)
  have hUj : U.card + ((A.sourceBlock w j).filter (fun v => l < v)).card = (A.sourceBlock w j).card := by
    simpa only [not_le] using Finset.card_filter_add_card_filter_not (s := A.sourceBlock w j) (p := fun v => v ≤ l)
  have hXi : A.sourceLoss w i + (A.sourceBlock w i).card = w := Nat.sub_add_cancel (A.sourceBlock_card_le hw i)
  have hXj : A.sourceLoss w j + (A.sourceBlock w j).card = w := Nat.sub_add_cancel (A.sourceBlock_card_le hw j)
  have hrk := Nat.mod_add_div (A.right k).val w
  have hrl := Nat.mod_add_div (A.right l).val w
  have hkt' : (A.right k).val/w = t := (A.symm.mem_sourceBlock w t k).mp hkt
  have hlt' : (A.right l).val/w = t := (A.symm.mem_sourceBlock w t l).mp hlt
  rw [hkt', ← hkmod] at hrk
  rw [hlt', ← hlmod] at hrl
  have hklt := Nat.mod_lt (A.left k).val hw
  have hllt := Nat.mod_lt (A.left l).val hw
  have hkl : (A.right k).val ≤ (A.right l).val := A.right.monotone (A.sourceBlock_order hij hki hlj).le
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem anchors_strict_order (hw : 0 < w) {ε : ℝ} (hε : ε ≤ 1/10)
    (A : WordMatching (encode c x) (encode c y) q)
    {i j : Fin x.length} {s t : Fin y.length} (hij : i < j)
    {k l : Fin q} (hk : k ∈ A.blockPair w i s) (hl : l ∈ A.blockPair w j t)
    (hkmod : (A.left k).val%w = (A.right k).val%w)
    (hlmod : (A.left l).val%w = (A.right l).val%w)
    (hUi : (A.sourceLoss w i : ℝ) ≤ ε*w) (hUj : (A.sourceLoss w j : ℝ) ≤ ε*w) : s < t := by
  have hkl : k < l := A.sourceBlock_order hij (Finset.mem_inter.mp hk).1 (Finset.mem_inter.mp hl).1
  have hks : (A.right k).val/w = s.val := (A.symm.mem_sourceBlock w s k).mp (Finset.mem_inter.mp hk).2
  have hlt : (A.right l).val/w = t.val := (A.symm.mem_sourceBlock w t l).mp (Finset.mem_inter.mp hl).2
  have hquot := Nat.div_le_div_right (c := w) (show (A.right k).val ≤ (A.right l).val from (A.right.strictMono hkl).le)
  rw [hks, hlt] at hquot
  have hne : s ≠ t := by
    intro he
    have hl' : l ∈ A.blockPair w j s := by simpa only [he] using hl
    have hc := A.two_anchors_source_loss hw hij hk hl' hkmod hlmod
    have hc' : (w : ℝ) ≤ A.sourceLoss w i + A.sourceLoss w j := by exact_mod_cast hc
    have hp : (0 : ℝ) < w := by exact_mod_cast hw
    nlinarith
  exact lt_of_le_of_ne hquot hne

theorem good_blocks_le_lcs (hw : 0 < w) {ε : ℝ} (hε : ε ≤ 1/10)
    (hlocal : AnchorLocal ε c) (A : WordMatching (encode c x) (encode c y) q) :
    (Finset.univ.filter (fun i : Fin x.length =>
      (A.sourceLoss w i : ℝ) ≤ ε*w ∧ (A.spanLoss w i : ℝ) ≤ ε*w)).card ≤ lcs x y := by
  classical
  let G := Finset.univ.filter (fun i : Fin x.length =>
      (A.sourceLoss w i : ℝ) ≤ ε*w ∧ (A.spanLoss w i : ℝ) ≤ ε*w)
  let e := G.orderEmbOfFin rfl
  have hgood (k : Fin G.card) : (A.sourceLoss w (e k) : ℝ) ≤ ε*w ∧ (A.spanLoss w (e k) : ℝ) ≤ ε*w :=
    (Finset.mem_filter.mp (G.orderEmbOfFin_mem rfl k)).2
  have hex (k : Fin G.card) : ∃ j : Fin y.length, x.get (e k) = y.get j ∧
      ∃ p ∈ A.blockPair w (e k) j, (A.left p).val%w = (A.right p).val%w :=
    A.good_block_anchor hw hε hlocal (e k) (hgood k).1 (hgood k).2
  choose f hlabels p hp hmod using hex
  have hmono : StrictMono f := by
    intro k l hkl
    exact A.anchors_strict_order hw hε (e.strictMono hkl) (hp k) (hp l)
      (hmod k) (hmod l) (hgood k).1 (hgood l).1
  let B : WordMatching x y G.card :=
    { left := e
      right := OrderEmbedding.ofStrictMono f hmono
      letters := hlabels }
  exact B.le_lcs

end WordMatching

theorem anchor_deficit_lower {α : Type*} {w : ℕ} (hw : 0 < w) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/10) {c : α → Fin w → Bool} (hlocal : AnchorLocal ε c)
    (x y : List α) (hlen : x.length = y.length) :
    (ε/2) * w * deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) := by
  classical
  obtain ⟨A⟩ := exists_lcs_matching (encode c x) (encode c y)
  let U : Fin x.length → ℝ := fun i => A.sourceLoss w i
  let V : Fin x.length → ℝ := fun i => A.spanLoss w i
  let G := Finset.univ.filter (fun i : Fin x.length => U i ≤ ε*w ∧ V i ≤ ε*w)
  let B := Gᶜ
  have hG : G.card ≤ lcs x y := A.good_blocks_le_lcs hw hε hlocal
  have hB : deficit x y ≤ B.card := by
    have hc := Finset.card_compl G
    simp only [Fintype.card_fin] at hc
    dsimp only [B, deficit]
    omega
  have hbad (i : Fin x.length) (hi : i ∈ B) : ε*w ≤ U i + V i := by
    have hn : ¬(U i ≤ ε*w ∧ V i ≤ ε*w) := by
      simpa only [B, G, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hu : 0 ≤ U i := Nat.cast_nonneg _
    have hv : 0 ≤ V i := Nat.cast_nonneg _
    push Not at hn
    by_cases hh : U i ≤ ε*w
    · have := hn hh
      linarith
    · push Not at hh
      linarith
  have hsumU : ∑ i, U i = (deficit (encode c x) (encode c y) : ℝ) := by
    have h := A.sum_sourceLoss hw (length_encode c x)
    simp only [U, deficit, length_encode]
    exact_mod_cast h
  have hsumV : ∑ i, V i ≤ (deficit (encode c x) (encode c y) : ℝ) := by
    have h := A.sum_spanLoss_le hw (length_encode c x) (by rw [length_encode, hlen])
    simp only [V, deficit, length_encode]
    exact_mod_cast h
  have hcost : ε*w*(B.card : ℝ) ≤ ∑ i, (U i + V i) := calc
    _ = ∑ _i ∈ B, ε*w := by simp [mul_comm]
    _ ≤ ∑ i ∈ B, (U i + V i) := Finset.sum_le_sum hbad
    _ ≤ ∑ i, (U i + V i) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [Finset.sum_add_distrib, hsumU] at hcost
  have hmul := mul_le_mul_of_nonneg_left (show (deficit x y : ℝ) ≤ B.card by exact_mod_cast hB)
    (mul_nonneg hε0 (Nat.cast_nonneg w))
  nlinarith

end FiniteCircle

end OAI
