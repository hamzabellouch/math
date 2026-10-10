import OAI.Combinatorics.FiniteCircle.PhaseCost

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

@[simp] theorem mem_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) (j : MaskTag h p l) :
    j ∈ maskTags h p l := by
  rcases j with ⟨k,b⟩
  simp only [maskTags, List.mem_flatten, List.mem_ofFn]
  exact ⟨_, ⟨k, rfl⟩, List.mem_ofFn.mpr ⟨b,rfl⟩⟩

@[simp] theorem length_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    (maskTags h p l).length = ∑ k : Fin h, p l k := by
  simp [maskTags, List.length_flatten, List.map_ofFn, List.sum_ofFn]

theorem nodup_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    (maskTags h p l).Nodup := by
  classical
  unfold maskTags
  have he : (List.ofFn (fun k : Fin h => List.ofFn (fun b : Fin (p l k) => (Sigma.mk k b : MaskTag h p l)))) =
      (List.ofFn (fun k : Fin h => k)).map (fun k : Fin h => List.ofFn (fun b : Fin (p l k) => (Sigma.mk k b : MaskTag h p l))) := by simp only [List.map_ofFn]; rfl
  rw [he, ← List.flatMap_def]
  change ((List.ofFn (fun k : Fin h => k)).flatMap
    (fun k : Fin h => List.ofFn (fun b : Fin (p l k) => (Sigma.mk k b : MaskTag h p l)))).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro k _
    apply List.nodup_ofFn.mpr
    intro a b hab
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    apply List.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,hu⟩ := List.mem_ofFn.mp ha
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp hb
    have he : i = j := congrArg Sigma.fst (hu.trans hv.symm)
    exact (Fin.ne_of_lt hij) he

noncomputable def maskLength (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ) : ℕ → ℕ
  | 0 => M
  | l+1 => (R*period h p (l+1))*((maskTags h p (l+1)).length*maskLength h p R M l)

@[simp] theorem length_maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M l) : (maskWord h p R M l v).length = maskLength h p R M l := by
  induction l with
  | zero =>
    have he := maskWord.eq_1 h p R M v
    dsimp only [MaskState] at v
    dsimp only [MaskAlphabet] at he
    have hh := congrArg (@List.length Bool) he
    simp only [List.length_map, List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap,
      List.length_range] at hh
    exact hh
  | succ l ih =>
    change ((List.range (R*period h p (l+1))).flatMap (fun a =>
      taggedRow (maskTags h p (l+1)) (fun j => maskWord h p R M l
        (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j))))).length = _
    rw [length_flatMap_uniform _ _ ((maskTags h p (l+1)).length*maskLength h p R M l)]
    · simp [maskLength]
    · intro a _
      apply length_flatMap_uniform
      intro j _
      simp [ih]

@[simp] theorem shiftMaskState_zero (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (v : MaskState h p M l) : shiftMaskState h p M l v 0 = v := by
  induction l with
  | zero => change ZMod M at v; exact add_zero v
  | succ l ih => funext j; exact ih (v j)

theorem shiftMaskState_add (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (v : MaskState h p M l) (a b : ZMod M) :
    shiftMaskState h p M l (shiftMaskState h p M l v a) b =
      shiftMaskState h p M l v (a+b) := by
  induction l with
  | zero => change ZMod M at v; exact add_assoc v a b
  | succ l ih => funext j; exact ih (v j)

theorem shiftMaskState_change_base (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (v : MaskState h p M l) (θ a b : ZMod M) :
    shiftMaskState h p M l (shiftMaskState h p M l v θ) b =
      shiftMaskState h p M l (shiftMaskState h p M l v a) (θ+b-a) := by
  rw [shiftMaskState_add, shiftMaskState_add]
  congr 1
  abel

def maskRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (a : ℕ) : List (MaskAlphabet h p (l+1)) :=
  taggedRow (maskTags h p (l+1)) (fun j => maskWord h p R M l
    (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)))

@[simp] theorem length_maskRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (a : ℕ) :
    (maskRow h p R M l v a).length = (maskTags h p (l+1)).length*maskLength h p R M l := by
  change (MaskTag h p (l+1) → MaskState h p M l) at v
  change (taggedRow (maskTags h p (l+1)) (fun j => maskWord h p R M l
    (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)))).length = _
  unfold taggedRow
  apply length_flatMap_uniform
  intro j _
  rw [List.length_map, length_maskWord]

theorem segment_maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (a : Fin (R*period h p (l+1))) :
    segment (maskWord h p R M (l+1) v)
        (a.val*((maskTags h p (l+1)).length*maskLength h p R M l))
        ((maskTags h p (l+1)).length*maskLength h p R M l) = maskRow h p R M l v a := by
  have he := segment_flatMap_uniform (List.range (R*period h p (l+1)))
    (maskRow h p R M l v) _ (fun a _ => length_maskRow h p R M l v a)
    ⟨a.val, by simp⟩
  change segment ((List.range (R*period h p (l+1))).flatMap (maskRow h p R M l v)) _ _ = _
  simpa only [List.get_eq_getElem, List.getElem_range] using he

theorem tag_get_maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (hL : 0 < maskLength h p R M l)
    (ht : 0 < (maskTags h p (l+1)).length)
    (k : Fin (maskWord h p R M (l+1) v).length) :
    (maskTags h p (l+1)).idxOf ((maskWord h p R M (l+1) v).get k).1 =
      (k.val/maskLength h p R M l)%(maskTags h p (l+1)).length := by
  classical
  exact tag_get_rows _ (nodup_maskTags h p (l+1)) _ hL ht
    (fun _ _ _ _ => length_maskWord ..) k

 theorem fin_orderEmbedding_lower {q n : ℕ} (e : Fin q ↪o Fin n) (i : Fin q) :
    i.val ≤ (e i).val := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have he := e.strictMono (Fin.castSucc_lt_succ (i := i))
      change (e i.castSucc).val < (e i.succ).val at he
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt (ih.trans_lt he))

 theorem fin_orderEmbedding_upper {q n : ℕ} (e : Fin q ↪o Fin n) (i : Fin q) :
    (e i).val ≤ i.val+(n-q) := by
  let r : Fin q ↪o Fin n := OrderEmbedding.ofStrictMono (fun j => (e j.rev).rev) (by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (e.strictMono (Fin.rev_lt_rev.mpr hab)))
  have h := fin_orderEmbedding_lower r i.rev
  change i.rev.val ≤ n-((e i.rev.rev).val+1) at h
  simp only [Fin.rev_rev, Fin.val_rev] at h
  have hqn : q ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  have hi := i.isLt
  have hei := (e i).isLt
  omega

 theorem threshold_neighborhood_card {n : ℕ} (t E : ℕ) :
    (Finset.univ.filter (fun i : Fin n => t ≤ i.val+E ∧ i.val < t+E)).card ≤ 2*E := by
  classical
  have hc : (Finset.univ.filter (fun i : Fin n => t ≤ i.val+E ∧ i.val < t+E)).card ≤
      (Finset.Ico (t-E) (t+E)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro i hi
      have hi := (Finset.mem_filter.mp hi).2
      exact Finset.mem_Ico.mpr ⟨by omega, hi.2⟩
    · intro i _ j _ hij
      exact Fin.ext hij
  rw [Nat.card_Ico] at hc
  omega

theorem hamming_le_five_deficit {n : ℕ} (f g : Fin n → Bool) (t u : ℕ)
    (hg : ∀ i j : Fin n, g i ≠ g j →
      (i.val < t ∧ t ≤ j.val) ∨ (j.val < t ∧ t ≤ i.val) ∨
      (i.val < u ∧ u ≤ j.val) ∨ (j.val < u ∧ u ≤ i.val)) :
    (Finset.univ.filter (fun i => f i ≠ g i)).card ≤
      5*deficit (List.ofFn f) (List.ofFn g) := by
  classical
  obtain ⟨A⟩ := exists_lcs_matching (List.ofFn f) (List.ofFn g)
  let q := lcs (List.ofFn f) (List.ofFn g)
  let E := n-q
  let L : Fin q ↪o Fin n := A.left.trans (Fin.castOrderIso (List.length_ofFn)).toOrderEmbedding
  let R : Fin q ↪o Fin n := A.right.trans (Fin.castOrderIso (List.length_ofFn)).toOrderEmbedding
  have hletters (i : Fin q) : f (L i) = g (R i) := by
    change f (Fin.cast (List.length_ofFn) (A.left i)) = g (Fin.cast (List.length_ofFn) (A.right i))
    simpa only [List.get_ofFn] using A.letters i
  have hdisp (i : Fin q) : (L i).val ≤ (R i).val+E ∧ (R i).val ≤ (L i).val+E := by
    have hl := fin_orderEmbedding_lower L i
    have hu := fin_orderEmbedding_upper L i
    have hl' := fin_orderEmbedding_lower R i
    have hu' := fin_orderEmbedding_upper R i
    exact ⟨by omega, by omega⟩
  let U := Finset.univ \ (Finset.univ.image L)
  let B (a : ℕ) := Finset.univ.filter (fun i : Fin n => a ≤ i.val+E ∧ i.val < a+E)
  have hUC : U.card = E := by
    dsimp [U, E]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_image_of_injective _ L.injective]
    simp
  have hsub : Finset.univ.filter (fun i => f i ≠ g i) ⊆ U ∪ (B t ∪ B u) := by
    intro i hi
    have hd := (Finset.mem_filter.mp hi).2
    by_cases hu : i ∈ U
    · exact Finset.mem_union_left _ hu
    · have him : i ∈ Finset.univ.image L := by simpa [U] using hu
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp him
      have hg' : g (L k) ≠ g (R k) := by rw [← hletters]; exact Ne.symm hd
      have hc := hg (L k) (R k) hg'
      have hm := hdisp k
      apply Finset.mem_union_right
      rcases hc with hc | hc | hc | hc
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le U (B t ∪ B u))
  have hb := Finset.card_union_le (B t) (B u)
  have ht := threshold_neighborhood_card (n := n) t E
  have hu := threshold_neighborhood_card (n := n) u E
  change (B t).card ≤ 2*E at ht
  change (B u).card ≤ 2*E at hu
  have hde : deficit (List.ofFn f) (List.ofFn g) = E := by simp [deficit, E, q]
  rw [hde]
  omega

def halfBit {M : ℕ} (v b : ZMod M) : Bool := decide ((b-v).val < M/2)

 theorem zmod_val_sub_cases {M : ℕ} [NeZero M] (b v : ZMod M) :
    (b-v).val = if v.val ≤ b.val then b.val-v.val else M+b.val-v.val := by
  split_ifs with h
  · exact ZMod.val_sub h
  · have hlt : b.val < v.val := by omega
    have hv : v ≠ 0 := by intro he; simp [he] at h
    rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val, ite_eq_right hv]
    have hb := b.val_lt
    have hv' := v.val_lt
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

 theorem halfBit_interval {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v b : ZMod M) :
    halfBit v b = if v.val ≤ M/2 then
      decide (v.val ≤ b.val ∧ b.val < v.val+M/2)
    else decide (b.val < v.val-M/2 ∨ v.val ≤ b.val) := by
  unfold halfBit
  rw [zmod_val_sub_cases]
  split_ifs with h h' <;> apply Bool.eq_iff_iff.mpr <;> simp only [decide_eq_true_eq] <;>
    have hv := v.val_lt <;> have hb := b.val_lt <;> omega

 theorem halfBit_thresholds {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v : ZMod M) :
    ∀ i j : Fin M, halfBit v (i.val : ZMod M) ≠ halfBit v (j.val : ZMod M) →
      (i.val < v.val ∧ v.val ≤ j.val) ∨ (j.val < v.val ∧ v.val ≤ i.val) ∨
      (i.val < (v.val+M/2)%M ∧ (v.val+M/2)%M ≤ j.val) ∨
      (j.val < (v.val+M/2)%M ∧ (v.val+M/2)%M ≤ i.val) := by
  intro i j hij
  rw [halfBit_interval he, halfBit_interval he] at hij
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij
  by_cases hv : v.val < M/2
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)] at hij
    rw [Nat.mod_eq_of_lt (by omega : v.val+M/2 < M)]
    have hh : ¬ ((v.val ≤ i.val ∧ i.val < v.val+M/2) ↔
      (v.val ≤ j.val ∧ j.val < v.val+M/2)) := by simpa only [ne_eq, decide_eq_decide] using hij
    omega
  · have hmod : (v.val+M/2)%M = v.val-M/2 := by
      have hval := v.val_lt
      have hh : v.val+M/2 = (v.val-M/2)+M := by omega
      rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    by_cases hv' : v.val = M/2
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), hv'] at hij
      have hi := i.isLt; have hj := j.isLt
      have hh : ¬ ((M/2 ≤ i.val ∧ i.val < M/2+M/2) ↔
        (M/2 ≤ j.val ∧ j.val < M/2+M/2)) := by simpa only [ne_eq, decide_eq_decide] using hij
      omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hij
      have hh : ¬ ((i.val < v.val-M/2 ∨ v.val ≤ i.val) ↔
        (j.val < v.val-M/2 ∨ v.val ≤ j.val)) := by simpa only [ne_eq, decide_eq_decide] using hij
      omega

noncomputable def halfHamming {M : ℕ} [NeZero M] (v w : ZMod M) : ℕ :=
  (Finset.univ.filter (fun b : ZMod M => halfBit v b ≠ halfBit w b)).card

 theorem halfHamming_symm {M : ℕ} [NeZero M] (v w : ZMod M) :
    halfHamming v w = halfHamming w v := by
  unfold halfHamming
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

 theorem halfHamming_translate {M : ℕ} [NeZero M] (v w a : ZMod M) :
    halfHamming (v+a) (w+a) = halfHamming v w := by
  classical
  unfold halfHamming
  apply Finset.card_bij (fun b _ => b-a)
  · intro b hb
    have hb := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [halfBit, sub_add_eq_sub_sub, sub_right_comm] using hb
  · intro b _ c _ hbc
    exact sub_left_injective hbc
  · intro b hb
    refine ⟨b+a, ?_, by simp⟩
    have hb := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [halfBit, add_sub_add_right_eq_sub] using hb

 theorem halfHamming_zero_neg {M : ℕ} [NeZero M] (v : ZMod M) :
    halfHamming 0 (-v) = halfHamming 0 v := by
  have h := halfHamming_translate (0 : ZMod M) (-v) v
  simp only [zero_add, neg_add_cancel] at h
  exact h.symm.trans (halfHamming_symm _ _)

 theorem halfHamming_zero_small {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v : ZMod M) (hv : v.val ≤ M/2) : halfHamming 0 v = 2*v.val := by
  classical
  let D := Finset.univ.filter (fun b : ZMod M => halfBit 0 b ≠ halfBit v b)
  have hmem (b : ZMod M) : b ∈ D ↔ b.val < v.val ∨ (M/2 ≤ b.val ∧ b.val < M/2+v.val) := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [halfBit_interval he, halfBit_interval he, ite_eq_left hv]
    simp only [ZMod.val_zero, Nat.zero_le, ite_true, zero_add, true_and]
    have hb := b.val_lt
    simp only [ne_eq, decide_eq_decide]
    omega
  let f : Bool × Fin v.val → ZMod M := fun a => ((if a.1 then M/2 else 0)+a.2.val : ℕ)
  have hfval (a : Bool × Fin v.val) : (f a).val = (if a.1 then M/2 else 0)+a.2.val := by
    change (((if a.1 then M/2 else 0)+a.2.val : ℕ) : ZMod M).val = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    cases a with | mk t b => cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] <;> omega
  have hcard : (Finset.univ : Finset (Bool × Fin v.val)).card = D.card := by
    apply Finset.card_bij (fun a _ => f a)
    · intro a _
      rw [hmem, hfval]
      cases a with | mk t b => cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] <;> omega
    · intro a _ b _ hab
      have hab' := congrArg ZMod.val hab
      rw [hfval, hfval] at hab'
      rcases a with ⟨ta,ia⟩
      rcases b with ⟨tb,ib⟩
      have hi := ia.isLt
      have hj := ib.isLt
      cases ta <;> cases tb <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hab'
      · exact Prod.ext rfl (Fin.ext hab')
      · omega
      · omega
      · exact Prod.ext rfl (Fin.ext (Nat.add_left_cancel hab'))
    · intro b hb
      rw [hmem] at hb
      rcases hb with hb | hb
      · refine ⟨(false,⟨b.val,hb⟩), Finset.mem_univ _, ?_⟩
        apply ZMod.val_injective
        rw [hfval]
        simp
      · refine ⟨(true,⟨b.val-M/2, by omega⟩), Finset.mem_univ _, ?_⟩
        apply ZMod.val_injective
        rw [hfval]
        simp only [↓reduceIte]
        omega
  simpa [halfHamming, D] using hcard.symm

 theorem halfHamming_eq {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v w : ZMod M) : halfHamming v w = 2*(w-v).valMinAbs.natAbs := by
  have ht : halfHamming v w = halfHamming 0 (w-v) := by
    have hh := halfHamming_translate v w (-v)
    simpa only [add_neg_cancel, ← sub_eq_add_neg] using hh.symm
  rw [ht]
  by_cases h : (w-v).val ≤ M/2
  · rw [halfHamming_zero_small he _ h, ZMod.valMinAbs_def_pos, ite_eq_left h, Int.natAbs_natCast]
  · have hh : (-(w-v)).val ≤ M/2 := by
      rw [ZMod.neg_val, ite_eq_right]
      · have hv := (w-v).val_lt
        omega
      · intro hz
        simp [hz] at h
    rw [← halfHamming_zero_neg (w-v), halfHamming_zero_small he _ hh]
    have ha : (-(w-v)).valMinAbs.natAbs = (-(w-v)).val := by
      rw [ZMod.valMinAbs_def_pos, ite_eq_left hh, Int.natAbs_natCast]
    rw [← ha, ZMod.natAbs_valMinAbs_neg]

 theorem halfHamming_fin {M : ℕ} [NeZero M] (v w : ZMod M) :
    (Finset.univ.filter (fun i : Fin M => halfBit v (i.val : ZMod M) ≠
      halfBit w (i.val : ZMod M))).card = halfHamming v w := by
  classical
  unfold halfHamming
  apply Finset.card_bij (fun b _ => (b.val : ZMod M))
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  · intro b _ c _ hbc
    have hh := congrArg ZMod.val hbc
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt c.isLt] at hh
    exact Fin.ext hh
  · intro b hb
    refine ⟨⟨b.val,b.val_lt⟩, ?_, ZMod.natCast_zmod_val b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa only [ZMod.natCast_zmod_val] using hb

 theorem maskWord_zero_eq {h M R : ℕ} {p : ℕ → ℕ → ℕ} (v : ZMod M) :
    maskWord h p R M 0 v = List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)) := by
  have he := maskWord.eq_1 h p R M v
  dsimp only [MaskState, MaskAlphabet] at he
  refine he.trans ?_
  simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Function.comp_def, halfBit]

 theorem halfCircle_separation {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v θ : ZMod M) :
    (M:ℝ)*circleCost θ/4 ≤
      (deficit (List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)))
        (List.ofFn (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))) : ℝ) := by
  have hh := hamming_le_five_deficit
    (fun i : Fin M => halfBit v (i.val : ZMod M))
    (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))
    (v+θ).val (((v+θ).val+M/2)%M) (halfBit_thresholds he (v+θ))
  rw [halfHamming_fin, halfHamming_eq he, add_sub_cancel_left] at hh
  have hr : 2*(θ.valMinAbs.natAbs : ℝ) ≤ 5*
      (deficit (List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)))
        (List.ofFn (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))) : ℝ) := by exact_mod_cast hh
  have hM : (M:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [circleCost, mul_div_cancel₀ _ hM]
  nlinarith [Nat.cast_nonneg (α := ℝ) θ.valMinAbs.natAbs]

noncomputable def subcircle {M p : ℕ} (hp : p ∣ M) : ZMod p →+ ZMod M :=
  ZMod.lift p ⟨(AddMonoidHom.mulRight (M/p : ZMod M)).comp (Int.castAddHom _), by
    change ((p : ℤ) : ZMod M) * ((M/p : ℕ) : ZMod M) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' hp]
    simp⟩

@[simp] theorem subcircle_natCast {M p : ℕ} (hp : p ∣ M) (a : ℕ) :
    subcircle hp (a : ZMod p) = (M/p : ZMod M)*(a : ZMod M) := by
  have he := ZMod.lift_coe p
    ⟨(AddMonoidHom.mulRight (M/p : ZMod M)).comp (Int.castAddHom _), by
      change ((p : ℤ) : ZMod M) * ((M/p : ℕ) : ZMod M) = 0
      rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' hp]
      simp⟩ (a : ℤ)
  simpa [subcircle, Int.castAddHom, mul_comm] using he

@[simp] theorem subcircle_val {M p : ℕ} [NeZero p] (hp : p ∣ M) (a : ZMod p) :
    subcircle hp a = ((M/p*a.val : ℕ) : ZMod M) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [subcircle_natCast]
  simp

 theorem subcircle_injective {M p : ℕ} [NeZero M] [NeZero p] (hp : p ∣ M) :
    Function.Injective (subcircle hp) := by
  apply (injective_iff_map_eq_zero (subcircle hp)).mpr
  intro a ha
  rw [subcircle_val] at ha
  have hd := (ZMod.natCast_eq_zero_iff (M/p*a.val) M).mp ha
  have hM : M/p*p = M := Nat.div_mul_cancel hp
  have hpos : 0 < M/p := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hp) (NeZero.pos p)
  have hd' : p ∣ a.val := by
    exact (Nat.mul_dvd_mul_iff_left hpos).mp (show M/p*p ∣ M/p*a.val by simpa only [hM] using hd)
  have haz := Nat.eq_zero_of_dvd_of_lt hd' a.val_lt
  exact (ZMod.val_eq_zero a).mp haz

theorem add_ne_zero_of_coprime_orders {G : Type*} [AddCommGroup G] {x y : G}
    {q r : ℕ} (hc : q.Coprime r) (hx : x ≠ 0) (hq : q • x = 0) (hr : r • y = 0) :
    x+y ≠ 0 := by
  intro h
  have he : y = -x := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  rw [he, smul_neg, neg_eq_zero] at hr
  have hq' := addOrderOf_dvd_of_nsmul_eq_zero hq
  have hr' := addOrderOf_dvd_of_nsmul_eq_zero hr
  have ho : addOrderOf x = 1 := Nat.dvd_one.mp (hc ▸ Nat.dvd_gcd hq' hr')
  exact hx (AddMonoid.addOrderOf_eq_one_iff.mp ho)

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

theorem sub_le (f : PhaseCost G) (x y : G) : f (x-y) ≤ f x+f y := by
  simpa only [sub_eq_add_neg, f.neg] using f.add_le x (-y)

theorem le_pair (f : PhaseCost G) (x d : G) : f d ≤ f x+f (x+d) := by
  have h := f.sub_le (x+d) x
  simpa only [add_sub_cancel_left, add_comm] using h

theorem grid_pair_bound (f : PhaseCost G) {p : ℕ} [NeZero p]
    (φ : ZMod p →+ G) (x : G) :
    (p : ℝ)*f (φ 1) ≤ 2*∑ b : ZMod p, f (x+φ b) := by
  have hpairs := Finset.sum_le_sum (s := Finset.univ)
    (fun (b : ZMod p) _ => f.le_pair (x+φ b) (φ 1))
  have hs : ∑ b : ZMod p, f (x+φ b+φ 1) = ∑ b : ZMod p, f (x+φ b) := by
    simpa only [Equiv.coe_addRight, map_add, add_assoc] using
      Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) (fun b => f (x+φ b))
  simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Finset.sum_add_distrib, hs, two_mul] using hpairs

theorem prime_grid_bound (f : PhaseCost G) {p : ℕ} [NeZero p] (hp : p.Prime)
    (φ : ZMod p →+ G) (x : G) (z : ZMod p) (hz : z ≠ 0) :
    (p : ℝ)*f (φ 1) ≤ 2*∑ b : ZMod p, f (x+b.val • φ z) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : ∑ b : ZMod p, f (x+b.val • φ z) = ∑ b : ZMod p, f (x+φ b) := by
    have he (b : ZMod p) : b.val • φ z = φ (b*z) := by
      rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp_rw [he]
    exact Equiv.sum_comp (Equiv.mulRight₀ z hz) (fun b => f (x+φ b))
  rw [hs]
  exact f.grid_pair_bound φ x

end PhaseCost

end FiniteCircle

end OAI
