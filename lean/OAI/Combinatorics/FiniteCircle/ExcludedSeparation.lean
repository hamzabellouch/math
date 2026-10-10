import OAI.Combinatorics.FiniteCircle.MaskSeparation

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

noncomputable def excludedPhaseHom (m : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (hd : ∀ k : Fin m, p l k ∣ M) : MaskResidues m p l →+ (Fin m → ZMod M) where
  toFun z i := ∑ j ∈ Finset.univ.erase i, subcircle (hd j) (z j)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp [Finset.sum_add_distrib]

 theorem excludedPhaseHom_apply {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin m, p l k ∣ M) (z : MaskResidues m p l) (i : Fin m) :
    excludedPhaseHom m p M l hd z i = (∑ j, subcircle (hd j) (z j)) - subcircle (hd i) (z i) := by
  change (∑ j ∈ Finset.univ.erase i, subcircle (hd j) (z j)) = _
  exact (Finset.sum_erase_eq_sub (Finset.mem_univ i))

 theorem excludedPhaseHom_natCast (m : ℕ) (p : ℕ → ℕ → ℕ) (M l a : ℕ)
    (hd : ∀ k : Fin m, p l k ∣ M) (hn : ∀ k : Fin m, 0 < p l k) :
    excludedPhaseHom m p M l hd (fun k => (a : ZMod (p l k))) =
      excludedTranslation m p M l a := by
  ext i
  change (∑ j ∈ Finset.univ.erase i, subcircle (hd j) (a : ZMod (p l j))) = _
  unfold excludedTranslation
  apply Finset.sum_congr rfl
  intro j _
  let : NeZero (p l j) := ⟨(hn j).ne'⟩
  rw [subcircle_val, ZMod.val_natCast]

noncomputable def excludedCost (m : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin m), p l k ∣ M) (hn : ∀ l (k : Fin m), 0 < p l k) :
    ℕ → PhaseCost (ZMod M)
  | 0 => circlePhaseCost M
  | l+1 => by
    let : ∀ k : Fin m, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    exact (excludedCost m p M hd hn l).step (excludedPhaseHom m p M (l+1) (hd _))

 theorem excludedCost_le_half {m M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hm : 0 < m) (hd : ∀ l (k : Fin m), p l k ∣ M) (hn : ∀ l (k : Fin m), 0 < p l k)
    (l : ℕ) (x : ZMod M) : excludedCost m p M hd hn l x ≤ 1/2 := by
  induction l with
  | zero => exact circleCost_le_half x
  | succ l ih =>
    let : ∀ k : Fin m, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    exact ((excludedCost m p M hd hn l).infAverage_le_self _ x).trans ih

theorem excluded_active_average_lower {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hm : 2 ≤ m) (hd : ∀ k : Fin m, p l k ∣ M)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues m p l)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ i j : Fin m, z i ≠ 0 → i ≠ j →
      Q ≤ f (subcircle (hd i) (z i)-subcircle (hd j) (z j))) :
    (((Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card : ℝ)/(4*m))*Q ≤
      f.average (excludedPhaseHom m p M l hd) x z := by
  classical
  let A := Finset.univ.filter (fun k : Fin m => z k ≠ 0)
  let y (i : Fin m) := x+excludedPhaseHom m p M l hd z i
  let B := ∑ i : Fin m, f (y i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => f.nonneg _)
  have hpair (i j : Fin m) (hi : i ∈ A) (hij : i ≠ j) : Q ≤ f (y i)+f (y j) := by
    have he : subcircle (hd i) (z i)-subcircle (hd j) (z j) = y j-y i := by
      dsimp only [y]
      rw [excludedPhaseHom_apply, excludedPhaseHom_apply]
      abel
    exact (hq i j ((Finset.mem_filter.mp hi).2) hij).trans (by rw [he]; simpa [add_comm] using f.sub_le (y j) (y i))
  have hper (i : Fin m) (hi : i ∈ A) : ((m : ℝ) - 1)*Q ≤ (m:ℝ)*f (y i)+B := by
    have hh := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j hj =>
      hpair i j hi (Ne.symm (Finset.mem_erase.mp hj).1))
    have hsum : (∑ j ∈ Finset.univ.erase i, (f (y i)+f (y j))) ≤
        ∑ j : Fin m, (f (y i)+f (y j)) := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) (fun j _ _ => add_nonneg (f.nonneg _) (f.nonneg _))
    have hcard : (Finset.univ.erase i).card = m-1 := by simp
    rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hh
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh.trans hsum
  have hs : A.card ≤ m := by simpa using Finset.card_le_card (Finset.subset_univ A)
  have hsum := Finset.sum_le_sum (s := A) hper
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hpart : (∑ i ∈ A, f (y i)) ≤ B := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) (fun _ _ _ => f.nonneg _)
  have hsreal : (A.card : ℝ) ≤ m := by exact_mod_cast hs
  have hmreal : (2:ℝ) ≤ m := by exact_mod_cast hm
  have ha0 : (0:ℝ) ≤ A.card := by positivity
  have hsq : (A.card : ℝ)*Q ≤ 4*B := by
    have hupper : (m:ℝ)*(∑ i ∈ A, f (y i))+(A.card:ℝ)*B ≤ 2*m*B := by
      nlinarith [mul_le_mul_of_nonneg_left hpart (show (0 : ℝ) ≤ m by positivity),
        mul_le_mul_of_nonneg_right hsreal hB]
    have hbase : (A.card:ℝ)*((m : ℝ) - 1)*Q ≤ 2*m*B := by nlinarith
    have hnon : 0 ≤ (A.card:ℝ)*Q := mul_nonneg ha0 hQ
    nlinarith [mul_nonneg hnon (show (0:ℝ)≤(m : ℝ) - 2 by linarith)]
  change (A.card:ℝ)/(4*m)*Q ≤ B / Fintype.card (Fin m)
  rw [Fintype.card_fin]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < m)]
  calc
    _ = (A.card:ℝ)*Q/4 := by field_simp
    _ ≤ _ := by linarith

 theorem excluded_inactive_average_lower {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hm : 0 < m) (hd : ∀ k : Fin m, p l k ∣ M)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues m p l)
    (hs : 2*(Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card ≤ m) :
    (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
      f.average (excludedPhaseHom m p M l hd) x z := by
  classical
  let A := Finset.univ.filter (fun k : Fin m => z k ≠ 0)
  let N := Finset.univ.filter (fun k : Fin m => z k = 0)
  let Q := f (x+∑ k,subcircle (hd k) (z k))
  have hQ : 0 ≤ Q := f.nonneg _
  have hsum : (N.card:ℝ)*Q ≤ ∑ k : Fin m, f (x+excludedPhaseHom m p M l hd z k) := by
    calc
      _ = ∑ _k ∈ N, Q := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ k ∈ N, f (x+excludedPhaseHom m p M l hd z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [excludedPhaseHom_apply, (Finset.mem_filter.mp hk).2, map_zero, sub_zero]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => f.nonneg _)
  have hcard : A.card+N.card = m := by
    simpa only [Finset.card_univ, Fintype.card_fin, not_not] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun k : Fin m => z k ≠ 0)
  change 2*A.card ≤ m at hs
  have hN : (m:ℝ) ≤ 2*N.card := by exact_mod_cast (show m ≤ 2*N.card by omega)
  rw [PhaseCost.average, Fintype.card_fin, le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)]
  change (1/4:ℝ)*Q*m ≤ _
  have hh := mul_le_mul_of_nonneg_right hN hQ
  nlinarith

 theorem excluded_minimizer_options {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    [∀ k : Fin m, NeZero (p l k)]
    (hm : 2 ≤ m) (hd : ∀ k : Fin m, p l k ∣ M) (hn : ∀ k : Fin m, 0 < p l k)
    (f : PhaseCost (ZMod M)) (x : ZMod M) :
    ∃ z : MaskResidues m p l,
      (∀ Q : ℝ, 0 ≤ Q → (∀ i j : Fin m, z i ≠ 0 → i ≠ j →
        Q ≤ f (subcircle (hd i) (z i)-subcircle (hd j) (z j))) →
        (((Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card : ℝ)/(4*m))*Q ≤
          (f.step (excludedPhaseHom m p M l hd)) x) ∧
      (2*(Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card ≤ m →
        (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
          (f.step (excludedPhaseHom m p M l hd)) x) := by
  let : ∀ k : Fin m, NeZero (p l k) := fun k => ⟨(hn k).ne'⟩
  obtain ⟨z,hz⟩ := f.exists_average_eq (excludedPhaseHom m p M l hd) x
  refine ⟨z,?_,?_⟩
  · intro Q hQ hq
    change _ ≤ f.infAverage _ _
    rw [hz]
    exact excluded_active_average_lower hm hd f x z Q hQ hq
  · intro hs
    change _ ≤ f.infAverage _ _
    rw [hz]
    exact excluded_inactive_average_lower (by omega) hd f x z hs

 def excludedTags (m _l : ℕ) : List (Fin m) := List.ofFn id

@[simp] theorem length_excludedTags (m l : ℕ) : (excludedTags m l).length = m := by
  simp [excludedTags]

 theorem mem_excludedTags (m l : ℕ) (j : Fin m) : j ∈ excludedTags m l := by
  simp [excludedTags]

 theorem nodup_excludedTags (m l : ℕ) : (excludedTags m l).Nodup := by
  apply List.nodup_ofFn.mpr
  exact Function.injective_id

 theorem excludedWord_succ (m : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState m M (l+1)) :
    excludedWord m p R M (l+1) v = (List.range (R*period m p (l+1))).flatMap (fun a =>
      taggedRow (excludedTags m (l+1)) (fun j => excludedWord m p R M l
        (shiftExcludedState m M l (v j) (excludedTranslation m p M (l+1) a j)))) := by
  have he := excludedWord.eq_2 m p R M l v
  dsimp only [ExcludedAlphabet, ExcludedState] at he
  refine he.trans ?_
  unfold taggedRow excludedTags
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_id]
noncomputable def excludedLength (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ) : ℕ → ℕ
  | 0 => M
  | l+1 => (R*period h p (l+1))*((excludedTags h (l+1)).length*excludedLength h p R M l)

@[simp] theorem length_excludedWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M l) : (excludedWord h p R M l v).length = excludedLength h p R M l := by
  induction l with
  | zero =>
    have he := excludedWord.eq_1 h p R M v
    dsimp only [ExcludedAlphabet, ExcludedState] at he
    exact (congrArg List.length he).trans (List.length_ofFn)
  | succ l ih =>
    rw [excludedWord_succ]
    change ((List.range (R*period h p (l+1))).flatMap (fun a =>
      taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
        (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j))))).length = _
    rw [length_flatMap_uniform _ _ ((excludedTags h (l+1)).length*excludedLength h p R M l)]
    · simp [excludedLength]
    · intro a _
      apply length_flatMap_uniform
      intro j _
      simp [ih]

@[simp] theorem shiftExcludedState_zero (h : ℕ) (M l : ℕ)
    (v : ExcludedState h M l) : shiftExcludedState h M l v 0 = v := by
  induction l with
  | zero => change ZMod M at v; exact add_zero v
  | succ l ih => funext j; exact ih (v j)

theorem shiftExcludedState_add (h : ℕ) (M l : ℕ)
    (v : ExcludedState h M l) (a b : ZMod M) :
    shiftExcludedState h M l (shiftExcludedState h M l v a) b =
      shiftExcludedState h M l v (a+b) := by
  induction l with
  | zero => change ZMod M at v; exact add_assoc v a b
  | succ l ih => funext j; exact ih (v j)

theorem shiftExcludedState_change_base (h : ℕ) (M l : ℕ)
    (v : ExcludedState h M l) (θ a b : ZMod M) :
    shiftExcludedState h M l (shiftExcludedState h M l v θ) b =
      shiftExcludedState h M l (shiftExcludedState h M l v a) (θ+b-a) := by
  rw [shiftExcludedState_add, shiftExcludedState_add]
  congr 1
  abel

def excludedRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M (l+1)) (a : ℕ) : List (ExcludedAlphabet h M (l+1)) :=
  taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
    (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)))

@[simp] theorem length_excludedRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M (l+1)) (a : ℕ) :
    (excludedRow h p R M l v a).length = (excludedTags h (l+1)).length*excludedLength h p R M l := by
  change (Fin h → ExcludedState h M l) at v
  change (taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
    (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)))).length = _
  unfold taggedRow
  apply length_flatMap_uniform
  intro j _
  rw [List.length_map, length_excludedWord]

theorem segment_excludedWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M (l+1)) (a : Fin (R*period h p (l+1))) :
    segment (excludedWord h p R M (l+1) v)
        (a.val*((excludedTags h (l+1)).length*excludedLength h p R M l))
        ((excludedTags h (l+1)).length*excludedLength h p R M l) = excludedRow h p R M l v a := by
  have he := segment_flatMap_uniform (List.range (R*period h p (l+1)))
    (excludedRow h p R M l v) _ (fun a _ => length_excludedRow h p R M l v a)
    ⟨a.val, by simp⟩
  rw [excludedWord_succ]
  change segment ((List.range (R*period h p (l+1))).flatMap (excludedRow h p R M l v)) _ _ = _
  simpa only [List.get_eq_getElem, List.getElem_range] using he

theorem tag_get_excludedWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M (l+1)) (hL : 0 < excludedLength h p R M l)
    (ht : 0 < (excludedTags h (l+1)).length)
    (k : Fin (excludedWord h p R M (l+1) v).length) :
    (excludedTags h (l+1)).idxOf ((excludedWord h p R M (l+1) v).get k).1 =
      (k.val/excludedLength h p R M l)%(excludedTags h (l+1)).length := by
  classical
  have hl := congrArg List.length (excludedWord_succ h p R M l v)
  let k' := Fin.cast hl k
  have he := tag_get_rows (excludedTags h (l+1)) (nodup_excludedTags h (l+1))
    (fun a j => excludedWord h p R M l
      (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)))
    (N := R*period h p (l+1)) hL ht
    (fun _ _ _ _ => length_excludedWord ..) k'
  have hg : ((excludedWord h p R M (l+1) v).get k) =
      (((List.range (R*period h p (l+1))).flatMap (fun a =>
        taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
          (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j))))).get k') := by
    exact List.get_of_eq (excludedWord_succ h p R M l v) k
  rw [hg]
  exact he

 theorem excludedLength_pos {h M R : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hM : 0 < M) (hR : 0 < R) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) : 0 < excludedLength h p R M l := by
  induction l with
  | zero => exact hM
  | succ l ih =>
    unfold excludedLength
    apply Nat.mul_pos (Nat.mul_pos hR (Finset.prod_pos (fun k _ => hn _ k)))
    apply Nat.mul_pos _ ih
    simpa using hh

theorem excluded_separation {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (he : M = 2*(M/2)) (hh : 0 < h) (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (ht : ∀ l, 4 ≤ (excludedTags h l).length)
    (l : ℕ) (v : ExcludedState h M l) (θ : ZMod M) :
    (1/((2:ℝ)^l*4))*(excludedLength h p R M l)*excludedCost h p M hd hn l θ ≤
      (deficit (excludedWord h p R M l v)
        (excludedWord h p R M l (shiftExcludedState h M l v θ)) : ℝ) := by
  classical
  induction l generalizing θ with
  | zero =>
    change ZMod M at v
    change (1/((2:ℝ)^0*4))*M*circleCost θ ≤
      (deficit (excludedWord h p R M 0 v) (excludedWord h p R M 0 (v+θ)) : ℝ)
    have hbase (u : ZMod M) : (excludedWord h p R M 0 u).map Prod.snd =
        List.ofFn (fun i : Fin M => halfBit u (i.val : ZMod M)) := by
      change (List.ofFn (fun b : Fin M => (b,halfBit u (b.val : ZMod M)))).map Prod.snd = _
      rw [List.map_ofFn]
      rfl
    have hlcs := lcs_map_ge Prod.snd (excludedWord h p R M 0 v) (excludedWord h p R M 0 (v+θ))
    rw [hbase, hbase] at hlcs
    have hdef : deficit (List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)))
        (List.ofFn (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))) ≤
        deficit (excludedWord h p R M 0 v) (excludedWord h p R M 0 (v+θ)) := by
      have hlen := length_excludedWord h p R M 0 v
      change (excludedWord h p R M 0 v).length = M at hlen
      rw [deficit, List.length_ofFn, deficit, hlen]
      exact Nat.sub_le_sub_left hlcs M
    calc
      _ = (M:ℝ)*circleCost θ/4 := by norm_num; ring
      _ ≤ _ := (halfCircle_separation he v θ).trans (by exact_mod_cast hdef)
  | succ l ih =>
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let L := excludedLength h p R M l
    let t := (excludedTags h (l+1)).length
    let N := R*period h p (l+1)
    let f := excludedCost h p M hd hn l
    let σ := excludedPhaseHom h p M (l+1) (hd _)
    let ρ := (1/((2:ℝ)^l*4))*excludedCost h p M hd hn (l+1) θ
    have hL : 0 < L := excludedLength_pos hh (NeZero.pos M) hR hn l
    have hp2 : 1 ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
    have hρ : ρ ≤ 1/2 := by
      have hc := excludedCost_le_half hh hd hn (l+1) θ
      have hc0 := (excludedCost h p M hd hn (l+1)).nonneg θ
      dsimp [ρ]
      have hi : 1/((2:ℝ)^l*4) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
      calc
        _ ≤ 1*excludedCost h p M hd hn (l+1) θ := mul_le_mul_of_nonneg_right hi hc0
        _ ≤ _ := by simpa using hc
    have hx : (excludedWord h p R M (l+1) v).length = (t*L)*N := by
      rw [length_excludedWord h p R M (l+1) v]
      change N*(t*L) = (t*L)*N
      exact Nat.mul_comm _ _
    have hy : (excludedWord h p R M (l+1) (shiftExcludedState h M (l+1) v θ)).length = (t*L)*N := by
      rw [length_excludedWord]
      change N*(t*L) = (t*L)*N
      exact Nat.mul_comm _ _
    have hr := row_separation hL (ht (l+1)) hx hy
      (fun x => (excludedTags h (l+1)).idxOf x.1)
      (tag_get_excludedWord h p R M l v hL (by have := ht (l+1); omega))
      (tag_get_excludedWord h p R M l _ hL (by have := ht (l+1); omega)) ρ hρ
    have hrows : ∀ i j : Fin N, ρ*(t*L) ≤
        (deficit (segment (excludedWord h p R M (l+1) v) (i.val*(t*L)) (t*L))
          (segment (excludedWord h p R M (l+1) (shiftExcludedState h M (l+1) v θ))
            (j.val*(t*L)) (t*L)) : ℝ) := by
      intro a b
      rw [segment_excludedWord h p R M l v a, segment_excludedWord h p R M l _ b]
      let z : MaskResidues h p (l+1) := fun k => (b.val : ZMod (p (l+1) k)) - (a.val : ZMod (p (l+1) k))
      have hz (j : Fin h) : σ z j =
          excludedTranslation h p M (l+1) b j - excludedTranslation h p M (l+1) a j := by
        change σ ((fun k : Fin h => (b.val : ZMod (p (l+1) k))) - (fun k : Fin h => (a.val : ZMod (p (l+1) k)))) j = _
        rw [map_sub, Pi.sub_apply]
        exact congrArg₂ (·-·) (congrFun (excludedPhaseHom_natCast h p M (l+1) b (hd _) (hn _)) j)
          (congrFun (excludedPhaseHom_natCast h p M (l+1) a (hd _) (hn _)) j)
      have hind (j : Fin h) := ih
        (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)) (θ+σ z j)
      have hstate (j : Fin h) :
          shiftExcludedState h M l (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)) (θ+σ z j) =
          shiftExcludedState h M l (shiftExcludedState h M l (v j) θ) (excludedTranslation h p M (l+1) b j) := by
        rw [shiftExcludedState_add, shiftExcludedState_add, hz]
        congr 1
        abel
      simp_rw [hstate] at hind
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hind j)
      have hdef := deficit_taggedRow_lower (excludedTags h (l+1)) (nodup_excludedTags ..)
        (mem_excludedTags h (l+1))
        (fun j => excludedWord h p R M l (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)))
        (fun j => excludedWord h p R M l (shiftExcludedState h M l (shiftExcludedState h M l (v j) θ) (excludedTranslation h p M (l+1) b j)))
      apply le_trans _ (hsum.trans hdef)
      rw [← Finset.mul_sum]
      have hcost : excludedCost h p M hd hn (l+1) θ ≤ f.average σ θ z := f.infAverage_le σ θ z
      have htpos : (0:ℝ) < t := by exact_mod_cast (show 0 < t by have := ht (l+1); omega)
      have hcard : (Fintype.card (Fin h) : ℝ) = t := by simp [t]
      rw [PhaseCost.average, hcard, le_div_iff₀ htpos] at hcost
      dsimp only [ρ]
      calc
        _ = ((1/((2:ℝ)^l*4))*(L:ℝ)) * ((excludedCost h p M hd hn (l+1) θ)*t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by positivity)
    have hfinal := hr hrows
    rw [length_excludedWord h p R M (l+1) v] at hfinal
    dsimp only [ρ] at hfinal
    calc
      _ = ((1/((2:ℝ)^l*4))*excludedCost h p M hd hn (l+1) θ)/2 * excludedLength h p R M (l+1) := by rw [pow_succ]; ring
      _ ≤ _ := hfinal

end FiniteCircle

end OAI
