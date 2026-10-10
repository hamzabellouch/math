import OAI.Combinatorics.FiniteCircle.TreeBranching

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem editDistance_append_le {α : Type*} (x y x' y' : List α) :
    editDistance (x++y) (x'++y') ≤ editDistance x x' + editDistance y y' := by
  apply editDistance_le_of_script
  exact ((editDistance_spec x x').append_right y).trans ((editDistance_spec y y').append_left x')

 theorem editDistance_flatMap_le {α β : Type*} (xs : List α) (f g : α → List β) :
    editDistance (xs.flatMap f) (xs.flatMap g) ≤ (xs.map (fun a => editDistance (f a) (g a))).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simpa only [List.flatMap_cons, List.map_cons, List.sum_cons] using
      (editDistance_append_le (f a) (xs.flatMap f) (g a) (xs.flatMap g)).trans (Nat.add_le_add_left ih _)

 theorem editDistance_flatMap_uniform {α β : Type*} (xs : List α) (f g : α → List β)
    (k : ℕ) (hk : ∀ a ∈ xs, editDistance (f a) (g a) ≤ k) :
    editDistance (xs.flatMap f) (xs.flatMap g) ≤ xs.length*k := by
  apply (editDistance_flatMap_le xs f g).trans
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := hk a (by simp)
    have hs := ih (fun a ha => hk a (by simp [ha]))
    nlinarith

 theorem editDistance_ofFn_le_hamming {α : Type*} [DecidableEq α] {N : ℕ} (f g : Fin N → α) :
    editDistance (List.ofFn f) (List.ofFn g) ≤
      (Finset.univ.filter fun i => f i ≠ g i).card := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have he : ∀ a b : α, editDistance [a] [b] ≤ if a=b then 0 else 1 := by
      intro a b
      split_ifs with h
      · subst b
        simp
      · apply editDistance_le_of_script
        exact EditScript.one (.substitute [] [] a b)
    rw [List.ofFn_succ, List.ofFn_succ]
    have ht := editDistance_append_le [f 0] (List.ofFn (fun i => f i.succ))
      [g 0] (List.ofFn (fun i => g i.succ))
    have hi := ih (fun i => f i.succ) (fun i => g i.succ)
    have hcard : (Finset.univ.filter fun i : Fin (N+1) => f i ≠ g i).card =
        (if f 0 = g 0 then 0 else 1) +
        (Finset.univ.filter fun i : Fin N => f i.succ ≠ g i.succ).card := by
      simp only [Finset.card_filter, Fin.sum_univ_succ]
      split_ifs <;> simp_all
    rw [hcard]
    exact ht.trans (Nat.add_le_add (he _ _) hi)

 theorem ed_halfBit_le {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v w : ZMod M) :
    editDistance (List.ofFn (fun b : Fin M => halfBit v b.val))
      (List.ofFn (fun b : Fin M => halfBit w b.val)) ≤ 2*(w-v).valMinAbs.natAbs := by
  exact (editDistance_ofFn_le_hamming _ _).trans_eq ((halfHamming_fin v w).trans (halfHamming_eq he v w))

 theorem ed_tagged_halfBit_le {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v w : ZMod M) :
    editDistance (List.ofFn (fun b : Fin M => (b,halfBit v b.val)))
      (List.ofFn (fun b : Fin M => (b,halfBit w b.val))) ≤ 2*(w-v).valMinAbs.natAbs := by
  apply (editDistance_ofFn_le_hamming _ _).trans
  have heq : (Finset.univ.filter fun i : Fin M => (i,halfBit v i.val) ≠ (i,halfBit w i.val)) =
      (Finset.univ.filter fun i : Fin M => halfBit v i.val ≠ halfBit w i.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply not_congr
    constructor
    · exact congrArg Prod.snd
    · intro hh
      rw [hh]
  rw [heq]
  exact le_of_eq ((halfHamming_fin v w).trans (halfHamming_eq he v w))

theorem editDistance_shifted_rows {α : Type*} (f : ℕ → List α) (N q b : ℕ)
    (hq : q ≤ N) (hf : ∀ a, (f a).length = b) :
    editDistance ((List.range N).flatMap f)
      ((List.range N).flatMap (fun a => f (q+a))) ≤ 2*q*b := by
  let z := (List.range (N-q)).flatMap (fun a => f (q+a))
  have hx : z <+ (List.range N).flatMap f := by
    have he : N = q+(N-q) := by omega
    conv_rhs => rw [he, List.range_add, List.flatMap_append, List.flatMap_map]
    exact List.sublist_append_right _ _
  have hy : z <+ (List.range N).flatMap (fun a => f (q+a)) := by
    have he : N = (N-q)+q := by omega
    conv_rhs => rw [he, List.range_add, List.flatMap_append]
    exact List.sublist_append_left _ _
  have hlen : ∀ a, ((List.range N).flatMap (fun i => f (a+i))).length = N*b := by
    intro a
    simpa only [List.length_range] using length_flatMap_uniform (List.range N) (fun i => f (a+i)) b (fun i _ => hf _)
  have hlx : ((List.range N).flatMap f).length = N*b := by simpa using hlen 0
  have hlz : z.length = (N-q)*b := by
    simpa only [List.length_range] using length_flatMap_uniform (List.range (N-q)) (fun i => f (q+i)) b (fun i _ => hf _)
  have hd := editDistance_le_of_script ((EditScript.of_sublist hx).trans (EditScript.of_sublist hy).symm)
  rw [hlx, hlen, hlz] at hd
  have hab : (N-q)*b+q*b = N*b := by rw [← Nat.add_mul]; congr; omega
  have hh : N*b-(N-q)*b = q*b := by omega
  rw [hh] at hd
  simpa only [two_mul, add_mul] using hd

 theorem editDistance_flatMap_scaled {α β : Type*} (xs : List α) (f g : α → List β)
    (R k : ℕ) (hk : ∀ a ∈ xs, R*editDistance (f a) (g a) ≤ k) :
    R*editDistance (xs.flatMap f) (xs.flatMap g) ≤ xs.length*k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ht := Nat.mul_le_mul_left R (editDistance_append_le (f a) (xs.flatMap f) (g a) (xs.flatMap g))
    have ha := hk a (by simp)
    have hs := ih (fun a ha => hk a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_cons]
    rw [Nat.mul_add] at ht
    nlinarith

theorem tree_cheap_ed (J Z A : ℕ → Type) [∀ l, AddCommGroup (Z l)]
    {M R : ℕ} (hR : 0 < R) (P L : ℕ → ℕ)
    (tags : ∀ l, List (J (l+1)))
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (σ : ∀ l, Z l →+ (J l → ZMod M))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hlen : ∀ l v, (W l v).length = L l)
    (hL : ∀ l, L (l+1) = (R*P (l+1))*((tags l).length*L l))
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (hCRT : ∀ l z, ∃ q : ℕ, q < P (l+1) ∧ ∀ a j, γ l (q+a) j = σ (l+1) z j+γ l a j)
    (l : ℕ) (v c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    R*editDistance (W l v) (W l (v+c)) ≤ 2*l*L l := by
  classical
  induction l with
  | zero =>
    have hz : c=0 := hc
    simp [hz]
  | succ l ih =>
    obtain ⟨cc,hcc,z,hz⟩ := hc
    let u : TreeLeaf J (l+1) → ZMod M := fun i => v i+cc i.1 i.2
    have hu : R*editDistance (W (l+1) v) (W (l+1) u) ≤ 2*l*L (l+1) := by
      rw [hrec, hrec]
      have hh := editDistance_flatMap_scaled (List.range (R*P (l+1)))
        (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j)))
        (fun a => (tags l).flatMap (fun j => (W l (fun i => u (j,i)+γ l a j)).map (tag l j)))
        R ((tags l).length*(2*l*L l)) (by
          intro a _
          apply editDistance_flatMap_scaled
          intro j _
          have he : (fun i => u (j,i)+γ l a j) = (fun i => v (j,i)+γ l a j)+cc j := by
            funext i
            dsimp [u]
            abel
          rw [he]
          exact (Nat.mul_le_mul_left R (editDistance_map_le _ _ _)).trans
            (ih (fun i => v (j,i)+γ l a j) (cc j) (hcc j)))
      simpa only [List.length_range, hL, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
    obtain ⟨q,hq,hqγ⟩ := hCRT l z
    let row (a : ℕ) := (tags l).flatMap (fun j => (W l (fun i => u (j,i)+γ l a j)).map (tag l j))
    have hrow : ∀ a, (row a).length = (tags l).length*L l := by
      intro a
      apply length_flatMap_uniform
      intro j _
      simp only [List.length_map, hlen]
    have hshift : W (l+1) (v+c) = (List.range (R*P (l+1))).flatMap (fun a => row (q+a)) := by
      rw [hrec]
      apply List.flatMap_congr
      intro a _
      apply List.flatMap_congr
      intro j _
      congr 2
      funext i
      change v (j,i)+c (j,i)+γ l a j = u (j,i)+γ l (q+a) j
      rw [hz, hqγ]
      dsimp [u]
      abel
    have hqN : q ≤ R*P (l+1) := by
      exact hq.le.trans (Nat.le_mul_of_pos_left _ hR)
    have hs := editDistance_shifted_rows row (R*P (l+1)) q ((tags l).length*L l) hqN hrow
    change editDistance ((List.range (R*P (l+1))).flatMap row) _ ≤ _ at hs
    have hurow : W (l+1) u = (List.range (R*P (l+1))).flatMap row := hrec l u
    rw [← hurow, ← hshift] at hs
    have hs' : R*editDistance (W (l+1) u) (W (l+1) (v+c)) ≤ 2*L (l+1) := by
      apply (Nat.mul_le_mul_left R hs).trans
      rw [hL]
      have hqp := Nat.mul_le_mul_right (R*((tags l).length*L l)) hq.le
      nlinarith
    have ht := Nat.mul_le_mul_left R (editDistance_triangle (W (l+1) v) (W (l+1) u) (W (l+1) (v+c)))
    rw [Nat.mul_add] at ht
    nlinarith

noncomputable def treeCopies (R : ℕ) (P : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | l+1 => (R*P (l+1))*treeCopies R P l

 theorem tree_coordinate_ed (J A : ℕ → Type) [∀ l, Fintype (J l)]
    {M R : ℕ} (P : ℕ → ℕ) (tags : ∀ l, List (J (l+1)))
    (hsum : ∀ l (f : J (l+1) → ℕ), ((tags l).map f).sum = ∑ j, f j)
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hbase : ∀ v w, editDistance (W 0 v) (W 0 w) ≤ 2*(w PUnit.unit-v PUnit.unit).valMinAbs.natAbs)
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (l : ℕ) (v w : TreeLeaf J l → ZMod M) :
    editDistance (W l v) (W l w) ≤ 2*treeCopies R P l * ∑ i, (w i-v i).valMinAbs.natAbs := by
  classical
  induction l with
  | zero => simpa only [treeCopies, mul_one, Fintype.sum_unique] using hbase v w
  | succ l ih =>
    rw [hrec, hrec]
    have hr : ∀ a, editDistance
        ((tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j)))
        ((tags l).flatMap (fun j => (W l (fun i => w (j,i)+γ l a j)).map (tag l j))) ≤
        2*treeCopies R P l * ∑ i, (w i-v i).valMinAbs.natAbs := by
      intro a
      apply (editDistance_flatMap_le _ _ _).trans
      rw [hsum]
      change (∑ j, editDistance _ _) ≤ 2*treeCopies R P l *
        ∑ i : J (l+1) × TreeLeaf J l, (w i-v i).valMinAbs.natAbs
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply (editDistance_map_le _ _ _).trans
      have hh := ih (fun i => v (j,i)+γ l a j) (fun i => w (j,i)+γ l a j)
      simpa only [add_sub_add_right_eq_sub] using hh
    have hh := editDistance_flatMap_uniform (List.range (R*P (l+1))) _ _
      (2*treeCopies R P l * ∑ i, (w i-v i).valMinAbs.natAbs) (fun a _ => hr a)
    simpa only [List.length_range, treeCopies, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

 theorem tree_single_ed (J A : ℕ → Type) [∀ l, Fintype (J l)]
    {M R : ℕ} [NeZero M] (P : ℕ → ℕ) (tags : ∀ l, List (J (l+1)))
    (hsum : ∀ l (f : J (l+1) → ℕ), ((tags l).map f).sum = ∑ j, f j)
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hbase : ∀ v w, editDistance (W 0 v) (W 0 w) ≤ 2*(w PUnit.unit-v PUnit.unit).valMinAbs.natAbs)
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (l : ℕ) (v : TreeLeaf J l → ZMod M) (i : TreeLeaf J l) (q : ℕ) :
    editDistance (W l v) (W l (v+Pi.single i (q : ZMod M))) ≤ 2*treeCopies R P l*q := by
  classical
  have hh := tree_coordinate_ed J A P tags hsum tag γ W hbase hrec l v (v+Pi.single i (q : ZMod M))
  have hs : (∑ k, ((v+Pi.single i (q : ZMod M) : TreeLeaf J l → ZMod M) k-v k).valMinAbs.natAbs) = (q : ZMod M).valMinAbs.natAbs := by
    simp only [Pi.add_apply, add_sub_cancel_left, Pi.single_apply]
    simp only [apply_ite, ZMod.valMinAbs_zero, Int.natAbs_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hs] at hh
  apply hh.trans
  apply Nat.mul_le_mul_left
  rw [ZMod.valMinAbs_natAbs_eq_min]
  exact (min_le_left _ _).trans ((ZMod.val_natCast M q).trans_le (Nat.mod_le _ _))

 theorem tree_length_eq (J : ℕ → Type) [∀ l, Fintype (J l)] (M R : ℕ) (P L : ℕ → ℕ)
    (h0 : L 0=M) (hL : ∀ l, L (l+1)=(R*P (l+1))*(Fintype.card (J (l+1))*L l)) (l : ℕ) :
    L l = M*Fintype.card (TreeLeaf J l)*treeCopies R P l := by
  induction l with
  | zero => simp only [TreeLeaf, Fintype.card_punit, treeCopies, mul_one, h0]
  | succ l ih =>
    change L (l+1) = M*Fintype.card (J (l+1) × TreeLeaf J l)*treeCopies R P (l+1)
    rw [hL, ih, Fintype.card_prod, treeCopies]
    ring

 theorem residue_representative {h : ℕ} (p : Fin h → ℕ)
    (hn : ∀ k, 0 < p k) (hp : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (z : ∀ k, ZMod (p k)) : ∃ q : ℕ, q < ∏ k, p k ∧ ∀ k, (q : ZMod (p k)) = z k := by
  classical
  let a := fun k => (z k).val
  have hs : ∀ k ∈ (Finset.univ : Finset (Fin h)), p k ≠ 0 := fun k _ => (hn k).ne'
  have hpp : Set.Pairwise (Finset.univ : Finset (Fin h)) (fun i j => Nat.Coprime (p i) (p j)) :=
    fun i _ j _ hij => hp hij
  let q := Nat.chineseRemainderOfFinset a p Finset.univ hs hpp
  refine ⟨q.val, Nat.chineseRemainderOfFinset_lt_prod a p hs hpp, ?_⟩
  intro k
  let : NeZero (p k) := ⟨(hn k).ne'⟩
  have ht := q.property k (Finset.mem_univ k)
  have he := (ZMod.natCast_eq_natCast_iff q.val (a k) (p k)).mpr ht
  exact he.trans (ZMod.natCast_zmod_val (z k))

 theorem mask_CRT_shift {h M : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l, Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)))
    (l : ℕ) (z : MaskResidues h p (l+1)) :
    ∃ q, q < period h p (l+1) ∧ ∀ a j,
      maskGamma h p M (l+1) (q+a) j =
        maskPhaseHom h p M (l+1) (hd (l+1)) z j + maskGamma h p M (l+1) a j := by
  obtain ⟨q,hq,hz⟩ := residue_representative (fun k : Fin h => p (l+1) k) (hn _) (hp _) z
  refine ⟨q,hq,?_⟩
  intro a j
  rw [← maskPhaseHom_natCast h p M (l+1) (q+a) (hd _) (hn _),
    ← maskPhaseHom_natCast h p M (l+1) a (hd _) (hn _)]
  have he : (fun k : Fin h => ((q+a : ℕ) : ZMod (p (l+1) k))) = z+(fun k : Fin h => (a : ZMod (p (l+1) k))) := by
    funext k
    simp only [Nat.cast_add, hz, Pi.add_apply]
  rw [he, map_add, Pi.add_apply]

 theorem excluded_CRT_shift {h M : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l, Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)))
    (l : ℕ) (z : MaskResidues h p (l+1)) :
    ∃ q, q < period h p (l+1) ∧ ∀ a j,
      excludedTranslation h p M (l+1) (q+a) j =
        excludedPhaseHom h p M (l+1) (hd (l+1)) z j + excludedTranslation h p M (l+1) a j := by
  obtain ⟨q,hq,hz⟩ := residue_representative (fun k : Fin h => p (l+1) k) (hn _) (hp _) z
  refine ⟨q,hq,?_⟩
  intro a j
  rw [← excludedPhaseHom_natCast h p M (l+1) (q+a) (hd _) (hn _),
    ← excludedPhaseHom_natCast h p M (l+1) a (hd _) (hn _)]
  have he : (fun k : Fin h => ((q+a : ℕ) : ZMod (p (l+1) k))) = z+(fun k : Fin h => (a : ZMod (p (l+1) k))) := by
    funext k
    simp only [Nat.cast_add, hz, Pi.add_apply]
  rw [he, map_add, Pi.add_apply]

noncomputable def flatMaskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (MaskChildren h p) l → ZMod M) : List (MaskAlphabet h p l) :=
  maskWord h p R M l (flatMaskState h p M l v)

noncomputable def flatExcludedWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (fun _ => Fin h) l → ZMod M) : List (ExcludedAlphabet h M l) :=
  excludedWord h p R M l (flatExcludedState h M l v)

 theorem flatMaskWord_succ (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (MaskChildren h p) (l+1) → ZMod M) :
    flatMaskWord h p R M (l+1) v = (List.range (R*period h p (l+1))).flatMap
      (fun a => (maskTags h p (l+1)).flatMap (fun j =>
        (flatMaskWord h p R M l (fun i => v (j,i)+maskGamma h p M (l+1) a j)).map (Prod.mk j))) := by
  change (List.range _).flatMap _ = _
  apply List.flatMap_congr
  intro a _
  apply List.flatMap_congr
  intro j _
  congr 2
  exact (flatMaskState_shift h p M l (fun i => v (j,i)) _).symm

 theorem flatExcludedWord_succ (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (fun _ => Fin h) (l+1) → ZMod M) :
    flatExcludedWord h p R M (l+1) v = (List.range (R*period h p (l+1))).flatMap
      (fun a => (excludedTags h (l+1)).flatMap (fun j =>
        (flatExcludedWord h p R M l (fun i => v (j,i)+excludedTranslation h p M (l+1) a j)).map (Prod.mk j))) := by
  unfold flatExcludedWord
  rw [excludedWord_succ]
  apply List.flatMap_congr
  intro a _
  unfold taggedRow
  apply List.flatMap_congr
  intro j _
  congr 2
  change excludedWord h p R M l (shiftExcludedState h M l (flatExcludedState h M l (fun i => v (j,i))) _) = _
  rw [flatExcludedState_shift]

 theorem mask_cheap_ed {h M R : ℕ} {p : ℕ → ℕ → ℕ} (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l, Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)))
    (l : ℕ) (v c : TreeLeaf (MaskChildren h p) l → ZMod M)
    (hc : c ∈ treeCheap (MaskChildren h p) (MaskResidues h p) (fun l => maskPhaseHom h p M l (hd l)) l) :
    R*editDistance (flatMaskWord h p R M l v) (flatMaskWord h p R M l (v+c)) ≤ 2*l*maskLength h p R M l := by
  apply tree_cheap_ed (MaskChildren h p) (MaskResidues h p) (MaskAlphabet h p) hR
    (period h p) (maskLength h p R M) (fun l => maskTags h p (l+1)) (fun _ => Prod.mk)
    (fun l => maskPhaseHom h p M l (hd l)) (fun l => maskGamma h p M (l+1))
    (flatMaskWord h p R M) (fun l v => length_maskWord h p R M l (flatMaskState h p M l v))
    (fun _ => rfl) (flatMaskWord_succ h p R M) (mask_CRT_shift hd hn hp) l v c hc

 theorem excluded_cheap_ed {h M R : ℕ} {p : ℕ → ℕ → ℕ} (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l, Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)))
    (l : ℕ) (v c : TreeLeaf (fun _ => Fin h) l → ZMod M)
    (hc : c ∈ treeCheap (fun _ => Fin h) (MaskResidues h p) (fun l => excludedPhaseHom h p M l (hd l)) l) :
    R*editDistance (flatExcludedWord h p R M l v) (flatExcludedWord h p R M l (v+c)) ≤ 2*l*excludedLength h p R M l := by
  apply tree_cheap_ed (fun _ => Fin h) (MaskResidues h p) (ExcludedAlphabet h M) hR
    (period h p) (excludedLength h p R M) (fun l => excludedTags h (l+1)) (fun _ => Prod.mk)
    (fun l => excludedPhaseHom h p M l (hd l)) (fun l => excludedTranslation h p M (l+1))
    (flatExcludedWord h p R M) (fun l v => length_excludedWord h p R M l (flatExcludedState h M l v))
    (fun _ => rfl) (flatExcludedWord_succ h p R M) (excluded_CRT_shift hd hn hp) l v c hc

 theorem sum_map_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) (f : MaskTag h p l → ℕ) :
    ((maskTags h p l).map f).sum = ∑ j, f j := by
  simp only [maskTags, List.map_flatten, List.map_ofFn, List.sum_flatten, List.sum_ofFn,
    Fintype.sum_sigma]
  simp only [Function.comp_def, List.map_ofFn, List.sum_ofFn]

 theorem sum_map_excludedTags (h l : ℕ) (f : Fin h → ℕ) :
    ((excludedTags h l).map f).sum = ∑ j, f j := by
  simp only [excludedTags, List.map_ofFn, Function.comp_id, List.sum_ofFn]

 theorem flatMaskWord_base (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ)
    (v : TreeLeaf (MaskChildren h p) 0 → ZMod M) :
    flatMaskWord h p R M 0 v = List.ofFn (fun b : Fin M => halfBit (v PUnit.unit) b.val) := by
  exact maskWord_zero_eq _

 theorem flatExcludedWord_base (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ)
    (v : TreeLeaf (fun _ => Fin h) 0 → ZMod M) :
    flatExcludedWord h p R M 0 v = List.ofFn (fun b : Fin M => (b,halfBit (v PUnit.unit) b.val)) := by
  rfl

 theorem mask_single_ed {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M] (he : M=2*(M/2))
    (l : ℕ) (v : TreeLeaf (MaskChildren h p) l → ZMod M) (i : TreeLeaf (MaskChildren h p) l) (q : ℕ) :
    editDistance (flatMaskWord h p R M l v) (flatMaskWord h p R M l (v+Pi.single i (q : ZMod M))) ≤
      2*treeCopies R (period h p) l*q := by
  apply tree_single_ed (MaskChildren h p) (MaskAlphabet h p) (period h p) (fun l => maskTags h p (l+1))
    (fun l => sum_map_maskTags h p (l+1)) (fun _ => Prod.mk) (fun l => maskGamma h p M (l+1))
    (flatMaskWord h p R M) _ (flatMaskWord_succ h p R M) l v i q
  intro v w
  rw [flatMaskWord_base, flatMaskWord_base]
  exact ed_halfBit_le he _ _

 theorem excluded_single_ed {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M] (he : M=2*(M/2))
    (l : ℕ) (v : TreeLeaf (fun _ => Fin h) l → ZMod M) (i : TreeLeaf (fun _ => Fin h) l) (q : ℕ) :
    editDistance (flatExcludedWord h p R M l v) (flatExcludedWord h p R M l (v+Pi.single i (q : ZMod M))) ≤
      2*treeCopies R (period h p) l*q := by
  apply tree_single_ed (fun _ => Fin h) (ExcludedAlphabet h M) (period h p) (fun l => excludedTags h (l+1))
    (fun l => sum_map_excludedTags h (l+1)) (fun _ => Prod.mk) (fun l => excludedTranslation h p M (l+1))
    (flatExcludedWord h p R M) _ (flatExcludedWord_succ h p R M) l v i q
  intro v w
  rw [flatExcludedWord_base, flatExcludedWord_base]
  exact ed_tagged_halfBit_le he _ _

end FiniteCircle

end OAI
