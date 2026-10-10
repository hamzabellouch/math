import OAI.Dynamics.SmoothObstruction.WordEntropy

namespace OAI

section

namespace SmoothObstruction.WordConcatenation
open Finset
variable {A B : Type*} {m N : ℕ}

noncomputable def mismatches {ι : Type*} [Fintype ι] (u v : ι → A) : ℕ := by
  classical
  exact (univ.filter (fun r => u r ≠ v r)).card

lemma mismatches_nonneg {ι : Type*} [Fintype ι] (u v : ι → A) : 0 ≤ (mismatches u v : ℝ) :=
  Nat.cast_nonneg _

lemma mismatches_sum [DecidableEq A] {ι : Type*} [Fintype ι] (u v : ι → A) :
    mismatches u v = ∑ r, if u r=v r then (0 : ℕ) else 1 := by
  classical
  simp only [mismatches,card_eq_sum_ones,sum_filter,ne_eq,ite_not]

lemma mismatches_comp {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (u v : κ → A) :
    mismatches (u ∘ e) (v ∘ e) = mismatches u v := by
  classical
  simp only [mismatches_sum,Function.comp_apply]
  exact e.sum_comp (fun r => if u r=v r then (0 : ℕ) else 1)

lemma mismatches_concat (u : B → Fin m → A) (w v : Fin N → B) :
    mismatches (concat u w) (concat u v) = ∑ b, mismatches (u (w b)) (u (v b)) := by
  classical
  rw [←mismatches_comp pack]
  simp only [mismatches_sum,Function.comp_apply,concat_pack,Fintype.sum_prod_type]

lemma concat_distance {δ : ℝ} (u : B → Fin m → A)
    (hu : ∀ a b, a≠b → δ*m ≤ (mismatches (u a) (u b) : ℝ)) (w v : Fin N → B) :
    δ*m*mismatches w v ≤ (mismatches (concat u w) (concat u v) : ℝ) := by
  classical
  rw [mismatches_concat,Nat.cast_sum,mismatches_sum,Nat.cast_sum,mul_sum]
  apply sum_le_sum
  intro b _
  by_cases he : w b=v b
  · simp only [he,↓reduceIte,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _
  · simpa only [he,↓reduceIte,Nat.cast_one,mul_one] using hu (w b) (v b) he

/-- Arbitrarily addressed letters of a two-word splice. Only addresses less
than twice the word length are used by recognition. -/
def joined [NeZero m] (u v : Fin m → A) (k : ℕ) : A :=
  if k < m then u ⟨k%m,Nat.mod_lt _ (NeZero.pos m)⟩
  else v ⟨k%m,Nat.mod_lt _ (NeZero.pos m)⟩

def splice [NeZero m] (u v : Fin m → A) (t : Fin m) : Fin m → A :=
  fun r => joined u v (t.val+r.val)

@[simp] lemma splice_zero [NeZero m] (u v : Fin m → A) : splice u v 0=u := by
  funext r
  simp [splice,joined,Nat.mod_eq_of_lt r.isLt,r.isLt]

lemma joined_low [NeZero m] (u v : Fin m → A) (k : Fin m) : joined u v k.val=u k := by
  simp [joined,k.isLt,Nat.mod_eq_of_lt k.isLt]

lemma joined_high [NeZero m] (u v : Fin m → A) (k : Fin m) : joined u v (m+k.val)=v k := by
  simp [joined,Nat.not_lt.mpr (Nat.le_add_right _ _),Nat.mod_eq_of_lt k.isLt]

lemma concat_at [NeZero m] [NeZero N] (u : B → Fin m → A) (w : Fin N → B)
    (k : Fin (m*N)) :
    concat u w k = u (w ⟨k.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
      (by simpa only [Nat.mul_comm N m] using k.isLt)⟩)
      ⟨k.val%m,Nat.mod_lt _ (NeZero.pos m)⟩ := by
  have he : k=pack (⟨k.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
      (by simpa only [Nat.mul_comm N m] using k.isLt)⟩,
      ⟨k.val%m,Nat.mod_lt _ (NeZero.pos m)⟩) := by
    apply Fin.ext
    simp only [pack_val]
    exact (Nat.div_add_mod' k.val m).symm
  calc
    _ = concat u w (pack (⟨k.val/m,_⟩,⟨k.val%m,_⟩)) := congrArg (concat u w) he
    _ = _ := concat_pack u w _ _

lemma joined_concat [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w v : Fin N → B) (k : ℕ) :
    joined (concat u w) (concat u v) k =
      u (joined w v (k/m)) ⟨k%m,Nat.mod_lt _ (NeZero.pos m)⟩ := by
  have hiff : k/m < N ↔ k < m*N := by
    rw [Nat.div_lt_iff_lt_mul (NeZero.pos m),Nat.mul_comm N m]
  simp only [joined,hiff]
  split_ifs <;> rw [concat_at] <;> congr 2
  · exact Fin.ext (Nat.mod_mul_right_div_self k m N)
  · exact Nat.mod_mod_of_dvd k (dvd_mul_right m N)
  · exact Fin.ext (Nat.mod_mul_right_div_self k m N)
  · exact Nat.mod_mod_of_dvd k (dvd_mul_right m N)

/-- Every lower-length portion of a shifted concatenation is precisely a
splice of two successive lower words. This identity includes the join of
the two larger words and repeated constituents. -/
lemma splice_chunk [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w v : Fin N → B) (t : Fin (m*N)) (b : Fin N) :
    (fun r => splice (concat u w) (concat u v) t (pack (b,r))) =
      splice (u (joined w v (t.val/m+b.val)))
        (u (joined w v (t.val/m+b.val+1)))
        ⟨t.val%m,Nat.mod_lt _ (NeZero.pos m)⟩ := by
  funext r
  simp only [splice,pack_val,joined_concat]
  have he : t.val+(b.val*m+r.val)=t.val%m+r.val+(t.val/m+b.val)*m := by
    have hh := Nat.div_add_mod' t.val m
    nlinarith
  simp only [he,Nat.add_mul_div_right _ _ (NeZero.pos m),Nat.add_mul_mod_self_right]
  conv_rhs => rw [joined]
  have hs := Nat.mod_lt t.val (NeZero.pos m)
  by_cases hh : t.val%m+r.val < m
  · rw [ite_eq_left hh,Nat.div_eq_of_lt hh]
    simp only [zero_add,Nat.mod_eq_of_lt hh]
  · have hd : (t.val%m+r.val)/m=1 := Nat.div_eq_of_lt_le (by omega)
        (by have := r.isLt; omega)
    rw [ite_eq_right hh,hd]
    congr 2
    omega

lemma mismatches_blocks (w v : Fin (m*N) → A) :
    mismatches w v = ∑ b, mismatches (fun r => w (pack (b,r))) (fun r => v (pack (b,r))) := by
  classical
  rw [←mismatches_comp pack]
  simp only [mismatches_sum,Function.comp_apply,Fintype.sum_prod_type]

lemma splice_aligned [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w v : Fin N → B) (t : Fin (m*N)) (ht : t.val%m=0) :
    splice (concat u w) (concat u v) t =
      concat u (splice w v ⟨t.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
        (by simpa only [Nat.mul_comm N m] using t.isLt)⟩) := by
  funext j
  obtain ⟨⟨b,r⟩,rfl⟩ := pack.surjective j
  have hh := congrFun (splice_chunk u w v t b) r
  have hz : (⟨t.val%m,Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m)=0 := Fin.ext ht
  rw [hz,splice_zero] at hh
  simpa only [concat_pack,splice] using hh

/-- A single recognition predicate handles both distinct words and every
nontrivial splice, so the symbol-scale induction cannot drop an offset. -/
def Recognizes [NeZero m] (u : B → Fin m → A) (δ : ℝ) : Prop :=
  ∀ a b c (t : Fin m), t≠0 ∨ a≠c →
    δ*m ≤ (mismatches (splice (u a) (u b) t) (u c) : ℝ)

variable {C : Type*}

theorem recognition_step [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w : C → Fin N → B) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hu : Recognizes u δ) (hw : Recognizes w (1-ε)) :
    Recognizes (fun a => concat u (w a)) (δ*(1-ε)) := by
  intro a b c t ht
  by_cases hmod : t.val%m=0
  · rw [splice_aligned u (w a) (w b) t hmod]
    let t' : Fin N := ⟨t.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
        (by simpa only [Nat.mul_comm N m] using t.isLt)⟩
    have ht' : t'≠0 ∨ a≠c := by
      rcases ht with ht|ht
      · left
        intro hz
        have hv := congrArg Fin.val hz
        dsimp [t'] at hv
        have hd := Nat.div_add_mod' t.val m
        rw [hv,hmod,zero_mul,zero_add] at hd
        exact ht (Fin.ext hd.symm)
      · exact Or.inr ht
    have hh := hw a b c t' ht'
    have hb := concat_distance (δ:=δ) u
      (fun x y hxy => by simpa only [splice_zero] using hu x x y 0 (Or.inr hxy))
      (splice (w a) (w b) t') (w c)
    have he := mul_le_mul_of_nonneg_left hh (mul_nonneg hδ (Nat.cast_nonneg m))
    push_cast
    dsimp [t'] at hb
    nlinarith
  · rw [mismatches_blocks,Nat.cast_sum]
    have hb (j : Fin N) : δ*m ≤
        (mismatches (fun r => splice (concat u (w a)) (concat u (w b)) t (pack (j,r)))
          (fun r => concat u (w c) (pack (j,r))) : ℝ) := by
      rw [splice_chunk]
      simp only [concat_pack]
      apply hu
      left
      intro hh
      exact hmod (congrArg Fin.val hh)
    have hs := sum_le_sum (fun j (_hj : j ∈ (univ : Finset (Fin N))) => hb j)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    push_cast
    have hn : 0 ≤ δ*(m:ℝ)*N := by positivity
    nlinarith

end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.WordHierarchy
open WordConcatenation WordParameters WordStep Finset

lemma splice_first {α : Type*} {M n : ℕ} [NeZero n] (w : Fin M → Fin n → α)
    (a b : Fin M) (t r : Fin n) :
    splice (w a) (w b) t r =
      w (ShiftComparisons.first a b t r).1 (ShiftComparisons.first a b t r).2 := by
  simp only [splice,joined,ShiftComparisons.first,Nat.add_comm t.val r.val]
  split_ifs <;> rfl

lemma count_complement {α : Type*} [Fintype α] [DecidableEq α]
    {M n : ℕ} [NeZero n] (w : Fin M → Fin n → α) (a b c : Fin M) (t : Fin n) :
    mismatches (splice (w a) (w b) t) (w c)+ShiftComparisons.matchCount w a b c t=n := by
  simp only [mismatches_sum,ShiftComparisons.matchCount,card_eq_sum_ones,sum_filter,
    ←sum_add_distrib]
  calc
    _ = ∑ _r : Fin n, 1 := by
      apply sum_congr rfl
      intro r _
      rw [splice_first]
      split_ifs <;> rfl
    _ = n := by simp

lemma stage_recognizes (i : ℕ) : Recognizes (stage i).word (1-epsilon i) := by
  intro a b c t ht
  let a' := (Fintype.equivFin (A (i+1))) a
  let b' := (Fintype.equivFin (A (i+1))) b
  let c' := (Fintype.equivFin (A (i+1))) c
  have hsep := (stage i).separated a' b' c' t (ht.imp id (fun h h' => h
    ((Fintype.equivFin (A (i+1))).injective h')))
  have hlt : (ShiftComparisons.matchCount (stage i).w a' b' c' t : ℝ) <
      epsilon i*N (S i) := (Nat.lt_ceil.mp hsep)
  have hc := count_complement (stage i).w a' b' c' t
  have hcr : (mismatches (splice ((stage i).word a) ((stage i).word b) t)
      ((stage i).word c) : ℝ)+ShiftComparisons.matchCount (stage i).w a' b' c' t = N (S i) := by
    exact_mod_cast (hc.trans (q_mul_H (S i)))
  have hg : (groupLength i : ℝ) = N (S i) := congrArg Nat.cast (q_mul_H (S i))
  calc
    (1-epsilon i)*(groupLength i : ℝ)=(1-epsilon i)*(N (S i) : ℝ) := by rw [hg]
    _ ≤ _ := by nlinarith only [hcr,hlt]

lemma recognizes_reindex_length {α β : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    (h : m=n) (w : β → Fin m → α) {δ : ℝ} (hw : Recognizes w δ) :
    Recognizes (fun a j => w a ((finCongr h).symm j)) δ := by
  subst n
  simpa only [finCongr_refl,Equiv.refl_symm,Equiv.refl_apply] using hw

instance recognitionNNeZero (i : ℕ) : NeZero (N (S i)) :=
  ⟨by rw [←q_mul_H]; exact NeZero.ne (q (S i)*H (S i))⟩

lemma children_recognizes (i : ℕ) : Recognizes (children i) (1-epsilon i) :=
  recognizes_reindex_length (q_mul_H (S i)) (stage i).word (stage_recognizes i)

noncomputable def delta (i : ℕ) : ℝ := ∏ j ∈ range i, (1-epsilon j)

@[simp] lemma delta_zero : delta 0=1 := by simp [delta]
lemma delta_succ (i : ℕ) : delta (i+1)=delta i*(1-epsilon i) := by
  simp [delta,prod_range_succ]
lemma delta_nonneg (i : ℕ) : 0 ≤ delta i := prod_nonneg (fun j _ =>
  sub_nonneg.mpr (epsilon_le_one j))

lemma epsilon_sum (i : ℕ) : (∑ j ∈ range i,epsilon j)=1/4-2*epsilon i := by
  induction i with
  | zero => norm_num [epsilon]
  | succ i ih => rw [sum_range_succ,ih,epsilon_succ]; ring

lemma delta_lower (i : ℕ) : 3/4 ≤ delta i := by
  have hlo : 1-(∑ j ∈ range i,epsilon j) ≤ delta i := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [sum_range_succ,delta_succ]
      have hsum : 0 ≤ ∑ j ∈ range i,epsilon j := sum_nonneg (fun j _ => (epsilon_pos j).le)
      have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (epsilon_le_one i))
      nlinarith [mul_nonneg hsum (epsilon_pos i).le]
  rw [epsilon_sum] at hlo
  have hh := epsilon_pos i
  linarith

noncomputable instance recognitionLengthNeZero (i : ℕ) : NeZero (length 40000 i) :=
  ⟨(length_pos 40000 i).ne'⟩

/-- Source recognition at every symbol offset for the actual chosen words,
not only for the constituent-label lists. -/
theorem word_recognizes (i : ℕ) : Recognizes (word i) (delta i) := by
  induction i with
  | zero =>
    intro a b c t ht
    have hz : t=0 := by
      apply Fin.ext
      have hh := t.isLt
      change t.val < 1 at hh
      simp only [Fin.val_zero]
      omega
    subst t
    have hne : a≠c := ht.resolve_left (not_not.mpr rfl)
    rw [splice_zero]
    classical
    have hc : mismatches (word 0 a) (word 0 c)=1 := by
      rw [mismatches_sum]
      simp only [word,hne,ite_false]
      change (∑ _r : Fin 1,(1:ℕ))=1
      decide
    rw [hc]
    norm_num only [delta_zero,length,Nat.cast_one,mul_one]
  | succ i ih =>
    rw [delta_succ]
    exact recognition_step (word i) (children i) (delta_nonneg i) (epsilon_pos i).le ih
      (children_recognizes i)

/-- The uniform fixed-alphabet constant is at least 3/4, hence strictly
positive independently of the level and the three source labels. -/
theorem uniform_recognition (i : ℕ) : Recognizes (word i) (3/4) := by
  intro a b c t ht
  exact (mul_le_mul_of_nonneg_right (delta_lower i) (Nat.cast_nonneg _)).trans
    (word_recognizes i a b c t ht)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.RecognitionWindow
open Finset WordConcatenation
variable {A B : Type*} {m : ℕ} [NeZero m]

/-- A legal phase-marked bilateral sequence, with no restriction at window
endpoints; adjacent words are allowed to be identical. -/
def LegalAt (w : B → Fin m → A) (u : ℤ → A) (p : ZMod m) : Prop :=
  ∀ t : ℤ,(t : ZMod m)=-p → ∃ a,∀ r : Fin m,u (t+r.val)=w a r

/-- Every arbitrary length-m window is a splice of the two actual adjacent
legal words. This includes negative starts and windows beyond the observed
half-name. -/
theorem window_splice (w : B → Fin m → A) (u : ℤ → A)
    (p : ZMod m) (hu : LegalAt w u p) (t : ℤ) :
    ∃ a b, ∃ o : Fin m, (o.val : ZMod m)=p+(t : ZMod m) ∧
      (fun r : Fin m => u (t+r.val))=splice (w a) (w b) o := by
  let q : ZMod m := p+(t : ZMod m)
  let o : Fin m := ⟨q.val,q.val_lt⟩
  let s : ℤ := t-o.val
  have ho : (o.val : ZMod m)=q := ZMod.natCast_zmod_val q
  have hs : (s : ZMod m)=-p := by
    change ((t-(o.val:ℤ) : ℤ) : ZMod m)=-p
    rw [Int.cast_sub,Int.cast_natCast,ho]
    dsimp only [q]
    ring
  obtain ⟨a,ha⟩ := hu s hs
  obtain ⟨b,hb⟩ := hu (s+m) (by
    rw [Int.cast_add,Int.cast_natCast,ZMod.natCast_self,add_zero,hs])
  refine ⟨a,b,o,ho,?_⟩
  funext r
  simp only [splice,joined]
  by_cases hr : o.val+r.val < m
  · rw [ite_eq_left hr,←ha]
    congr 1
    change t+(r.val:ℤ)=s+(((o.val+r.val)%m:ℕ):ℤ)
    rw [Nat.mod_eq_of_lt hr]
    dsimp only [s]
    push_cast
    ring
  · rw [ite_eq_right hr,←hb]
    have hmod : (o.val+r.val)%m=o.val+r.val-m := by
      have ho' := o.isLt
      have hr' := r.isLt
      rw [Nat.mod_eq_sub_mod (by omega : m≤o.val+r.val),Nat.mod_eq_of_lt (by omega)]
    change u (t+(r.val:ℤ))=u (s+(m:ℤ)+(((o.val+r.val)%m:ℕ):ℤ))
    rw [hmod,Nat.cast_sub (by omega : m≤o.val+r.val)]
    dsimp only [s]
    congr 1
    push_cast
    ring

lemma mismatches_symm {ι : Type*} [Fintype ι] (u v : ι → A) :
    mismatches u v=mismatches v u := by
  classical
  simp only [mismatches,ne_comm]

/-- Recognition forces a fixed cost on every aligned block whenever the
other sequence has a different phase. -/
lemma phase_block_cost (w : B → Fin m → A) {δ : ℝ} (hw : Recognizes w δ)
    (u v : ℤ → A) (p q : ZMod m) (hu : LegalAt w u p) (hv : LegalAt w v q)
    (hpq : p≠q) (t : ℤ) (ht : (t : ZMod m)=-p) :
    δ*m≤(mismatches (fun r : Fin m => u (t+r.val))
      (fun r : Fin m => v (t+r.val)) : ℝ) := by
  obtain ⟨c,hc⟩ := hu t ht
  obtain ⟨a,b,o,ho,hv'⟩ := window_splice w v q hv t
  have ho0 : o≠0 := by
    intro hz
    have hq : q-p=0 := by
      simpa only [hz,Fin.val_zero,Nat.cast_zero,ht,←sub_eq_add_neg] using ho.symm
    exact hpq (sub_eq_zero.mp hq).symm
  have hu' : (fun r : Fin m => u (t+r.val))=w c := funext hc
  rw [hu',hv',mismatches_symm]
  exact hw a b c o (Or.inl ho0)

lemma mismatches_injection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (u v : κ → A) :
    mismatches (u ∘ e) (v ∘ e)≤ mismatches u v := by
  classical
  simp only [mismatches_sum,Function.comp_apply]
  calc
    _ = ∑ k∈univ.map e,if u k=v k then (0:ℕ) else 1 := (sum_map _ _ _).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

/-- The D-1 full blocks after first alignment are disjoint and remain in
[0,D*m), including the case of a nonzero advance. -/
def blocksEmbedding (D a : ℕ) (ha : a < m) : Fin (D-1) × Fin m ↪ Fin (D*m) where
  toFun jr := ⟨a+jr.1.val*m+jr.2.val,by
    have hj := jr.1.isLt
    have hr := jr.2.isLt
    have hm := NeZero.pos m
    have hjD : jr.1.val+2≤D := by omega
    have hb := Nat.mul_le_mul_right m hjD
    nlinarith⟩
  inj' := by
    intro p q he
    have hv := congrArg Fin.val he
    change a+p.1.val*m+p.2.val=a+q.1.val*m+q.2.val at hv
    have hp := p.2.isLt
    have hq := q.2.isLt
    have hm := NeZero.pos m
    have hj : p.1.val=q.1.val := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with h|h
      · have hh := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
        nlinarith
      · have hh := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
        nlinarith
    have hk : p.2.val=q.2.val := by nlinarith
    exact Prod.ext (Fin.ext hj) (Fin.ext hk)

/-- The whole-window mismatch count dominates the sum of all complete
aligned block counts. No stochastic independence is involved. -/
lemma complete_blocks_le (D a : ℕ) (ha : a < m) (u v : ℤ → A) (t : ℤ) :
    (∑ j : Fin (D-1),mismatches
      (fun r : Fin m => u (t+(a+j.val*m+r.val : ℕ)))
      (fun r : Fin m => v (t+(a+j.val*m+r.val : ℕ))))≤
    mismatches (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val)) := by
  have hh := mismatches_injection (blocksEmbedding D a ha)
    (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val))
  change mismatches
    (fun jr : Fin (D-1) × Fin m => u (t+(a+jr.1.val*m+jr.2.val : ℕ)))
    (fun jr : Fin (D-1) × Fin m => v (t+(a+jr.1.val*m+jr.2.val : ℕ)))≤
      mismatches (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val)) at hh
  classical
  simpa only [mismatches_sum,Fintype.sum_prod_type] using hh

/-- Small mismatch on one half-name recovers the ORIGINAL phase. It does
not choose or shift entry indices after the geometric switch. -/
theorem phase_recovery (w : B → Fin m → A) {δ : ℝ} (_hδ : 0<δ)
    (hw : Recognizes w δ) (u v : ℤ → A) (p q : ZMod m)
    (hu : LegalAt w u p) (hv : LegalAt w v q)
    (D : ℕ) (hD : 2≤D) (a : ℕ) (ha : a < m) (haP : (a : ZMod m)=-p)
    (hclose : (mismatches (fun r : Fin (D*m) => u r.val)
      (fun r : Fin (D*m) => v r.val) : ℝ)<δ*(D*m)/100) : p=q := by
  by_contra hpq
  have hc (j : Fin (D-1)) : δ*m≤(mismatches
      (fun r : Fin m => u ((a+j.val*m+r.val : ℕ):ℤ))
      (fun r : Fin m => v ((a+j.val*m+r.val : ℕ):ℤ)) : ℝ) := by
    have ht : (((a+j.val*m : ℕ):ℤ):ZMod m)=-p := by
      simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,
        mul_zero,add_zero,haP]
    have hh := phase_block_cost w hw u v p q hu hv hpq ((a+j.val*m : ℕ):ℤ) ht
    simpa only [Nat.cast_add,Nat.cast_mul] using hh
  have hb := complete_blocks_le D a ha u v 0
  have hbr : (∑ j : Fin (D-1),(mismatches
      (fun r : Fin m => u ((a+j.val*m+r.val : ℕ):ℤ))
      (fun r : Fin m => v ((a+j.val*m+r.val : ℕ):ℤ)) : ℝ))≤
      (mismatches (fun r : Fin (D*m) => u r.val) (fun r : Fin (D*m) => v r.val) : ℝ) := by
    exact_mod_cast (by simpa only [zero_add] using hb)
  have hsum := (sum_le_sum (fun j (_ : j∈univ) => hc j)).trans hbr
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub (by omega : 1≤D),
    Nat.cast_one] at hsum
  have hm : (0:ℝ) < m := by exact_mod_cast NeZero.pos m
  have hDr : (2:ℝ)≤D := by exact_mod_cast hD
  have hh : δ*(D*m)/2≤(D-1)*(δ*m) := by nlinarith
  nlinarith
end SmoothObstruction.RecognitionWindow

namespace SmoothObstruction.RecognitionWindow
open Finset WordConcatenation
variable {A B : Type*} {m : ℕ} [NeZero m]

lemma distinct_word_cost (w : B → Fin m → A) {δ : ℝ} (hw : Recognizes w δ)
    {a b : B} (hab : a≠b) : δ*m≤(mismatches (w a) (w b):ℝ) := by
  have hh := hw a a b 0 (Or.inr hab)
  simpa only [splice_zero] using hh

/-- Once the original phases have been recovered, the original entry labels
cannot disagree with the switched labels at many positions. No new alignment
or reindexing of entries is permitted. -/
theorem entry_recovery (w : B → Fin m → A) {δ : ℝ} (hδ : 0<δ)
    (hw : Recognizes w δ) (u v : ℤ → A) (D a : ℕ) (ha : a < m) (t : ℤ)
    (U V : Fin (D-1) → B)
    (hU : ∀ j r,u (t+(a+j.val*m+r.val:ℕ))=w (U j) r)
    (hV : ∀ j r,v (t+(a+j.val*m+r.val:ℕ))=w (V j) r)
    (hclose : (mismatches (fun r : Fin (D*m) => u (t+r.val))
      (fun r : Fin (D*m) => v (t+r.val)):ℝ)<δ*(D*m)/100) :
    (mismatches U V:ℝ)<D/100 := by
  classical
  have hpoint (j : Fin (D-1)) :
      (if U j=V j then (0:ℝ) else 1)*(δ*m)≤(mismatches
        (fun r : Fin m => u (t+(a+j.val*m+r.val:ℕ)))
        (fun r : Fin m => v (t+(a+j.val*m+r.val:ℕ))):ℝ) := by
    by_cases hj : U j=V j
    · simp only [hj,ite_true,zero_mul]
      exact Nat.cast_nonneg _
    · rw [ite_eq_right hj,one_mul,show (fun r : Fin m => u (t+(a+j.val*m+r.val:ℕ)))=w (U j) by
        funext r; exact hU j r,
        show (fun r : Fin m => v (t+(a+j.val*m+r.val:ℕ)))=w (V j) by
        funext r; exact hV j r]
      exact distinct_word_cost w hw hj
  have hs := sum_le_sum (fun j (_ : j∈univ) => hpoint j)
  have hsum : (mismatches U V:ℝ)*(δ*m)≤(mismatches
      (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val)):ℝ) := by
    calc
      _ = ∑ j : Fin (D-1),(if U j=V j then (0:ℝ) else 1)*(δ*m) := by
        rw [←sum_mul,mismatches_sum]
        simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
      _ ≤ _ := hs
      _ ≤ _ := by exact_mod_cast complete_blocks_le D a ha u v t
  have hm : (0:ℝ) < m := by exact_mod_cast NeZero.pos m
  have hp : 0<δ*m := mul_pos hδ hm
  apply (mul_lt_mul_iff_left₀ hp).mp
  calc
    (mismatches U V:ℝ)*(δ*m) ≤ _ := hsum
    _ < _ := hclose
    _ = (D/100)*(δ*m) := by ring

/-- Pure entry pairing: two small label-error sets remove at most their sum
from a graph window. In particular the source constants give the literal .96
passing bound in the unchanged index order. -/
theorem paired_graph_bound {D : ℕ} (hD : 2≤D) (R : B → B → Prop)
    [DecidableRel R] (U V Z W : Fin (D-1) → B)
    (hgraph : ∀ j,R (Z j) (W j))
    (hU : (mismatches U Z:ℝ)<D/100) (hV : (mismatches V W:ℝ)<D/100) :
    (24/25:ℝ)≤(∑ j,if R (U j) (V j) then (1:ℝ) else 0)/(D-1) := by
  classical
  have hj (j : Fin (D-1)) :
      (1:ℝ)≤(if R (U j) (V j) then 1 else 0)+
        (if U j=Z j then 0 else 1)+(if V j=W j then 0 else 1) := by
    by_cases h₁ : U j=Z j
    · by_cases h₂ : V j=W j
      · simp only [h₁,h₂,hgraph j,ite_true]; norm_num
      · simp only [h₁,h₂,ite_true,ite_false]; split_ifs <;> norm_num
    · simp only [h₁,ite_false]; split_ifs <;> norm_num
  have hs := sum_le_sum (fun j (_ : j∈univ) => hj j)
  have he (L K : Fin (D-1) → B) :
      (∑ j,if L j=K j then (0:ℝ) else 1)=(mismatches L K:ℝ) := by
    rw [mismatches_sum]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  simp only [sum_add_distrib,he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,Nat.cast_sub (by omega : 1≤D),Nat.cast_one] at hs
  have hDr : (2:ℝ)≤D := by exact_mod_cast hD
  rw [le_div_iff₀ (by linarith : (0:ℝ)<D-1)]
  linarith
end SmoothObstruction.RecognitionWindow

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

lemma actual_legal (i : ℕ) (x : Extension) :
    RecognitionWindow.LegalAt (word i) x.val.1 (phase i x) := by
  intro t ht
  obtain ⟨a,ha⟩ := (x.property i).2 t ht
  exact ⟨a,fun r => (congrFun ha r).symm⟩

lemma actual_iterate_symbol (x : Extension) (j : ℕ) (t : ℤ) :
    ((T^[j] x).val).1 t=x.val.1 (t+j) := by
  rw [iterate_coe,PhaseDynamics.iterate_symbol]

lemma advance_phase (i : ℕ) (x : Extension) : phase i (advance i x)=0 :=
  Alignment.align_phase T (phase i) (fun _ => rfl) x

lemma measurable_advance (i : ℕ) : Measurable (advance i) :=
  Alignment.measurable_align T (phase i) measurable_T (measurable_phase i)

/-- Original ordered labels after the first true boundary, without changing
its phase or introducing a new pairing. -/
noncomputable def firstList (i D : ℕ) (x : Extension) : Fin (D-1) → A i :=
  labelList i (D-1) (advance i x)

lemma measurable_firstList (i D : ℕ) : Measurable (firstList i D) :=
  (measurable_labelList i (D-1)).comp (measurable_advance i)

lemma firstList_word (i D : ℕ) (x : Extension) (j : Fin (D-1)) (r : Fin (length 40000 i)) :
    x.val.1 (((-phase i x).val+j.val*length 40000 i+r.val:ℕ):ℤ)=
      word i (firstList i D x j) r := by
  let a := (-phase i x).val
  have hp : phase i ((T^[j.val*length 40000 i]) (advance i x))=0 := by
    rw [phase_iterate,advance_phase,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero]
  have hh := congrFun (word_label i ((T^[j.val*length 40000 i]) (advance i x))) r
  change word i (firstList i D x j) r=
    ((T^[j.val*length 40000 i] (advance i x)).val).1 (-(phase i ((T^[j.val*length 40000 i]) (advance i x))).val+(r.val:ℤ)) at hh
  rw [hp,ZMod.val_zero,Nat.cast_zero,neg_zero,zero_add,actual_iterate_symbol] at hh
  change word i (firstList i D x j) r=((T^[a] x).val).1 ((r.val:ℤ)+(j.val*length 40000 i:ℕ)) at hh
  rw [actual_iterate_symbol] at hh
  rw [hh]
  dsimp only [a]
  push_cast
  ring_nf

/-- On the actual extension, source symbol agreement recovers both the true
phase and all but D/100 of the original ordered labels. -/
theorem actual_recovery (i D : ℕ) (hD : 2≤D) (x z : Extension)
    (hclose : (mismatches (fun r : Fin (D*length 40000 i) => x.val.1 r.val)
      (fun r : Fin (D*length 40000 i) => z.val.1 r.val):ℝ)<
        (3/4:ℝ)*(D*length 40000 i)/100) :
    phase i x=phase i z ∧ (mismatches (firstList i D x) (firstList i D z):ℝ)<D/100 := by
  have hp := RecognitionWindow.phase_recovery (word i) (by norm_num : (0:ℝ)<3/4)
    (uniform_recognition i) x.val.1 z.val.1 (phase i x) (phase i z)
    (actual_legal i x) (actual_legal i z) D hD (-phase i x).val
    (ZMod.val_lt _) (ZMod.natCast_zmod_val _) hclose
  refine ⟨hp,?_⟩
  apply RecognitionWindow.entry_recovery (word i) (by norm_num : (0:ℝ)<3/4)
    (uniform_recognition i) x.val.1 z.val.1 D (-phase i x).val (ZMod.val_lt _) 0
    (firstList i D x) (firstList i D z)
  · intro j r
    simpa only [zero_add] using firstList_word i D x j r
  · intro j r
    simpa only [zero_add,hp] using firstList_word i D z j r
  · simpa only [zero_add] using hclose

lemma measurable_form_pair (i : ℕ) :
    Measurable (fun p : A i × A i => WordAlphabet.form (S i) p.1.val p.2.val) :=
  measurable_of_countable _

lemma measurable_graphWindows_at (i k : ℕ) (j : Fin (2^k-1)) :
    MeasurableSet {x : Extension | WordAlphabet.form (S i)
      (label i ((T^[j.val*length 40000 i]) x)).val
      (label i ((T^[(j.val+2^k)*length 40000 i]) x)).val=0} := by
  have hl : Measurable (fun x : Extension => label i ((T^[j.val*length 40000 i]) x)) :=
    (measurable_label i).comp (measurable_T.iterate _)
  have hr : Measurable (fun x : Extension => label i ((T^[(j.val+2^k)*length 40000 i]) x)) :=
    (measurable_label i).comp (measurable_T.iterate _)
  exact ((measurable_form_pair i).comp (hl.prodMk hr)) (measurableSet_singleton (0 : ZMod 2))

lemma measurable_graphWindows (i k : ℕ) : MeasurableSet {x | graphWindows i k x} := by
  change MeasurableSet {x | ∀ j : Fin (2^k-1), WordAlphabet.form (S i)
      (label i ((T^[j.val*length 40000 i]) x)).val
      (label i ((T^[(j.val+2^k)*length 40000 i]) x)).val=0}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (measurable_graphWindows_at i k)

/-- Actual graph-event probability under the stationary law, obtained by
pushing its first-boundary advance, never by assuming uniform parents. -/
theorem stationary_graph_probability (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i k : ℕ) (hk : k≤K (S i)/8) :
    1-((2*2^k-2:ℕ):ℝ)/H (S i)≤
      μ.real {x | graphWindows i k (advance i x)} := by
  have hh := boundary_graph_probability μ hT i k hk
  rw [←advance_map μ hT i] at hh
  simpa only [Measure.real,Measure.map_apply (measurable_advance i) (measurable_graphWindows i k),
    Set.preimage_ofPred_eq] using hh

end SmoothObstruction.WordHierarchy

end

end OAI
