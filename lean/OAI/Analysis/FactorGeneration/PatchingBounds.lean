import OAI.Analysis.FactorGeneration.PatchingWords

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact positive tolerance recurrence used in Popa Lemma 3.2. -/
section

def patchingTolerance (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | k+1 => (2 : ℝ)^(k+2)*patchingTolerance δ k

@[simp] theorem patchingTolerance_zero (δ : ℝ) : patchingTolerance δ 0=δ := rfl
@[simp] theorem patchingTolerance_succ (δ : ℝ) (k : ℕ) :
    patchingTolerance δ (k+1)=2^(k+2)*patchingTolerance δ k := rfl

theorem patchingTolerance_pos (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    0 < patchingTolerance δ k := by
  induction k with
  | zero => exact hδ
  | succ k ih => exact mul_pos (pow_pos (by norm_num) _) ih

theorem patchingTolerance_four_mul_le (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    4*patchingTolerance δ k ≤ patchingTolerance δ (k+1) := by
  have hp : (4 : ℝ) ≤ 2^(k+2) := by
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := k)
    rw [pow_add]
    norm_num
    nlinarith only [h]
  exact mul_le_mul_of_nonneg_right hp (patchingTolerance_pos δ hδ k).le

theorem patchingTolerance_mono (δ : ℝ) (hδ : 0 < δ) : Monotone (patchingTolerance δ) := by
  apply monotone_nat_of_le_succ
  intro k
  have hp := patchingTolerance_pos δ hδ k
  have hh := patchingTolerance_four_mul_le δ hδ k
  linarith

theorem middleMomentError_nonneg (ε : ℕ → ℝ) (hε : ∀ k,0 ≤ ε k) (r : ℕ) :
    0 ≤ middleMomentError ε r := by
  unfold middleMomentError
  split
  · exact le_rfl
  · exact hε r

/-- Choose eta=delta/3. Both middle moments fit within 2 epsilon_(r+2)/3. -/
theorem patchingTolerance_middle_budget (δ : ℝ) (hδ : 0 < δ) (r : ℕ) :
    δ/3+(middleMomentError (patchingTolerance δ) r+patchingTolerance δ (r+2))/3 ≤
      2*patchingTolerance δ (r+2)/3 := by
  have hm : middleMomentError (patchingTolerance δ) r ≤ patchingTolerance δ r := by
    unfold middleMomentError
    split
    · exact (patchingTolerance_pos δ hδ r).le
    · exact le_rfl
  have hd : δ ≤ patchingTolerance δ r := patchingTolerance_mono δ hδ (Nat.zero_le r)
  have hstep := patchingTolerance_four_mul_le δ hδ r
  have hstep2 := patchingTolerance_mono δ hδ (show r+1 ≤ r+2 by omega)
  have hp := patchingTolerance_pos δ hδ r
  linarith

end

/-! Explicit binary masks for the existing ordered expansion. A true bit is a
patch letter. Occurrences are retained even when their operator values coincide. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def binaryMasks : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (binaryMasks n).map (false :: ·) ++ (binaryMasks n).map (true :: ·)

theorem mem_binaryMasks (n : ℕ) (bs : List Bool) :
    bs ∈ binaryMasks n ↔ bs.length=n := by
  induction n generalizing bs with
  | zero => simp [binaryMasks]
  | succ n ih =>
    cases bs with
    | nil => simp [binaryMasks]
    | cons b bs => cases b <;> simp [binaryMasks,ih]

theorem binaryMasks_length (n : ℕ) : (binaryMasks n).length=2^n := by
  induction n with
  | zero => simp [binaryMasks]
  | succ n ih => simp [binaryMasks,ih,pow_succ]; omega

def maskedWord (v w : M.toStarSubalgebra) :
    List (Bool × M.toStarSubalgebra) → List Bool → M.toStarSubalgebra
  | [], _ => 1
  | (s,x)::xs, bs =>
      signedLetter (if bs.headD false then w else v) s*x*maskedWord v w xs bs.tail

theorem patchingExpansion_eq_masks (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    patchingExpansion v w xs = (binaryMasks xs.length).map
      (fun bs => (bs.count true,maskedWord v w xs bs)) := by
  induction xs with
  | nil => simp [patchingExpansion,binaryMasks,maskedWord]
  | cons a xs ih =>
    simp [patchingExpansion,binaryMasks,ih,List.map_map,Function.comp_def,maskedWord]

theorem maskedWord_append (v w : M.toStarSubalgebra)
    (xs ys : List (Bool × M.toStarSubalgebra)) (bs cs : List Bool)
    (hlen : bs.length=xs.length) :
    maskedWord v w (xs++ys) (bs++cs) = maskedWord v w xs bs*maskedWord v w ys cs := by
  induction xs generalizing bs with
  | nil => have hb : bs=[] := List.length_eq_zero_iff.mp hlen; simp [hb,maskedWord]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs => simp [maskedWord,ih bs (by simpa using hlen),mul_assoc]

theorem maskedWord_no_patch (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    maskedWord v w xs (List.replicate xs.length false)=patchingWord v xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [maskedWord,patchingWord,List.replicate_succ,ih]

theorem maskedWord_norm_le_one (v w : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (bs : List Bool)
    (hx : ∀ a ∈ xs,‖a.2‖ ≤ 1) : ‖maskedWord v w xs bs‖ ≤ 1 := by
  induction xs generalizing bs with
  | nil => exact (IsStarProjection.one _).norm_le
  | cons a xs ih =>
    have hp : ‖if bs.headD false then w else v‖ ≤ 1 := by split <;> assumption
    have ha := hx a (by simp)
    have ht := ih bs.tail (fun c hc => hx c (by simp [hc]))
    have hs : ‖signedLetter (if bs.headD false then w else v) a.1*a.2‖ ≤ 1 := by
      apply (norm_mul_le _ _).trans
      rw [signedLetter_norm]
      exact (mul_le_mul hp ha (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    exact (norm_mul_le _ _).trans
      ((mul_le_mul hs ht (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

/-- Locate the first patch, with no earlier patch occurrences. -/
theorem exists_first_true (bs : List Bool) (h : 1 ≤ bs.count true) :
    ∃ i cs,bs=List.replicate i false++true::cs := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | true => exact ⟨0,bs,rfl⟩
    | false =>
      obtain ⟨i,cs,he⟩ := ih (by simpa using h)
      exact ⟨i+1,cs,by simp [List.replicate_succ,he]⟩

/-- Locate the first two patches; all bits before and between them are false. -/
theorem exists_first_two_true (bs : List Bool) (h : 2 ≤ bs.count true) :
    ∃ i r cs,bs=List.replicate i false++true::(List.replicate r false++true::cs) := by
  obtain ⟨i,ds,he⟩ := exists_first_true bs (by omega)
  have hd : 1 ≤ ds.count true := by
    rw [he] at h
    simpa [List.count_replicate] using h
  obtain ⟨r,cs,hr⟩ := exists_first_true ds hd
  exact ⟨i,r,cs,by rw [he,hr]⟩

/-- The second moment has full word length only for the two-endpoint mask. -/
theorem first_two_full_length_iff (i r : ℕ) (cs : List Bool) :
    r+2=(List.replicate i false++true::(List.replicate r false++true::cs)).length ↔
      i=0 ∧ cs=[] := by
  simp only [List.length_append,List.length_replicate,List.length_cons]
  rw [← List.length_eq_zero_iff]
  omega

theorem first_two_other_length (i r : ℕ) (cs : List Bool) (h : i ≠ 0 ∨ cs ≠ []) :
    r+2+1 ≤ (List.replicate i false++true::(List.replicate r false++true::cs)).length := by
  have hn : cs ≠ [] → 0 < cs.length := List.length_pos_iff.mpr
  simp only [List.length_append,List.length_replicate,List.length_cons]
  rcases h with h | h
  · omega
  · have := hn h; omega

end

/-! Mask uniqueness and a deliberately coarse budget that avoids off-by-one
counts: 2^k ordinary budgets plus one exceptional budget fit epsilon_k. -/
section

theorem binaryMasks_nodup (n : ℕ) : (binaryMasks n).Nodup := by
  induction n with
  | zero => simp [binaryMasks]
  | succ n ih =>
    rw [binaryMasks,List.nodup_append]
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2),
      ih.map (fun _ _ h => List.cons.inj h |>.2),?_⟩
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    simp

theorem count_true_zero_iff (bs : List Bool) :
    bs.count true=0 ↔ bs=List.replicate bs.length false := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [List.replicate_succ,ih]

def exceptionalMask (k : ℕ) : List Bool := true::(List.replicate (k-2) false++[true])

theorem exceptionalMask_eq (r : ℕ) :
    exceptionalMask (r+2)=true::(List.replicate r false++[true]) := by
  simp [exceptionalMask]

theorem first_two_eq_exceptional (i r : ℕ) (cs : List Bool)
    (h : r+2=(List.replicate i false++true::(List.replicate r false++true::cs)).length) :
    List.replicate i false++true::(List.replicate r false++true::cs) =
      exceptionalMask (List.replicate i false++true::(List.replicate r false++true::cs)).length := by
  obtain ⟨hi,hcs⟩ := (first_two_full_length_iff i r cs).mp h
  subst i; subst cs
  simp [exceptionalMask,Nat.add_comm]
  omega

theorem sum_indicator_le {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (a : α) (B : ℝ) (hB : 0 ≤ B) :
    (xs.map (fun b => if b=a then B else 0)).sum ≤ B := by
  have he : (xs.map (fun b => if b=a then B else 0)).sum = (xs.count a : ℝ)*B := by
    clear hn
    induction xs with
    | nil => simp
    | cons b xs ih =>
      by_cases h : b=a
      · subst b; simp [ih,add_mul]; ring
      · simp [h,ih]
  rw [he]
  have hh : xs.count a ≤ 1 := (List.nodup_iff_count_le_one.mp hn) a
  have hh' : (xs.count a : ℝ) ≤ 1 := by exact_mod_cast hh
  exact (mul_le_mul_of_nonneg_right hh' hB).trans_eq (one_mul B)

theorem sum_three_budgets {α : Type*} [DecidableEq α]
    (xs : List α) (hn : xs.Nodup) (f : α → ℝ) (a b : α) (C A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ xs,f x ≤ C+(if x=a then A else 0)+(if x=b then B else 0)) :
    (xs.map f).sum ≤ (xs.length : ℝ)*C+A+B := by
  have he : (xs.map (fun x => C+(if x=a then A else 0)+(if x=b then B else 0))).sum =
      (xs.length : ℝ)*C+(xs.map (fun x => if x=a then A else 0)).sum+
        (xs.map (fun x => if x=b then B else 0)).sum := by
    clear hn hf
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
                      rw [ih]; ring
  have hle : (xs.map f).sum ≤
      (xs.map (fun x => C+(if x=a then A else 0)+(if x=b then B else 0))).sum := by
    clear he hn
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (hf x (by simp))
        (ih (fun y hy => hf y (by simp [hy])))
  rw [he] at hle
  have h₁ := sum_indicator_le xs hn a A hA
  have h₂ := sum_indicator_le xs hn b B hB
  linarith

/-- The coarse ordinary+exceptional budget is exactly epsilon_k. The two
special masks are each counted only once; no binomial count is assumed. -/
theorem patchingTolerance_mask_budget (δ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (2^k : ℝ)*(2*patchingTolerance δ (k-1)/3)+2*patchingTolerance δ k/3 =
      patchingTolerance δ k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,patchingTolerance_succ]
  rw [show j+2=(j+1)+1 by omega,pow_succ]
  ring

end

/-! Extract actual coefficient segments and fixed one-patch outer factors.
These lemmas apply to the source lists without assuming segment membership. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_list_split {α : Type*} (xs : List α) (i : ℕ) (hi : i < xs.length) :
    ∃ pre a post,xs=pre++a::post ∧ pre.length=i := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons a xs => exact ⟨[],a,xs,rfl,rfl⟩
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      obtain ⟨pre,b,post,he,hp⟩ := ih xs (by simpa using hi)
      exact ⟨a::pre,b,post,by simp [he],by simp [hp]⟩

theorem exists_list_split_two {α : Type*} (xs : List α) (i r : ℕ)
    (hlen : i+r+2 ≤ xs.length) :
    ∃ pre a mid b post,xs=pre++a::(mid++b::post) ∧ pre.length=i ∧ mid.length=r := by
  obtain ⟨pre,a,rest,he,hp⟩ := exists_list_split xs i (by omega)
  have hr : r < rest.length := by rw [he,List.length_append,List.length_cons,hp] at hlen; omega
  obtain ⟨mid,b,post,hm,hl⟩ := exists_list_split rest r hr
  exact ⟨pre,a,mid,b,post,by rw [he,hm],hp,hl⟩

theorem patchingCoefficients_before (F : Set M.toStarSubalgebra)
    (pre : List (Bool × M.toStarSubalgebra)) (a : Bool × M.toStarSubalgebra)
    (post : List (Bool × M.toStarSubalgebra))
    (h : patchingCoefficients F (pre++a::post)) :
    (∀ c ∈ pre,c.2 ∈ F) ∧ patchingCoefficients F (a::post) := by
  induction pre with
  | nil => exact ⟨by simp,h⟩
  | cons b pre ih =>
    have hb : b.2 ∈ F ∧ patchingCoefficients F (pre++a::post) := by
      cases pre <;> exact h
    obtain ⟨hi,ht⟩ := ih hb.2
    exact ⟨fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb.1
      · exact hi c hc,ht⟩

theorem patchingCoefficients_middle (F : Set M.toStarSubalgebra)
    (pre mid post : List (Bool × M.toStarSubalgebra)) (a b : Bool × M.toStarSubalgebra)
    (h : patchingCoefficients F (pre++a::(mid++b::post))) :
    a.2 ∈ F ∧ (∀ c ∈ mid,c.2 ∈ F) := by
  have ht := (patchingCoefficients_before F pre a (mid++b::post) h).2
  have hi := (patchingCoefficients_before F (a::mid) b post ht).1
  exact ⟨hi a (by simp),fun c hc => hi c (by simp [hc])⟩

theorem maskedWord_first_two (v w : M.toStarSubalgebra)
    (pre mid post : List (Bool × M.toStarSubalgebra)) (a b : Bool × M.toStarSubalgebra)
    (cs : List Bool) :
    maskedWord v w (pre++a::(mid++b::post))
      (List.replicate pre.length false++true::(List.replicate mid.length false++true::cs)) =
      patchingWord v pre*signedLetter w a.1*(a.2*patchingWord v mid)*
        signedLetter w b.1*(b.2*maskedWord v w post cs) := by
  rw [maskedWord_append v w pre _ _ _ (List.length_replicate ..),maskedWord_no_patch]
  simp only [maskedWord,List.headD_cons,List.tail_cons,↓reduceIte]
  rw [maskedWord_append v w mid _ _ _ (List.length_replicate ..),maskedWord_no_patch]
  simp [maskedWord,mul_assoc]

/-- Every mask with at least two true bits yields its actual internal middle
segment, with no assumptions about a separately supplied finite list. -/
theorem maskedWord_two_decomposition (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hc : patchingCoefficients F xs)
    (bs : List Bool) (hlen : bs.length=xs.length) (hcount : 2 ≤ bs.count true) :
    ∃ pre a mid b post cs,
      xs=pre++a::(mid++b::post) ∧
      bs=List.replicate pre.length false++true::(List.replicate mid.length false++true::cs) ∧
      a.2 ∈ F ∧ (∀ c ∈ mid,c.2 ∈ F) ∧ cs.length=post.length ∧
      mid.length+2 ≤ xs.length := by
  obtain ⟨i,r,cs,hbs⟩ := exists_first_two_true bs hcount
  have hlen' : i+r+2+cs.length=xs.length := by
    rw [hbs] at hlen
    simp only [List.length_append,List.length_replicate,List.length_cons] at hlen
    omega
  obtain ⟨pre,a,mid,b,post,hxs,hp,hm⟩ := exists_list_split_two xs i r (by omega)
  have hi := patchingCoefficients_middle F pre mid post a b (by rwa [← hxs])
  have ht : cs.length=post.length := by
    rw [hxs,List.length_append,List.length_cons,List.length_append,List.length_cons,hp,hm] at hlen'
    omega
  exact ⟨pre,a,mid,b,post,cs,hxs,by simpa [hp,hm] using hbs,hi.1,hi.2,ht,by omega⟩

theorem maskedWord_one (v w : M.toStarSubalgebra)
    (pre post : List (Bool × M.toStarSubalgebra)) (a : Bool × M.toStarSubalgebra) :
    maskedWord v w (pre++a::post)
      (List.replicate pre.length false++true::List.replicate post.length false) =
      patchingWord v pre*signedLetter w a.1*(a.2*patchingWord v post) := by
  rw [maskedWord_append v w pre _ _ _ (List.length_replicate ..),maskedWord_no_patch]
  simp [maskedWord,maskedWord_no_patch,mul_assoc]

end

/-! The triangle inequality for the exact noncommutative mask expansion. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem trace_list_sum (xs : List M.toStarSubalgebra) :
    τ.trace xs.sum=(xs.map τ.trace).sum := by
  induction xs with
  | nil => exact inner_zero_right _
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,cornerTrace_add,ih]

theorem norm_list_sum_le (xs : List ℂ) : ‖xs.sum‖ ≤ (xs.map norm).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa only [List.sum_cons,List.map_cons] using
      (norm_add_le x xs.sum).trans (add_le_add le_rfl ih)

theorem patching_trace_sum_le (v w x₀ : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    ‖τ.trace (x₀*patchingWord (v+w) xs)‖ ≤
      ((binaryMasks xs.length).map (fun bs => ‖τ.trace (x₀*maskedWord v w xs bs)‖)).sum := by
  rw [← patchingExpansion_sum,patchingExpansion_eq_masks]
  simp only [List.map_map,Function.comp_def]
  rw [← sum_map_left_mul,trace_list_sum]
  simpa only [List.map_map,Function.comp_def] using norm_list_sum_le
    ((((binaryMasks xs.length).map (fun bs => maskedWord v w xs bs)).map (fun z => x₀*z)).map τ.trace)

end Generator.Tracial

end

end OAI
