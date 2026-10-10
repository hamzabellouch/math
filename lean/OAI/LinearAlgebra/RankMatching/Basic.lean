import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.RankMatching

variable {k : Type*} [Field k]

open scoped Classical

def Triangular (A : Matrix ℤ ℤ k) : Prop := ∀ l j, j < l → A l j = 0

def block (A : Matrix ℤ ℤ k) (l j : ℤ) : Matrix (Set.Icc l j) (Set.Icc l j) k :=
  fun r c => A r c

noncomputable def blockRank (A : Matrix ℤ ℤ k) (l j : ℤ) : ℕ := (block A l j).rank

noncomputable def weight (A : Matrix ℤ ℤ k) (l j : ℤ) : ℤ :=
  (blockRank A l j : ℤ) - blockRank A l (j - 1) - blockRank A (l + 1) j +
    blockRank A (l + 1) (j - 1)

def Matched (A : Matrix ℤ ℤ k) (l j : ℤ) : Prop := weight A l j = 1

def OldUnmatched (A : Matrix ℤ ℤ k) (l j : ℤ) : Prop :=
  blockRank A l (j - 1) = blockRank A (l + 1) (j - 1) ∧
  blockRank A (l + 1) j = blockRank A (l + 1) (j - 1)

def PriorAgreement (A B : Matrix ℤ ℤ k) (l j : ℤ) : Prop :=
  ∀ r c, l ≤ r → r ≤ c → c ≤ j → c - r < j - l → A r c = B r c

noncomputable def matchingCount (A : Matrix ℤ ℤ k) (l j : ℤ) : ℕ := by
  classical
  exact ((Finset.Icc l j ×ˢ Finset.Icc l j).filter
    (fun rc : ℤ × ℤ => Matched A rc.1 rc.2)).card

def column (A : Matrix ℤ ℤ k) (l j : ℤ) : ℤ → k :=
  fun r => if l ≤ r then A r j else 0

def columnSpace (A : Matrix ℤ ℤ k) (l j : ℤ) : Submodule k (ℤ → k) :=
  Submodule.span k (column A l '' Set.Iic j)

lemma column_zero (A : Matrix ℤ ℤ k) (hA : Triangular A) {l j : ℤ} (h : j < l) :
    column A l j = 0 := by
  ext r
  by_cases hr : l ≤ r
  · simp [column, hr, hA r j (lt_of_lt_of_le h hr)]
  · simp [column, hr]

lemma columnSpace_eq_finite (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    columnSpace A l j = Submodule.span k (column A l '' Set.Icc l j) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, rfl⟩
    by_cases hlc : l ≤ c
    · exact Submodule.subset_span ⟨c, ⟨hlc, hc⟩, rfl⟩
    · rw [column_zero A hA (lt_of_not_ge hlc)]
      exact Submodule.zero_mem _
  · exact Submodule.span_mono (Set.image_mono fun _ h => h.2)

lemma columnSpace_finite (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    FiniteDimensional k (columnSpace A l j) := by
  rw [columnSpace_eq_finite A hA]
  exact FiniteDimensional.span_of_finite k ((Set.finite_Icc l j).image _)

lemma columnSpace_step (A : Matrix ℤ ℤ k) (l j : ℤ) :
    columnSpace A l j = columnSpace A l (j - 1) ⊔ Submodule.span k {column A l j} := by
  have hset : Set.Iic j = insert j (Set.Iic (j - 1)) := by
    ext c
    simp only [Set.mem_Iic, Set.mem_insert_iff]
    omega
  simp only [columnSpace, hset, Set.image_insert_eq, Submodule.span_insert]
  exact sup_comm _ _

lemma finrank_sup_singleton {V : Type*} [AddCommGroup V] [Module k V]
    (S : Submodule k V) [FiniteDimensional k S] (v : V) :
    Module.finrank k (S ⊔ Submodule.span k {v} : Submodule k V) =
      Module.finrank k S + if v ∈ S then 0 else 1 := by
  classical
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv, add_zero, sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hv))]
  · have hd := (Submodule.disjoint_span_singleton_of_notMem hv).eq_bot
    have heq := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span k {v})
    have hn : v ≠ 0 := fun h => hv (h ▸ S.zero_mem)
    rw [hd, finrank_bot, add_zero, finrank_span_singleton hn] at heq
    simpa [hv] using heq

noncomputable def intervalExtend (l j : ℤ) : (Set.Icc l j → k) →ₗ[k] (ℤ → k) where
  toFun v r := if h : l ≤ r ∧ r ≤ j then v ⟨r,h⟩ else 0
  map_add' v w := by ext r; by_cases h : l ≤ r ∧ r ≤ j <;> simp [h]
  map_smul' a v := by ext r; by_cases h : l ≤ r ∧ r ≤ j <;> simp [h]

lemma intervalExtend_injective (l j : ℤ) :
    Function.Injective (intervalExtend (k := k) l j) := by
  intro v w heq
  ext r
  have h := congrFun heq r
  simpa [intervalExtend, r.property.1, r.property.2] using h

lemma intervalExtend_col (A : Matrix ℤ ℤ k) (hA : Triangular A)
    (l j : ℤ) (c : Set.Icc l j) :
    intervalExtend l j ((block A l j).col c) = column A l c := by
  ext r
  by_cases hr : l ≤ r ∧ r ≤ j
  · simp [intervalExtend, column, hr, Matrix.col, block]
  · by_cases hlr : l ≤ r
    · have hjr : j < r := by simpa [Set.mem_Icc, hlr] using hr
      simp [intervalExtend, column, hlr, not_le.mpr hjr, hA r c (lt_of_le_of_lt c.property.2 hjr)]
    · simp [intervalExtend, column, hlr]

lemma columnSpace_eq_map (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    columnSpace A l j =
      (Submodule.span k (Set.range (block A l j).col)).map (intervalExtend l j) := by
  rw [columnSpace_eq_finite A hA, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨(block A l j).col ⟨c,hc⟩, ⟨⟨c,hc⟩, rfl⟩, ?_⟩
    exact intervalExtend_col A hA l j ⟨c,hc⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, c.property, (intervalExtend_col A hA l j c).symm⟩

lemma blockRank_eq_finrank (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    blockRank A l j = Module.finrank k (columnSpace A l j) := by
  rw [blockRank, Matrix.rank_eq_finrank_span_cols, columnSpace_eq_map A hA]
  exact (Submodule.equivMapOfInjective (intervalExtend l j)
    (intervalExtend_injective l j) _).finrank_eq

noncomputable def increment (A : Matrix ℤ ℤ k) (l j : ℤ) : ℕ :=
  if column A l j ∈ columnSpace A l (j - 1) then 0 else 1

lemma blockRank_step (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    blockRank A l j = blockRank A l (j - 1) + increment A l j := by
  let := columnSpace_finite A hA l (j - 1)
  rw [blockRank_eq_finrank A hA, columnSpace_step, finrank_sup_singleton,
    blockRank_eq_finrank A hA]
  rfl

def rowCut (l : ℤ) : (ℤ → k) →ₗ[k] (ℤ → k) where
  toFun v r := if l ≤ r then v r else 0
  map_add' v w := by ext r; by_cases h : l ≤ r <;> simp [h]
  map_smul' a v := by ext r; by_cases h : l ≤ r <;> simp [h]

lemma rowCut_column (A : Matrix ℤ ℤ k) {l l' : ℤ} (h : l ≤ l') (j : ℤ) :
    rowCut l' (column A l j) = column A l' j := by
  ext r
  by_cases hr : l' ≤ r
  · simp [rowCut, column, hr, le_trans h hr]
  · simp [rowCut, column, hr]

lemma rowCut_columnSpace (A : Matrix ℤ ℤ k) {l l' : ℤ} (h : l ≤ l') (j : ℤ) :
    columnSpace A l j ≤ (columnSpace A l' j).comap (rowCut l') := by
  apply Submodule.span_le.mpr
  rintro _ ⟨c, hc, rfl⟩
  change rowCut l' (column A l c) ∈ columnSpace A l' j
  rw [rowCut_column A h]
  exact Submodule.subset_span ⟨c, hc, rfl⟩

lemma increment_antitone (A : Matrix ℤ ℤ k) (j : ℤ) :
    Antitone (fun l => increment A l j) := by
  intro l l' h
  change increment A l' j ≤ increment A l j
  unfold increment
  split_ifs with h' h₀ h₀
  · exact le_rfl
  · exact Nat.zero_le _
  · exfalso
    apply h'
    have hm := rowCut_columnSpace A h (j - 1) h₀
    change rowCut l' (column A l j) ∈ columnSpace A l' (j - 1) at hm
    simpa [rowCut_column A h] using hm
  · exact le_rfl

lemma increment_le_one (A : Matrix ℤ ℤ k) (l j : ℤ) : increment A l j ≤ 1 := by
  unfold increment
  split_ifs <;> omega

lemma weight_eq_increment_sub (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    weight A l j = (increment A l j : ℤ) - increment A (l + 1) j := by
  unfold weight
  have h₁ := blockRank_step A hA l j
  have h₂ := blockRank_step A hA (l + 1) j
  omega

lemma weight_zero_or_one (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    weight A l j = 0 ∨ weight A l j = 1 := by
  rw [weight_eq_increment_sub A hA]
  have h₁ := increment_le_one A l j
  have h₂ := increment_le_one A (l + 1) j
  have h₃ := increment_antitone A j (show l ≤ l + 1 by omega)
  dsimp only at h₃
  omega

lemma matched_iff_increments (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    Matched A l j ↔ increment A l j = 1 ∧ increment A (l + 1) j = 0 := by
  unfold Matched
  rw [weight_eq_increment_sub A hA]
  have h₁ := increment_le_one A l j
  have h₂ := increment_le_one A (l + 1) j
  omega

lemma column_unique (A : Matrix ℤ ℤ k) (hA : Triangular A) {l l' j : ℤ}
    (h : Matched A l j) (h' : Matched A l' j) : l = l' := by
  obtain ⟨hp, hn⟩ := (matched_iff_increments A hA l j).mp h
  obtain ⟨hp', hn'⟩ := (matched_iff_increments A hA l' j).mp h'
  rcases lt_trichotomy l l' with hlt | heq | hgt
  · have hm := increment_antitone A j (show l + 1 ≤ l' by omega)
    dsimp only at hm
    omega
  · exact heq
  · have hm := increment_antitone A j (show l' + 1 ≤ l by omega)
    dsimp only at hm
    omega

def reflected (A : Matrix ℤ ℤ k) : Matrix ℤ ℤ k := fun l j => A (-j) (-l)

lemma triangular_reflected (A : Matrix ℤ ℤ k) (hA : Triangular A) :
    Triangular (reflected A) := by
  intro l j h
  exact hA (-j) (-l) (by omega)

def negInterval (l j : ℤ) : Set.Icc l j ≃ Set.Icc (-j) (-l) where
  toFun x := ⟨-x, by obtain ⟨h₁,h₂⟩ := x.property; constructor <;> omega⟩
  invFun x := ⟨-x, by obtain ⟨h₁,h₂⟩ := x.property; constructor <;> omega⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

lemma blockRank_reflected (A : Matrix ℤ ℤ k) (l j : ℤ) :
    blockRank (reflected A) l j = blockRank A (-j) (-l) := by
  have heq : block (reflected A) l j =
      ((block A (-j) (-l)).transpose).submatrix (negInterval l j) (negInterval l j) := rfl
  rw [blockRank, heq, Matrix.rank_submatrix, Matrix.rank_transpose]
  rfl

lemma weight_reflected (A : Matrix ℤ ℤ k) (l j : ℤ) :
    weight (reflected A) l j = weight A (-j) (-l) := by
  unfold weight
  simp only [blockRank_reflected]
  have h₁ : -(j - 1) = -j + 1 := by omega
  have h₂ : -(l + 1) = -l - 1 := by omega
  rw [h₁, h₂]
  ring

lemma row_unique (A : Matrix ℤ ℤ k) (hA : Triangular A) {l j j' : ℤ}
    (h : Matched A l j) (h' : Matched A l j') : j = j' := by
  have hr : Matched (reflected A) (-j) (-l) := by
    simpa only [Matched, weight_reflected, neg_neg] using h
  have hr' : Matched (reflected A) (-j') (-l) := by
    simpa only [Matched, weight_reflected, neg_neg] using h'
  have hn := column_unique (reflected A) (triangular_reflected A hA) hr hr'
  omega

lemma blockRank_zero (A : Matrix ℤ ℤ k) {l j : ℤ} (h : j < l) :
    blockRank A l j = 0 := by
  have heq : block A l j = 0 := by
    ext r c
    obtain ⟨h₁,h₂⟩ := r.property
    omega
  rw [blockRank, heq, Matrix.rank_zero]

lemma increment_zero (A : Matrix ℤ ℤ k) (hA : Triangular A) {l j : ℤ} (h : j < l) :
    increment A l j = 0 := by
  simp only [increment, column_zero A hA h, Submodule.zero_mem, ite_true]

lemma sum_interval_difference (f : ℤ → ℤ) (l j : ℤ) (h : l ≤ j + 1) :
    (∑ r ∈ Finset.Icc l j, (f r - f (r + 1))) = f l - f (j + 1) := by
  have hl : l - 1 ≤ j := by omega
  induction j, hl using Int.leInduction with
  | base => simp
  | succ n hn ih =>
    have heq : Finset.Icc l (n + 1) = insert (n + 1) (Finset.Icc l n) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [heq, Finset.sum_insert (by simp), ih (by omega)]
    ring

lemma sum_interval_predecessor (f : ℤ → ℤ) (l j : ℤ) (h : l ≤ j + 1) :
    (∑ r ∈ Finset.Icc l j, (f r - f (r - 1))) = f j - f (l - 1) := by
  have heq := sum_interval_difference (fun r => f (r - 1)) l j h
  simp only [add_sub_cancel_right] at heq
  rw [Finset.sum_sub_distrib] at heq ⊢
  omega

lemma sum_weights (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    (∑ r ∈ Finset.Icc l j, ∑ c ∈ Finset.Icc l j, weight A r c) = blockRank A l j := by
  by_cases h : l ≤ j
  · rw [Finset.sum_comm]
    calc
      _ = ∑ c ∈ Finset.Icc l j, (increment A l c : ℤ) := by
        apply Finset.sum_congr rfl
        intro c hc
        simp_rw [weight_eq_increment_sub A hA]
        rw [sum_interval_difference _ l j (by omega)]
        rw [increment_zero A hA (show c < j + 1 by have := (Finset.mem_Icc.mp hc).2; omega)]
        simp
      _ = blockRank A l j := by
        have heq := sum_interval_predecessor (fun c => (blockRank A l c : ℤ)) l j (by omega)
        have hz := blockRank_zero A (l := l) (j := l - 1) (by omega)
        rw [hz, Nat.cast_zero, sub_zero] at heq
        rw [← heq]
        apply Finset.sum_congr rfl
        intro c hc
        have hs := blockRank_step A hA l c
        omega
  · have h' : j < l := lt_of_not_ge h
    rw [Finset.Icc_eq_empty_of_lt h', Finset.sum_empty, blockRank_zero A h']
    rfl

lemma rank_eq_count (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) :
    blockRank A l j = matchingCount A l j := by
  have hw : ∀ r c, weight A r c = if Matched A r c then (1 : ℤ) else 0 := by
    intro r c
    rcases weight_zero_or_one A hA r c with h | h
    · simp [Matched, h]
    · simp [Matched, h]
  have hs := sum_weights A hA l j
  simp_rw [hw] at hs
  rw [← Finset.sum_product (Finset.Icc l j) (Finset.Icc l j)
    (fun rc : ℤ × ℤ => if Matched A rc.1 rc.2 then (1 : ℤ) else 0)] at hs
  rw [Finset.sum_boole] at hs
  exact_mod_cast hs.symm

theorem rank_matching (A : Matrix ℤ ℤ k) (hA : Triangular A) :
    (∀ l j, weight A l j = 0 ∨ weight A l j = 1) ∧
    (∀ l j j', Matched A l j → Matched A l j' → j = j') ∧
    (∀ l l' j, Matched A l j → Matched A l' j → l = l') ∧
    (∀ l j, blockRank A l j = matchingCount A l j) := by
  exact ⟨weight_zero_or_one A hA, fun _ _ _ => row_unique A hA,
    fun _ _ _ => column_unique A hA, rank_eq_count A hA⟩

lemma increment_eq_zero_iff (A : Matrix ℤ ℤ k) (l j : ℤ) :
    increment A l j = 0 ↔ column A l j ∈ columnSpace A l (j - 1) := by
  simp [increment]

lemma increment_eq_one_iff (A : Matrix ℤ ℤ k) (l j : ℤ) :
    increment A l j = 1 ↔ column A l j ∉ columnSpace A l (j - 1) := by
  simp [increment]

lemma rowCut_map_columnSpace (A : Matrix ℤ ℤ k) {l l' : ℤ} (h : l ≤ l') (j : ℤ) :
    (columnSpace A l j).map (rowCut l') = columnSpace A l' j := by
  simp only [columnSpace, Submodule.map_span, Set.image_image]
  congr 2
  funext c
  exact rowCut_column A h c

lemma columnSpace_supported (A : Matrix ℤ ℤ k) (l j : ℤ)
    {v : ℤ → k} (hv : v ∈ columnSpace A l j) {r : ℤ} (hr : r < l) : v r = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨c, hc, rfl⟩
    simp [column, not_le.mpr hr]
  · rfl
  · intro x y hx hy hx0 hy0
    simp [hx0, hy0]
  · intro a x hx hx0
    simp [hx0]

lemma rowCut_injOn_of_equal_ranks (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ)
    (heq : blockRank A l j = blockRank A (l + 1) j) :
    Set.InjOn (rowCut (k := k) (l + 1)) (columnSpace A l j) := by
  let := columnSpace_finite A hA l j
  let := columnSpace_finite A hA (l + 1) j
  let f : columnSpace A l j →ₗ[k] columnSpace A (l + 1) j :=
    (rowCut (l + 1)).restrict (fun _ hv => rowCut_columnSpace A (by omega) j hv)
  have hf : Function.Surjective f := by
    intro v
    have hm : (v : ℤ → k) ∈ (columnSpace A l j).map (rowCut (l + 1)) := by
      rw [rowCut_map_columnSpace A (by omega)]
      exact v.property
    obtain ⟨w,hw,he⟩ := Submodule.mem_map.mp hm
    exact ⟨⟨w,hw⟩, Subtype.ext he⟩
  have hdim : Module.finrank k (columnSpace A l j) =
      Module.finrank k (columnSpace A (l + 1) j) := by
    simpa only [blockRank_eq_finrank A hA] using heq
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf
  intro v hv w hw he
  exact congrArg Subtype.val (hi (show f ⟨v,hv⟩ = f ⟨w,hw⟩ from Subtype.ext he))

lemma matched_oldUnmatched (A : Matrix ℤ ℤ k) (hA : Triangular A) {l j : ℤ}
    (h : Matched A l j) : OldUnmatched A l j := by
  have hr : Matched (reflected A) (-j) (-l) := by
    simpa only [Matched, weight_reflected, neg_neg] using h
  have hn := ((matched_iff_increments A hA l j).mp h).2
  have hn' := ((matched_iff_increments (reflected A)
    (triangular_reflected A hA) (-j) (-l)).mp hr).2
  have hs := blockRank_step A hA (l + 1) j
  have hs' := blockRank_step (reflected A) (triangular_reflected A hA) (-j + 1) (-l)
  rw [hn', add_zero] at hs'
  simp only [blockRank_reflected, neg_neg] at hs'
  have heq₁ : -(-j + 1) = j - 1 := by omega
  have heq₂ : -(-l - 1) = l + 1 := by omega
  rw [heq₁, heq₂] at hs'
  exact ⟨hs', by omega⟩

lemma block_eq_of_prior {A B : Matrix ℤ ℤ k} (hA : Triangular A) (hB : Triangular B)
    {l j : ℤ} (hab : PriorAgreement A B l j) (L J : ℤ)
    (hl : l ≤ L) (hj : J ≤ j) (hdepth : J - L < j - l) :
    block A L J = block B L J := by
  ext r c
  change A r c = B r c
  by_cases hrc : (r : ℤ) ≤ c
  · apply hab r c (le_trans hl r.property.1) hrc (le_trans c.property.2 hj)
    obtain ⟨hr₁,hr₂⟩ := r.property
    obtain ⟨hc₁,hc₂⟩ := c.property
    omega
  · rw [hA r c (lt_of_not_ge hrc), hB r c (lt_of_not_ge hrc)]

lemma oldUnmatched_of_prior {A B : Matrix ℤ ℤ k} (hA : Triangular A) (hB : Triangular B)
    {l j : ℤ} (hab : PriorAgreement A B l j) :
    OldUnmatched A l j ↔ OldUnmatched B l j := by
  have h₁ := block_eq_of_prior hA hB hab l (j - 1) (by omega) (by omega) (by omega)
  have h₂ := block_eq_of_prior hA hB hab (l + 1) j (by omega) (by omega) (by omega)
  have h₃ := block_eq_of_prior hA hB hab (l + 1) (j - 1) (by omega) (by omega) (by omega)
  unfold OldUnmatched blockRank
  rw [h₁,h₂,h₃]

lemma prior_columnSpace {A B : Matrix ℤ ℤ k} (hA : Triangular A) (hB : Triangular B)
    {l j : ℤ} (hab : PriorAgreement A B l j) :
    columnSpace A l (j - 1) = columnSpace B l (j - 1) := by
  unfold columnSpace
  congr 1
  apply Set.image_congr
  intro c hc
  ext r
  by_cases hr : l ≤ r
  · by_cases hrc : r ≤ c
    · simp only [column, ite_eq_left hr]
      exact hab r c hr hrc (by have := hc; simp only [Set.mem_Iic] at this; omega) (by
        have := hc; simp only [Set.mem_Iic] at this; omega)
    · simp [column, hr, hA r c (lt_of_not_ge hrc), hB r c (lt_of_not_ge hrc)]
  · simp [column, hr]

lemma prior_lower_column {A B : Matrix ℤ ℤ k} (hA : Triangular A) (hB : Triangular B)
    {l j : ℤ} (hab : PriorAgreement A B l j) :
    column A (l + 1) j = column B (l + 1) j := by
  ext r
  by_cases hr : l + 1 ≤ r
  · by_cases hrj : r ≤ j
    · simp only [column, ite_eq_left hr]
      exact hab r j (by omega) hrj le_rfl (by omega)
    · simp [column, hr, hA r j (lt_of_not_ge hrj), hB r j (lt_of_not_ge hrj)]
  · simp [column, hr]

lemma oldUnmatched_lower_increment {A : Matrix ℤ ℤ k} (hA : Triangular A) {l j : ℤ}
    (h : OldUnmatched A l j) : increment A (l + 1) j = 0 := by
  have hs := blockRank_step A hA (l + 1) j
  have heq := h.2
  omega

lemma exceptional_exists (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ)
    (hold : OldUnmatched A l j) :
    ∃ c : k, ∀ B : Matrix ℤ ℤ k, Triangular B → PriorAgreement A B l j →
      (Matched B l j ↔ B l j ≠ c) := by
  have hi0 := oldUnmatched_lower_increment hA hold
  have hu : column A (l + 1) j ∈ columnSpace A (l + 1) (j - 1) :=
    (increment_eq_zero_iff A (l + 1) j).mp hi0
  have hm : column A (l + 1) j ∈ (columnSpace A l (j - 1)).map (rowCut (l + 1)) := by
    rw [rowCut_map_columnSpace A (by omega)]
    exact hu
  obtain ⟨v,hv,hproj⟩ := Submodule.mem_map.mp hm
  have hinj := rowCut_injOn_of_equal_ranks A hA l (j - 1) hold.1
  refine ⟨v l, ?_⟩
  intro B hB hab
  have hS := prior_columnSpace hA hB hab
  have hlow := prior_lower_column hA hB hab
  have hmem : column B l j ∈ columnSpace B l (j - 1) ↔ B l j = v l := by
    constructor
    · intro hb
      have hb' : column B l j ∈ columnSpace A l (j - 1) := by rwa [hS]
      have he : rowCut (l + 1) (column B l j) = rowCut (l + 1) v := by
        rw [rowCut_column B (show l ≤ l + 1 by omega), hproj, hlow]
      have hc := hinj hb' hv he
      have hf := congrFun hc l
      simpa [column] using hf
    · intro hc
      have he : column B l j = v := by
        ext r
        rcases lt_trichotomy r l with hr | hr | hr
        · simp [column, not_le.mpr hr, columnSpace_supported A l (j - 1) hv hr]
        · subst r
          simpa [column] using hc
        · have hr1 : l + 1 ≤ r := by omega
          have ht := congrFun (hproj.trans hlow) r
          change (if l + 1 ≤ r then v r else 0) =
            (if l + 1 ≤ r then B r j else 0) at ht
          simp only [ite_eq_left hr1] at ht
          simpa [column, show l ≤ r by omega] using ht.symm
      rw [he, ← hS]
      exact hv
  have holdB := (oldUnmatched_of_prior hA hB hab).mp hold
  have hiB := oldUnmatched_lower_increment hB holdB
  simp only [matched_iff_increments B hB, hiB, and_true,
    increment_eq_one_iff, hmem]

def cornerUpdate (A : Matrix ℤ ℤ k) (l j : ℤ) (c : k) : Matrix ℤ ℤ k :=
  fun r s => if r = l ∧ s = j then c else A r s

lemma triangular_cornerUpdate (A : Matrix ℤ ℤ k) (hA : Triangular A) {l j : ℤ}
    (hlj : l ≤ j) (c : k) : Triangular (cornerUpdate A l j c) := by
  intro r s hrs
  have hn : ¬ (r = l ∧ s = j) := by rintro ⟨rfl,rfl⟩; omega
  simp [cornerUpdate, hn, hA r s hrs]

omit [Field k] in
lemma prior_cornerUpdate (A : Matrix ℤ ℤ k) (l j : ℤ) (c : k) :
    PriorAgreement A (cornerUpdate A l j c) l j := by
  intro r s hlr hrs hsj hd
  have hn : ¬ (r = l ∧ s = j) := by rintro ⟨rfl,rfl⟩; omega
  simp [cornerUpdate, hn]

theorem corner_rule (A : Matrix ℤ ℤ k) (hA : Triangular A) (l j : ℤ) (hlj : l ≤ j) :
    (OldUnmatched A l j → ∃! c : k, ∀ B : Matrix ℤ ℤ k,
      Triangular B → PriorAgreement A B l j →
      (Matched B l j ↔ B l j ≠ c)) ∧
    (¬ OldUnmatched A l j → ∀ B : Matrix ℤ ℤ k,
      Triangular B → PriorAgreement A B l j → ¬ Matched B l j) := by
  constructor
  · intro hold
    obtain ⟨c,hc⟩ := exceptional_exists A hA l j hold
    refine ⟨c,hc,?_⟩
    intro c' hc'
    by_contra hne
    let B := cornerUpdate A l j c'
    have hB := triangular_cornerUpdate A hA hlj c'
    have hp := prior_cornerUpdate A l j c'
    have hm : Matched B l j := (hc B hB hp).mpr (by simpa [B, cornerUpdate] using hne)
    have hf := (hc' B hB hp).mp hm
    simp [B, cornerUpdate] at hf
  · intro hold B hB hab hm
    apply hold
    exact (oldUnmatched_of_prior hA hB hab).mpr (matched_oldUnmatched B hB hm)

end HahnWilson.RankMatching

end

end OAI
