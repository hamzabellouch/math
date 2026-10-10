import OAI.Geometry.TranslativeCovering.DiagramCrossBounds

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace MatchingSelf
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} [Fintype I]

abbrev OffMatching (I : Type u_2) [Fintype I] :=
  {M : Matching I I // ∀ e ∈ M.val, e.1 ≠ e.2}

noncomputable def off (M : Matching I I) : OffMatching I :=
  ⟨⟨M.val.filter (fun e => e.1 ≠ e.2), by
    constructor
    · intro i j k h hj; exact M.property.1 i j k
        (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp hj).1
    · intro i j k h hj; exact M.property.2 i j k
        (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp hj).1⟩,
    by intro e he; exact (Finset.mem_filter.mp he).2⟩

noncomputable def available (P : OffMatching I) : Finset I :=
  Finset.univ.filter (fun i => (∀ j, (i,j) ∉ P.val.val) ∧ (∀ j, (j,i) ∉ P.val.val))

abbrev Loops (P : OffMatching I) := {L : Finset I // L ⊆ available P}

noncomputable def loops (M : Matching I I) : Loops (off M) :=
  ⟨Finset.univ.filter (fun i => (i,i) ∈ M.val), by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    simp only [available, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro j hj
      have hh := (Finset.mem_filter.mp hj)
      exact hh.2 (M.property.1 i j i hh.1 h).symm
    · intro j hj
      have hh := (Finset.mem_filter.mp hj)
      exact hh.2 (M.property.2 j i i hh.1 h)⟩

noncomputable def join (P : OffMatching I) (L : Loops P) : Matching I I :=
  ⟨P.val.val ∪ L.val.diag, by
    constructor
    · intro i j k hij hik
      rcases Finset.mem_union.mp hij with hp | hl
      · rcases Finset.mem_union.mp hik with hq | hm
        · exact P.val.property.1 _ _ _ hp hq
        · have hd := Finset.mem_diag.mp hm
          dsimp only [Prod.fst, Prod.snd] at hd
          obtain ⟨hi, rfl⟩ := hd
          exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.1 j hp)
      · have hd := Finset.mem_diag.mp hl
        dsimp only [Prod.fst, Prod.snd] at hd
        obtain ⟨hi, rfl⟩ := hd
        rcases Finset.mem_union.mp hik with hq | hm
        · exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.1 k hq)
        · exact (Finset.mem_diag.mp hm).2
    · intro i j k hik hjk
      rcases Finset.mem_union.mp hik with hp | hl
      · rcases Finset.mem_union.mp hjk with hq | hm
        · exact P.val.property.2 _ _ _ hp hq
        · have hd := Finset.mem_diag.mp hm
          dsimp only [Prod.fst, Prod.snd] at hd
          obtain ⟨hi, rfl⟩ := hd
          exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.2 i hp)
      · have hd := Finset.mem_diag.mp hl
        dsimp only [Prod.fst, Prod.snd] at hd
        obtain ⟨hi, rfl⟩ := hd
        rcases Finset.mem_union.mp hjk with hq | hm
        · exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.2 j hq)
        · exact (Finset.mem_diag.mp hm).2.symm⟩

lemma join_off_loops (M : Matching I I) : join (off M) (loops M) = M := by
  apply Subtype.ext
  ext ⟨i,j⟩
  simp only [join, off, loops, Finset.mem_union, Finset.mem_filter,
    Finset.mem_diag, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h,_⟩ | ⟨h,rfl⟩) <;> exact h
  · intro h
    by_cases hij : i = j
    · subst j; exact Or.inr ⟨h,rfl⟩
    · exact Or.inl ⟨h,hij⟩

lemma off_join (P : OffMatching I) (L : Loops P) : off (join P L) = P := by
  apply Subtype.ext
  apply Subtype.ext
  ext ⟨i,j⟩
  simp only [off, join, Finset.mem_filter, Finset.mem_union, Finset.mem_diag]
  constructor
  · rintro ⟨h, hne⟩
    rcases h with h | ⟨_, he⟩
    · exact h
    · exact False.elim (hne he)
  · intro h; exact ⟨Or.inl h, P.property _ h⟩

lemma loops_join_val (P : OffMatching I) (L : Loops P) :
    (loops (join P L)).val = L.val := by
  ext i
  simp only [loops, join, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_union, Finset.mem_diag, and_true, true_and]
  exact or_iff_right (fun h => P.property (i,i) h rfl)

noncomputable def splitEquiv : Matching I I ≃ (Σ P : OffMatching I, Loops P) where
  toFun M := ⟨off M, loops M⟩
  invFun x := join x.1 x.2
  left_inv := join_off_loops
  right_inv := by
    intro ⟨P,L⟩
    apply Sigma.ext (off_join P L)
    apply (Subtype.heq_iff_coe_eq (by intro x; dsimp only; rw [off_join])).mpr
    exact loops_join_val P L

lemma join_product (h : I × I → ℝ) (P : OffMatching I) (L : Loops P) :
    (∏ e ∈ (join P L).val, h e) =
      (∏ e ∈ P.val.val, h e) * ∏ i ∈ L.val, h (i,i) := by
  have hd : Disjoint P.val.val L.val.diag := by
    apply Finset.disjoint_left.mpr
    intro e he hl
    exact P.property e he (Finset.mem_diag.mp hl).2
  dsimp only [join]
  rw [Finset.prod_union hd, Finset.prod_diag]

lemma loop_sum (h : I × I → ℝ) :
    (∑ M : Matching I I, ∏ e ∈ M.val, h e) =
      ∑ P : OffMatching I, (∏ e ∈ P.val.val, h e) *
        ∏ i ∈ available P, (1+h (i,i)) := by
  rw [← Equiv.sum_comp splitEquiv.symm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro P _
  simp only [splitEquiv, Equiv.coe_fn_symm_mk, join_product]
  rw [← Finset.mul_sum, Finset.prod_one_add]
  congr 1
  apply Finset.sum_bij (fun L _ => L.val)
  · intro L _; exact Finset.mem_powerset.mpr L.property
  · intro L _ N _ h; exact Subtype.ext h
  · intro L hL; exact ⟨⟨L, Finset.mem_powerset.mp hL⟩, Finset.mem_univ _, rfl⟩
  · intro L _; rfl

lemma endpoint_product_le (P : OffMatching I) (s : I → ℝ) (hs : ∀ i, 1 ≤ s i)
    (f : I × I → I) (hf : Set.InjOn f ↑P.val.val)
    (hav : Disjoint (available P) (P.val.val.image f)) :
    (∏ i ∈ available P, s i) * (∏ e ∈ P.val.val, s (f e)) ≤ ∏ i, s i := by
  rw [← Finset.prod_image hf, ← Finset.prod_union hav]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
  · intro i _; exact le_trans (by norm_num) (hs i)
  · intro i _ _; exact hs i

lemma endpoint_compensation (P : OffMatching I) (s : I → ℝ) (hs : ∀ i, 1 ≤ s i) :
    (∏ i ∈ available P, s i ^ 2) *
      (∏ e ∈ P.val.val, s e.1 * s e.2) ≤ ∏ i, s i ^ 2 := by
  have hf : Set.InjOn (Prod.fst : I × I → I) (P.val.val : Set (I × I)) := by
    intro ⟨i,j⟩ hij ⟨k,l⟩ hkl he
    dsimp only at he
    subst k
    congr 1
    exact P.val.property.1 _ _ _ hij hkl
  have hg : Set.InjOn (Prod.snd : I × I → I) (P.val.val : Set (I × I)) := by
    intro ⟨i,j⟩ hij ⟨k,l⟩ hkl he
    dsimp only at he
    subst l
    congr 1
    exact P.val.property.2 _ _ _ hij hkl
  have ha : Disjoint (available P) (P.val.val.image Prod.fst) := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨e, hmem, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hi).2.1 e.2 hmem
  have hb : Disjoint (available P) (P.val.val.image Prod.snd) := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨e, hmem, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hi).2.2 e.1 hmem
  have hn : ∀ i, 0 ≤ s i := fun i => le_trans zero_le_one (hs i)
  have h := mul_le_mul (endpoint_product_le P s hs Prod.fst hf ha)
    (endpoint_product_le P s hs Prod.snd hg hb)
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hn i))
      (Finset.prod_nonneg (fun e _ => hn e.2)))
    (Finset.prod_nonneg (fun i _ => hn i))
  simp only [Finset.prod_pow, Finset.prod_mul_distrib]
  nlinarith [h]

lemma normalized_term_bound (P : OffMatching I) (h : I × I → ℝ)
    (hh : ∀ e, 0 ≤ h e) (s : I → ℝ) (hs : ∀ i, 1 ≤ s i) :
    (∏ e ∈ P.val.val, h e) * (∏ i ∈ available P, s i ^ 2) ≤
      (∏ i, s i ^ 2) * (∏ e ∈ P.val.val, h e / (s e.1 * s e.2)) := by
  have hs0 : ∀ i, 0 < s i := fun i => lt_of_lt_of_le zero_lt_one (hs i)
  have hd : 0 < ∏ e ∈ P.val.val, s e.1 * s e.2 :=
    Finset.prod_pos (fun e _ => mul_pos (hs0 _) (hs0 _))
  rw [Finset.prod_div_distrib, ← mul_div_assoc, le_div_iff₀ hd]
  have hc := mul_le_mul_of_nonneg_left (endpoint_compensation P s hs)
    (Finset.prod_nonneg (s := P.val.val) (fun e _ => hh e))
  nlinarith [hc]

noncomputable def leftChoice (P : OffMatching I) (i : I) : Option I :=
  if h : ∃ j, (i,j) ∈ P.val.val then some h.choose else none

lemma leftChoice_eq_some (P : OffMatching I) (i j : I) :
    leftChoice P i = some j ↔ (i,j) ∈ P.val.val := by
  unfold leftChoice
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hj; exact P.val.property.1 _ _ _ h.choose_spec hj
  · simp only [false_iff]
    exact fun hj => h ⟨j,hj⟩

lemma leftChoice_injective : Function.Injective (leftChoice (I := I)) := by
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  ext ⟨i,j⟩
  rw [← leftChoice_eq_some, ← leftChoice_eq_some, he]

noncomputable def rowWeight (w : I × I → ℝ) (i : I) : Option I → ℝ
  | none => 1
  | some j => if i ≠ j then w (i,j) else 0

lemma row_product (w : I × I → ℝ) (P : OffMatching I) :
    (∏ i, rowWeight w i (leftChoice P i)) = ∏ e ∈ P.val.val, w e := by
  rw [← Finset.prod_fiberwise (g := Prod.fst)]
  apply Finset.prod_congr rfl
  intro i _
  unfold leftChoice
  split_ifs with h
  · have hf : P.val.val.filter (fun e => e.1 = i) = {(i,h.choose)} := by
      ext ⟨j,k⟩
      simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨he,rfl⟩
        exact ⟨rfl, P.val.property.1 _ _ _ he h.choose_spec⟩
      · rintro ⟨rfl,rfl⟩; exact ⟨h.choose_spec,rfl⟩
    rw [hf, Finset.prod_singleton]
    exact ite_eq_left (P.property _ h.choose_spec)
  · have hf : P.val.val.filter (fun e => e.1 = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ⟨j,k⟩ he
      have hm := Finset.mem_filter.mp he
      have hj : j = i := hm.2
      subst j
      exact h ⟨k,hm.1⟩
    rw [hf, Finset.prod_empty]
    rfl

lemma off_sum_le_rows (w : I × I → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ P : OffMatching I, ∏ e ∈ P.val.val, w e) ≤
      ∏ i, (1 + ∑ j ∈ Finset.univ.erase i, w (i,j)) := by
  have hrow (i : I) : (∑ o : Option I, rowWeight w i o) =
      1 + ∑ j ∈ Finset.univ.erase i, w (i,j) := by
    rw [Fintype.sum_option]
    dsimp only [rowWeight]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true, ne_comm]
    · intro j _; rfl
  simp_rw [← hrow]
  rw [Fintype.prod_sum]
  let t := Finset.univ.image (leftChoice (I := I))
  have he : (∑ P : OffMatching I, ∏ e ∈ P.val.val, w e) =
      ∑ f ∈ t, ∏ i, rowWeight w i (f i) := by
    dsimp only [t]
    rw [Finset.sum_image (fun _ _ _ _ he => leftChoice_injective he)]
    apply Finset.sum_congr rfl
    intro P _; exact (row_product w P).symm
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro f _ _
  apply Finset.prod_nonneg
  intro i _
  cases f i <;> simp only [rowWeight]
  · norm_num
  · split_ifs <;> first | exact hw _ | exact le_rfl

lemma self_matching_bound (h : I × I → ℝ) (hh : ∀ e, 0 ≤ h e) :
    (∑ M : Matching I I, ∏ e ∈ M.val, h e) ≤
      (∏ i, (1+h (i,i))) *
        ∏ i, (1 + ∑ j ∈ Finset.univ.erase i,
          h (i,j) / (Real.sqrt (1+h (i,i)) * Real.sqrt (1+h (j,j)))) := by
  let s := fun i => Real.sqrt (1+h (i,i))
  have hs : ∀ i, 1 ≤ s i := by
    intro i
    dsimp only [s]
    exact Real.one_le_sqrt.mpr (by linarith [hh (i,i)])
  have he : ∀ i, s i ^ 2 = 1+h (i,i) := by
    intro i
    exact Real.sq_sqrt (by linarith [hh (i,i)])
  rw [loop_sum]
  calc
    _ ≤ ∑ P : OffMatching I, (∏ i, s i ^ 2) *
        (∏ e ∈ P.val.val, h e / (s e.1 * s e.2)) := by
      apply Finset.sum_le_sum
      intro P _
      simpa only [he] using normalized_term_bound P h hh s hs
    _ = (∏ i, s i ^ 2) *
        ∑ P : OffMatching I, ∏ e ∈ P.val.val, h e / (s e.1*s e.2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (∏ i, s i ^ 2) * ∏ i,
        (1 + ∑ j ∈ Finset.univ.erase i, h (i,j) / (s i * s j)) := by
      apply mul_le_mul_of_nonneg_left
      · exact off_sum_le_rows _ (fun e => div_nonneg (hh e)
          (mul_nonneg (le_trans zero_le_one (hs e.1)) (le_trans zero_le_one (hs e.2))))
      · exact Finset.prod_nonneg (fun i _ => sq_nonneg (s i))
    _ = _ := by simp only [he, s]

end MatchingSelf

end OAI
