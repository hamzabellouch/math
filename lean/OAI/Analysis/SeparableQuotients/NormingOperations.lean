import OAI.Analysis.SeparableQuotients.NormingFamilies

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.reciprocal_summable (f : Family) :
    Summable (fun n => 1 / (Parameters.m f.s n : ℝ)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (Parameters.reciprocal_le_theta f.s_ge_two) (Parameters.hasSum_theta f.s_ge_two).summable

lemma TypeII.coefficient_le_one {f : Family} (e : TypeII f) (b : Fin e.length) :
    |(e.coefficient b : ℝ)| ≤ 1 := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  have hb : |(e.coefficient b : ℝ)| ^ f.q ≤ 1 :=
    (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (abs_nonneg (e.coefficient i : ℝ)) f.q)
      (Finset.mem_univ b)).trans e.bound
  by_contra h
  have ht := Real.one_lt_rpow (lt_of_not_ge h) hq
  exact (not_lt_of_ge hb) ht

lemma TypeII.hit_weight_injective {f : Family} (e : TypeII f) (a : Γ) :
    Set.InjOn (fun b : Fin e.length => (e.path b).raw.weight ((e.path b).hitIndex a))
      {b | restrict ((e.crop b).set f) (e.path b).value a ≠ 0} := by
  intro b hb c hc heq
  by_contra hbc
  have hb' := (e.path b).hit_weight_active (e.crop b) a hb
  have hc' := (e.path c).hit_weight_active (e.crop c) a hc
  dsimp only at heq
  rw [heq] at hb'
  exact Finset.disjoint_left.mp (e.disjoint_active hbc) hb' hc'

lemma TypeII.coefficient_bound {f : Family} (e : TypeII f)
    (h : ∀ b i j a, |(((e.path b).piece i).child j a : ℝ)| ≤ 1) (a : Γ) :
    |(e.value a : ℝ)| < 1/8 := by
  classical
  let active : Finset (Fin e.length) := Finset.univ.filter
    (fun b => restrict ((e.crop b).set f) (e.path b).value a ≠ 0)
  let j : Fin e.length → ℕ := fun b =>
    (e.path b).raw.weight ((e.path b).hitIndex a)
  have jpos : ∀ b, 1 ≤ j b := fun b => (e.path b).valid.weight_pos _
    ((e.path b).hitIndex a).isLt
  have jinj : Set.InjOn (fun b => j b - 1) active := by
    intro b hb c hc heq
    apply e.hit_weight_injective a (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
    change j b = j c
    dsimp only at heq
    have := jpos b
    have := jpos c
    omega
  have hterm : ∀ b ∈ active,
      |(e.coefficient b : ℝ) * (restrict ((e.crop b).set f) (e.path b).value a : ℝ)|
        ≤ 1 / (Parameters.m f.s (j b - 1) : ℝ) := by
    intro b hb
    have hAc : a ∈ (e.crop b).set f := by
      by_contra hn
      have := (Finset.mem_filter.mp hb).2
      simp [hn] at this
    have hv : |((e.path b).raw.piece ((e.path b).hitIndex a) a : ℝ)| ≤
        1 / (f.m (j b) : ℝ) := by
      rw [← (e.path b).value_eq]
      have hh := ((e.path b).piece ((e.path b).hitIndex a)).coefficient_bound
        (h b ((e.path b).hitIndex a)) a
      simpa only [(e.path b).weight_eq] using hh
    rw [restrict_apply, ite_eq_left hAc, (e.path b).value_at_hit, abs_mul]
    exact (mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (abs_nonneg _)).trans
      (by simpa only [one_mul, Family.m] using hv)
  have hsum : (e.value a : ℝ) = ∑ b ∈ active,
      (e.coefficient b : ℝ) * (restrict ((e.crop b).set f) (e.path b).value a : ℝ) := by
    simp only [TypeII.value, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Rat.cast_sum,
      Rat.cast_mul]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b _ hb
    have hz : restrict ((e.crop b).set f) (e.path b).value a = 0 := by
      simpa [active] using hb
    simp [hz]
  rw [hsum]
  calc
    |∑ b ∈ active, (e.coefficient b : ℝ) *
        (restrict ((e.crop b).set f) (e.path b).value a : ℝ)|
      ≤ ∑ b ∈ active, |(e.coefficient b : ℝ) *
        (restrict ((e.crop b).set f) (e.path b).value a : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ active, 1 / (Parameters.m f.s (j b - 1) : ℝ) := Finset.sum_le_sum hterm
    _ = ∑ n ∈ active.image (fun b => j b-1), 1 / (Parameters.m f.s n : ℝ) := by
      rw [Finset.sum_image]
      exact fun b hb c hc hbc => jinj hb hc hbc
    _ ≤ ∑' n, 1 / (Parameters.m f.s n : ℝ) :=
      f.reciprocal_summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ < 1/8 := Parameters.reciprocal_sum_small f.s_ge_two

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma stage_coefficient_bound {base : Set Array} (f : Family)
    (hbase : ∀ x ∈ base, ∀ a, |(x a : ℝ)| ≤ 1) :
    ∀ n x, x ∈ stage base f n → ∀ a, |(x a : ℝ)| ≤ 1 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx a
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx a
    · exact (e.coefficient_bound (fun i => ih _ (he i)) a).trans (by
        have hm : (1 : ℝ) ≤ f.m e.weight := by exact_mod_cast f.m_pos e.weight
        exact (div_le_one (lt_of_lt_of_le (by norm_num) hm)).mpr hm)
    · exact le_trans (le_of_lt (e.coefficient_bound
        (fun b i j => ih _ (he b i j)) a)) (by norm_num)

lemma pureBase_coefficient_bound (k : ℕ) (x : Array) (hx : x ∈ pureBase k) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  rcases hx with rfl | ⟨b, _, rfl | rfl⟩
  · simp
  all_goals by_cases hab : a = b <;> simp [hab]

lemma pure_coefficient_bound (k : ℕ) (x : Array) (hx : x ∈ Pure k) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact stage_coefficient_bound (.pure k) (pureBase_coefficient_bound k) n x hn a

lemma full_coefficient_bound (x : Array) (hx : x ∈ Full) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_coefficient_bound .mixed ?_ n x hn a
  intro y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact pure_coefficient_bound k y hk

lemma restrict_support_subset (A : Set Γ) (x : Array) :
    (restrict A x).support ⊆ x.support := Finset.filter_subset _ _

lemma restrict_zero (A : Set Γ) : restrict A 0 = 0 := by ext a; simp

lemma restrict_smul (A : Set Γ) (c : ℚ) (x : Array) :
    restrict A (c • x) = c • restrict A x := by
  ext a
  by_cases h : a ∈ A <;> simp [h]

lemma restrict_sum {ι : Type*} (A : Set Γ) (s : Finset ι) (x : ι → Array) :
    restrict A (∑ i ∈ s, x i) = ∑ i ∈ s, restrict A (x i) := Finsupp.filter_sum _ _

lemma restrict_restrict (A B : Set Γ) (x : Array) :
    restrict A (restrict B x) = restrict (A ∩ B) x := by
  ext a
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

def Crop.inter (A B : Crop) : Crop :=
  ⟨A.ordinal ∩ B.ordinal, A.ordinal_convex.inter B.ordinal_convex,
    A.colors ∩ B.colors, A.colors_convex.inter B.colors_convex⟩

@[simp] lemma Crop.inter_set (A B : Crop) (f : Family) :
    (A.inter B).set f = A.set f ∩ B.set f := by
  cases f <;> ext a <;> simp [Crop.set, Crop.inter, and_assoc, and_left_comm, and_comm]

lemma Successive.restrict {f : Family} {x y : Array} (h : Successive f x y) (A : Set Γ) :
    Successive f (restrict A x) (restrict A y) := by
  intro a ha b hb
  exact h a (restrict_support_subset A x ha) b (restrict_support_subset A y hb)

lemma TypeII.active_crop_subset {f : Family} (P : FinitePath f) (A B : Crop) :
    P.active (A.inter B) ⊆ P.active B := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro hz
  have hn := (Finset.mem_filter.mp hi).2
  apply hn
  rw [Crop.inter_set, ← restrict_restrict, hz, restrict_zero]

/-- Crops of Type II expressions retain the original paths and coding. -/
def TypeII.cropped {f : Family} (e : TypeII f) (A : Crop) : TypeII f where
  length := e.length
  path := e.path
  crop b := A.inter (e.crop b)
  coefficient := e.coefficient
  bound := e.bound
  disjoint_active := fun _b _c hbc => (e.disjoint_active hbc).mono
    (TypeII.active_crop_subset _ _ _) (TypeII.active_crop_subset _ _ _)

lemma TypeII.cropped_value {f : Family} (e : TypeII f) (A : Crop) :
    (e.cropped A).value = restrict (A.set f) e.value := by
  simp only [TypeII.value, TypeII.cropped, restrict_sum, restrict_smul,
    Crop.inter_set, restrict_restrict]
  rfl

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

/-- The crop operation discards zero children in order. -/
lemma TypeI.crop_cases {f : Family} (e : TypeI f) (A : Set Γ) :
    restrict A e.value = 0 ∨ ∃ d : TypeI f,
      d.weight = e.weight ∧ d.value = restrict A e.value ∧
      ∀ i, ∃ j, d.child i = restrict A (e.child j) := by
  let S : Finset (Fin e.length) := Finset.univ.filter (fun i => restrict A (e.child i) ≠ 0)
  have hsum : ∑ i ∈ S, restrict A (e.child i) = ∑ i, restrict A (e.child i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  by_cases hS : S.Nonempty
  · right
    let idx : Fin S.card → Fin e.length := fun i => (S.orderIsoOfFin rfl i).val
    have hidx : StrictMono idx := (S.orderEmbOfFin rfl).strictMono
    have hiS : ∀ i, idx i ∈ S := fun i => (S.orderIsoOfFin rfl i).property
    let d : TypeI f :=
      { weight := e.weight
        weight_pos := e.weight_pos
        length := S.card
        length_pos := Finset.card_pos.mpr hS
        length_le := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using e.length_le)
        child := fun i => restrict A (e.child (idx i))
        child_nonzero := fun i => (Finset.mem_filter.mp (hiS i)).2
        successive := fun i j hij => (e.successive _ _ (hidx hij)).restrict A }
    refine ⟨d, rfl, ?_, fun i => ⟨idx i, rfl⟩⟩
    have hsum' : ∑ i : Fin S.card, restrict A (e.child (idx i)) =
        ∑ i ∈ S, restrict A (e.child i) := by
      calc
        _ = ∑ i : S, restrict A (e.child i) :=
          (S.orderIsoOfFin rfl).toEquiv.sum_comp _
        _ = _ := (Finset.sum_subtype S (fun _ => Iff.rfl) (fun i => restrict A (e.child i))).symm
    simp only [d, TypeI.value, restrict_smul, restrict_sum, hsum', hsum]
  · left
    have hz : ∀ i, restrict A (e.child i) = 0 := by
      intro i
      by_contra hi
      exact hS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simp only [TypeI.value, restrict_smul, restrict_sum, hz, Finset.sum_const_zero, smul_zero]

lemma stage_zero {base : Set Array} (f : Family) (h0 : (0 : Array) ∈ base) (n : ℕ) :
    (0 : Array) ∈ stage base f n := stage_mono base f (Nat.zero_le n) h0

lemma stage_crop {base : Set Array} (f : Family) (h0 : (0 : Array) ∈ base)
    (hbase : ∀ (A : Crop) x, x ∈ base → restrict (A.set f) x ∈ base) :
    ∀ n (A : Crop) x, x ∈ stage base f n → restrict (A.set f) x ∈ stage base f n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro A x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact Or.inl (Or.inl (ih A x hx))
    · rcases e.crop_cases (A.set f) with hz | ⟨d, _, hd, hchild⟩
      · rw [hz]
        exact stage_zero f h0 (n+1)
      · apply Or.inl ∘ Or.inr
        refine ⟨d, hd, ?_⟩
        intro i
        obtain ⟨j, hj⟩ := hchild i
        rw [hj]
        exact ih A _ (he j)
    · right
      exact ⟨e.cropped A, e.cropped_value A, he⟩

lemma pureBase_zero (k : ℕ) : (0 : Array) ∈ pureBase k := Or.inl rfl

lemma pureBase_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ pureBase k) :
    restrict (A.set (.pure k)) x ∈ pureBase k := by
  rcases hx with rfl | ⟨a, ha, rfl | rfl⟩
  · exact Or.inl (restrict_zero _)
  all_goals
    by_cases hA : a ∈ A.set (.pure k)
    · rw [restrict, Finsupp.filter_single_of_pos _ hA]
      exact Or.inr ⟨a, ha, by first | exact Or.inl rfl | exact Or.inr rfl⟩
    · rw [restrict, Finsupp.filter_single_of_neg _ hA]
      exact pureBase_zero k

lemma pure_zero (k : ℕ) : (0 : Array) ∈ Pure k := Set.mem_iUnion.mpr ⟨0, pureBase_zero k⟩

lemma pure_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ Pure k) :
    restrict (A.set (.pure k)) x ∈ Pure k := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n,
    stage_crop (.pure k) (pureBase_zero k) (pureBase_crop k) n A x hn⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma TypeI.zero_at {f : Family} (e : TypeI f) (a : Γ)
    (h : ∀ i, e.child i a = 0) : e.value a = 0 := by
  simp [TypeI.value, h]

lemma FinitePath.zero_at {f : Family} (P : FinitePath f) (a : Γ)
    (h : ∀ i j, (P.piece i).child j a = 0) : P.value a = 0 := by
  rw [FinitePath.value, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [← P.value_eq]
  exact (P.piece i).zero_at a (h i)

lemma TypeII.zero_at {f : Family} (e : TypeII f) (a : Γ)
    (h : ∀ b i j, ((e.path b).piece i).child j a = 0) : e.value a = 0 := by
  simp only [TypeII.value, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    restrict_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [(e.path b).zero_at a (h b)]
  simp

lemma stage_vanish {base : Set Array} (f : Family) (a : Γ)
    (hbase : ∀ x ∈ base, x a = 0) :
    ∀ n x, x ∈ stage base f n → x a = 0 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · exact e.zero_at a (fun i => ih _ (he i))
    · exact e.zero_at a (fun b i j => ih _ (he b i j))

lemma pure_vanish (k : ℕ) (x : Array) (hx : x ∈ Pure k) (a : Γ)
    (ha : Colors.color a ≠ k) : x a = 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_vanish (.pure k) a ?_ n x hn
  intro y hy
  rcases hy with rfl | ⟨b, hb, rfl | rfl⟩
  · rfl
  all_goals
    have hab : a ≠ b := by intro h; subst b; exact ha hb
    simp [hab]

lemma pure_mixed_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ Pure k) :
    restrict (A.set .mixed) x =
      if k ∈ A.colors then restrict (A.set (.pure k)) x else 0 := by
  ext a
  by_cases hcol : Colors.color a = k
  · by_cases hk : k ∈ A.colors <;> simp [Crop.set, hcol, hk]
  · have hz := pure_vanish k x hx a hcol
    by_cases hk : k ∈ A.colors <;> simp [Crop.set, hk, hz]

lemma full_zero : (0 : Array) ∈ Full := pure_subset_full 0 (pure_zero 0)

lemma full_crop (A : Crop) (x : Array) (hx : x ∈ Full) :
    restrict (A.set .mixed) x ∈ Full := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨n, stage_crop .mixed ?_ ?_ n A x hn⟩
  · exact Set.mem_iUnion.mpr ⟨0, pure_zero 0⟩
  · intro B y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [pure_mixed_crop k B y hk]
    split_ifs
    · exact pure_crop k B y hk
    · exact pure_zero k

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma Successive.neg {f : Family} {x y : Array} (h : Successive f x y) :
    Successive f (-x) (-y) := by
  intro a ha b hb
  exact h a (by simpa using ha) b (by simpa using hb)

def TypeI.neg {f : Family} (e : TypeI f) : TypeI f where
  weight := e.weight
  weight_pos := e.weight_pos
  length := e.length
  length_pos := e.length_pos
  length_le := e.length_le
  child i := -e.child i
  child_nonzero i := neg_ne_zero.mpr (e.child_nonzero i)
  successive i j hij := (e.successive i j hij).neg

@[simp] lemma TypeI.neg_value {f : Family} (e : TypeI f) : e.neg.value = -e.value := by
  simp [TypeI.value, TypeI.neg, Finset.sum_neg_distrib]
  rfl

def TypeII.neg {f : Family} (e : TypeII f) : TypeII f where
  length := e.length
  path := e.path
  crop := e.crop
  coefficient b := -e.coefficient b
  bound := by simpa using e.bound
  disjoint_active := e.disjoint_active

@[simp] lemma TypeII.neg_value {f : Family} (e : TypeII f) : e.neg.value = -e.value := by
  simp [TypeII.value, TypeII.neg, Finset.sum_neg_distrib]
  rfl

lemma stage_neg {base : Set Array} (f : Family) (hbase : ∀ x ∈ base, -x ∈ base) :
    ∀ n x, x ∈ stage base f n → -x ∈ stage base f n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact Or.inl (Or.inl (ih x hx))
    · exact Or.inl (Or.inr ⟨e.neg, e.neg_value, fun i => ih _ (he i)⟩)
    · exact Or.inr ⟨e.neg, e.neg_value, he⟩

lemma pure_neg (k : ℕ) (x : Array) (hx : x ∈ Pure k) : -x ∈ Pure k := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨n, stage_neg (.pure k) ?_ n x hn⟩
  intro y hy
  rcases hy with rfl | ⟨a, ha, rfl | rfl⟩
  · exact Or.inl neg_zero
  · exact Or.inr ⟨a, ha, Or.inr (by simp)⟩
  · exact Or.inr ⟨a, ha, Or.inl (by simp)⟩

lemma full_neg (x : Array) (hx : x ∈ Full) : -x ∈ Full := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨n, stage_neg .mixed ?_ n x hn⟩
  intro y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨k, pure_neg k y hk⟩

end SeparableQuotient.Norming

end

end OAI
