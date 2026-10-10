import OAI.Combinatorics.ListHadwiger.Fractional

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

lemma Dual.extend {G : SimpleGraph V} {S : Set V} [DecidablePred (· ∈ S)] {w : S → ℝ}
    (h : Dual (G.induce S) w) :
    Dual G (fun v => if hv : v ∈ S then w ⟨v,hv⟩ else 0) := by
  classical
  refine ⟨?_,?_⟩
  · intro v
    dsimp only
    split_ifs
    · exact h.1 _
    · exact le_rfl
  · intro I hI
    let J : Finset S := Finset.univ.filter fun v => v.val ∈ I
    have hJ : Stable (G.induce S) J := by
      intro v hv u hu hadj
      exact hI _ (Finset.mem_filter.mp hv).2 _ (Finset.mem_filter.mp hu).2 hadj
    have hs : (∑ v ∈ I, if hv : v ∈ S then w ⟨v,hv⟩ else 0) = ∑ v ∈ J, w v := by
      calc
        _ = ∑ v ∈ I.filter (· ∈ S), if hv : v ∈ S then w ⟨v,hv⟩ else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : v ∈ S <;> simp [hv]
        _ = _ := by
          apply Finset.sum_bij (fun v hv => (⟨v,(Finset.mem_filter.mp hv).2⟩ : S))
          · intro v hv
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).1⟩
          · intro v hv u hu he
            exact congrArg Subtype.val he
          · intro v hv
            exact ⟨v.val,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,v.property⟩,rfl⟩
          · intro v hv
            simp only [dite_eq_left (Finset.mem_filter.mp hv).2]
    rw [hs]
    exact h.2 J hJ

theorem induced_duality (G : SimpleGraph V) (S : Finset V) :
    ∃ w : V → ℝ, Dual G w ∧ (∀ v ∉ S, w v = 0) ∧
      (∑ v ∈ S, w v) = number (G.induce (S : Set V)) := by
  classical
  obtain ⟨w,hw,heq⟩ := duality (G.induce (S : Set V))
  refine ⟨fun v => if hv : v ∈ S then w ⟨v,hv⟩ else 0,hw.extend,?_,?_⟩
  · intro v hv
    simp [hv]
  · rw [← heq]
    calc
      _ = ∑ v : (S : Set V), (if hv : v.val ∈ S then w ⟨v.val,hv⟩ else 0) :=
        (Finset.sum_coe_sort S _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        split_ifs with hv
        · rfl
        · exact (hv v.property).elim

lemma Dual.restrict_sum {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w)
    (S : Finset V) : (∑ v ∈ S, w v) ≤ number (G.induce (S : Set V)) := by
  classical
  obtain ⟨μ,hμ,hcost⟩ := optimum_exists (G.induce (S : Set V))
  have h := weak_duality hμ (hw.comap Subtype.val Subtype.val_injective)
  rw [hcost] at h
  have he : (∑ v : (S : Set V), w v.val) = ∑ v ∈ S, w v :=
    (Finset.sum_subtype S (fun v => Iff.rfl) w).symm
  rw [he] at h
  exact h

lemma induced_number_le (G : SimpleGraph V) (S T : Finset V) :
    number (G.induce (S : Set V)) ≤ number (G.induce (T : Set V)) + (S \ T).card := by
  classical
  obtain ⟨w,hw,hzero,hmax⟩ := induced_duality G S
  have hsplit : (∑ v ∈ S, w v) = (∑ v ∈ S ∩ T, w v) + ∑ v ∈ S \ T, w v := by
    have hd : Disjoint (S ∩ T) (S \ T) := by
      apply Finset.disjoint_left.mpr
      intro v hv ht
      exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mp hv).2
    rw [← Finset.sum_union hd]
    congr 1
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hT : (∑ v ∈ S ∩ T, w v) ≤ number (G.induce (T : Set V)) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun v _ _ => hw.1 v)).trans (hw.restrict_sum T)
  have hD : (∑ v ∈ S \ T, w v) ≤ (S \ T).card := by
    calc
      _ ≤ ∑ _v ∈ S \ T, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hw.le_one v)
      _ = _ := by simp
  rw [← hmax,hsplit]
  linarith

lemma induced_number_abs_sub_le (G : SimpleGraph V) (S T : Finset V) :
    |number (G.induce (S : Set V)) - number (G.induce (T : Set V))| ≤
      (S \ T).card + (T \ S).card := by
  have hST := induced_number_le G S T
  have hTS := induced_number_le G T S
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (S \ T).card,
    Nat.cast_nonneg (α := ℝ) (T \ S).card]

end LinearListHadwiger.Fractional

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

noncomputable def productMass (μ : ι → Ω → ℝ) (x : ι → Ω) : ℝ := ∏ i, μ i (x i)
noncomputable def expectation (μ f : Ω → ℝ) : ℝ := ∑ ω, μ ω * f ω
noncomputable def probability (μ : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if A ω then μ ω else 0

lemma productMass_nonneg {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι] {μ : ι → Ω → ℝ} (h : ∀ i ω, 0 ≤ μ i ω) (x : ι → Ω) :
    0 ≤ productMass μ x := Finset.prod_nonneg (fun i _ => h i _)

lemma productMass_sum {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1) :
    ∑ x, productMass μ x = 1 := by
  classical
  change (∑ x : ι → Ω, ∏ i, μ i (x i)) = 1
  rw [← Fintype.prod_sum]
  simp [h]

lemma expectation_product (μ f : ι → Ω → ℝ) :
    expectation (productMass μ) (fun x => ∏ i, f i (x i)) =
      ∏ i, expectation (μ i) (f i) := by
  classical
  simp only [expectation,productMass,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (ι := ι) (κ := fun _ => Ω) (fun i a => μ i a * f i a)).symm

lemma expectation_coordinate {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1)
    (i : ι) (f : Ω → ℝ) :
    expectation (productMass μ) (fun x => f (x i)) = expectation (μ i) f := by
  classical
  have he (x : ι → Ω) : (∏ j : ι, if j = i then f (x j) else 1) = f (x i) := by simp
  calc
    _ = expectation (productMass μ) (fun x => ∏ j, if j = i then f (x j) else 1) := by
      congr 1
      funext x
      exact (he x).symm
    _ = ∏ j, expectation (μ j) (fun ω => if j = i then f ω else 1) :=
      expectation_product μ (fun j ω => if j = i then f ω else 1)
    _ = expectation (μ i) f := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji
        simp [expectation,hji,h]
      · simp

lemma expectation_pair {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1)
    {i j : ι} (hij : i ≠ j) (f g : Ω → ℝ) :
    expectation (productMass μ) (fun x => f (x i) * g (x j)) =
      expectation (μ i) f * expectation (μ j) g := by
  classical
  have he (x : ι → Ω) :
      (∏ k : ι, (if k = i then f (x k) else 1) * (if k = j then g (x k) else 1)) =
        f (x i) * g (x j) := by rw [Finset.prod_mul_distrib]; simp
  calc
    _ = expectation (productMass μ) (fun x => ∏ k,
        (if k = i then f (x k) else 1) * (if k = j then g (x k) else 1)) := by
      congr 1
      funext x
      exact (he x).symm
    _ = ∏ k, expectation (μ k) (fun ω =>
        (if k = i then f ω else 1) * (if k = j then g ω else 1)) := expectation_product μ
          (fun k ω => (if k = i then f ω else 1) * (if k = j then g ω else 1))
    _ = ∏ k, (if k = i then expectation (μ i) f else 1) *
        (if k = j then expectation (μ j) g else 1) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k; simp [hij,expectation]
      · by_cases hkj : k = j
        · subst k; simp [hki,expectation]
        · simp [hki,hkj,expectation,h]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma expectation_nonneg {μ f : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ expectation μ f := Finset.sum_nonneg fun ω _ => mul_nonneg (hμ ω) (hf ω)

lemma expectation_mono {μ f g : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hfg : ∀ ω, f ω ≤ g ω) :
    expectation μ f ≤ expectation μ g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hμ ω)

lemma expectation_sum {κ : Type} (s : Finset κ) (μ : Ω → ℝ) (f : κ → Ω → ℝ) :
    expectation μ (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, expectation μ (f k) := by
  simp only [expectation,Finset.mul_sum]
  exact Finset.sum_comm

lemma probability_eq_expectation (μ : Ω → ℝ) (A : Ω → Prop) [DecidablePred A] :
    probability μ A = expectation μ (fun ω => if A ω then 1 else 0) := by
  classical
  simp only [probability,expectation]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma probability_nonneg {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (A : Ω → Prop) :
    0 ≤ probability μ A := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs; exact hμ ω; exact le_rfl

lemma probability_mono {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : probability μ A ≤ probability μ B := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp [hA,hAB ω hA]
  · simp only [hA,ite_false]
    split_ifs; exact hμ ω; exact le_rfl

lemma probability_coordinate {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1)
    (i : ι) (A : Ω → Prop) :
    probability (productMass μ) (fun x => A (x i)) = probability (μ i) A := by
  classical
  simp_rw [probability_eq_expectation]
  exact expectation_coordinate h i (fun ω => if A ω then (1 : ℝ) else 0)

lemma probability_union_le {κ : Type} [Fintype κ] {μ : Ω → ℝ}
    (hμ : ∀ ω, 0 ≤ μ ω) (A : κ → Ω → Prop) :
    probability μ (fun ω => ∃ k, A k ω) ≤ ∑ k, probability μ (A k) := by
  classical
  simp only [probability]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : ∃ k, A k ω
  · obtain ⟨k,hk⟩ := hA
    rw [ite_eq_left ⟨k,hk⟩]
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset κ))
        (f := fun k => if A k ω then μ ω else 0)
        (fun k _ => by split_ifs; exact hμ ω; exact le_rfl) (Finset.mem_univ k)
    simpa only [ite_eq_left hk] using hh
  · simp only [ite_eq_right hA]
    exact Finset.sum_nonneg (fun k _ => by split_ifs; exact hμ ω; exact le_rfl)

lemma probability_or_le {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) :
    probability μ (fun ω => A ω ∨ B ω) ≤ probability μ A + probability μ B := by
  classical
  simp only [probability,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA,hB,hμ ω]

lemma markov {μ f : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    probability μ (fun ω => a ≤ f ω) ≤ expectation μ f / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  simp only [probability,Finset.sum_mul,expectation]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ f ω
  · simp only [ite_eq_left h]
    exact mul_le_mul_of_nonneg_left h (hμ ω)
  · simp only [ite_eq_right h,zero_mul]
    exact mul_nonneg (hμ ω) (hf ω)

lemma exists_positive_avoiding {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hs : ∑ ω, μ ω = 1) {A : Ω → Prop} (hA : probability μ A < 1) :
    ∃ ω, 0 < μ ω ∧ ¬A ω := by
  classical
  by_contra hn
  push Not at hn
  have he : probability μ A = 1 := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : 0 < μ ω
    · simp only [ite_eq_left (hn ω h)]
    · have hz : μ ω = 0 := le_antisymm (le_of_not_gt h) (hμ ω)
      simp [hz]
  linarith

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open scoped BigOperators
open Fractional
variable {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq ι] [DecidableEq V]

lemma expectation_const {μ : Ω → ℝ} (hs : ∑ ω, μ ω = 1) (c : ℝ) :
    expectation μ (fun _ => c) = c := by simp [expectation,← Finset.sum_mul,hs]

noncomputable def otherCopies (W : Ω → Finset V) (i : ι) (x : ι → Ω) : Finset V :=
  (Finset.univ.erase i).biUnion fun j => W (x j)

noncomputable def privateCopy (W : Ω → Finset V) (i : ι) (x : ι → Ω) : Finset V :=
  W (x i) \ otherCopies W i x

noncomputable def collision (W : Ω → Finset V) (φ : Ω → V → ℝ) (i : ι)
    (x : ι → Ω) : ℝ := ∑ j ∈ Finset.univ.erase i, ∑ v,
      φ (x i) v * (if v ∈ W (x j) then 1 else 0)

lemma collision_nonneg {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (W : Ω → Finset V) {φ : Ω → V → ℝ}
    (hφ : ∀ ω v, 0 ≤ φ ω v) (i : ι) (x : ι → Ω) : 0 ≤ collision W φ i x := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hφ]

lemma expectation_collision {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hs : ∑ ω, μ ω = 1)
    (W : Ω → Finset V) {φ : Ω → V → ℝ} (hφ : ∀ ω v, 0 ≤ φ ω v)
    (hφsum : ∀ ω, ∑ v, φ ω v ≤ 1) {p : ℝ} (hp : 0 ≤ p)
    (hmarg : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p) (i : ι) :
    expectation (productMass (fun _ : ι => μ)) (collision W φ i) ≤
      (Fintype.card ι - 1 : ℕ) * p := by
  classical
  unfold collision
  rw [expectation_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, p := by
      apply Finset.sum_le_sum
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      rw [expectation_sum]
      calc
        _ = ∑ v, expectation μ (fun ω => φ ω v) * probability μ (fun ω => v ∈ W ω) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [expectation_pair (μ := fun _ : ι => μ) (f := fun ω => φ ω v)
            (g := fun ω => if v ∈ W ω then 1 else 0) (fun _ => hs) hij,
            probability_eq_expectation]
        _ ≤ ∑ v, expectation μ (fun ω => φ ω v) * p := by
          apply Finset.sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_left (hmarg v) (expectation_nonneg hμ (fun ω => hφ ω v))
        _ = expectation μ (fun ω => ∑ v, φ ω v) * p := by
          rw [← Finset.sum_mul,expectation_sum]
        _ ≤ 1 * p := by
          apply mul_le_mul_of_nonneg_right _ hp
          exact (expectation_mono hμ hφsum).trans_eq (expectation_const hs 1)
        _ = p := one_mul p
    _ = _ := by simp

lemma sum_on_eq (S : Finset V) (f : V → ℝ) :
    (∑ v ∈ S, f v) = ∑ v, if v ∈ S then f v else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

lemma private_weight_loss {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (W : Ω → Finset V) {φ : Ω → V → ℝ}
    (hφ : ∀ ω v, 0 ≤ φ ω v) (i : ι) (x : ι → Ω) :
    (∑ v ∈ W (x i), φ (x i) v) ≤
      (∑ v ∈ privateCopy W i x, φ (x i) v) + collision W φ i x := by
  classical
  rw [sum_on_eq (W (x i)) (φ (x i)),
    sum_on_eq (privateCopy W i x) (φ (x i))]
  unfold collision
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i,
      φ (x i) v * (if v ∈ W (x j) then 1 else 0) := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> simp [hφ]
  by_cases hv : v ∈ W (x i)
  · simp only [ite_eq_left hv]
    by_cases hpr : v ∈ privateCopy W i x
    · simp only [ite_eq_left hpr]
      linarith
    · simp only [ite_eq_right hpr,zero_add]
      have hvO : v ∈ otherCopies W i x := by
        simpa only [privateCopy,Finset.mem_sdiff,hv,true_and,not_not] using hpr
      obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hvO
      have hh := Finset.single_le_sum
        (s := Finset.univ.erase i)
        (f := fun j => φ (x i) v * (if v ∈ W (x j) then 1 else 0))
        (fun j _ => by split_ifs <;> simp [hφ]) hj
      simpa only [ite_eq_left hvj,mul_one] using hh
  · simp only [ite_eq_right hv]
    have hc : 0 ≤ (if v ∈ privateCopy W i x then φ (x i) v else 0) := by
      split_ifs; exact hφ _ _; exact le_rfl
    linarith

lemma privateCopies_disjoint {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (W : Ω → Finset V) (x : ι → Ω) {i j : ι} (hij : i ≠ j) :
    Disjoint (privateCopy W i x) (privateCopy W j x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨hi,hni⟩ := Finset.mem_sdiff.mp hvi
  obtain ⟨hj,hnj⟩ := Finset.mem_sdiff.mp hvj
  apply hni
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩,hj⟩

theorem private_fractional_failure (G : SimpleGraph V) {μ : Ω → ℝ}
    (hμ : ∀ ω, 0 ≤ μ ω) (hs : ∑ ω, μ ω = 1) (W : Ω → Finset V)
    {r p δ : ℝ} (hr : 0 < r) (hp : 0 ≤ p)
    (hmarg : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p)
    (hhigh : probability μ (fun ω => number (G.induce (W ω : Set V)) ≤ r/5) ≤ δ) :
    probability (productMass (fun _ : ι => μ))
      (fun x => ∃ i, number (G.induce (privateCopy W i x : Set V)) ≤ r/8) ≤
        (Fintype.card ι : ℝ) * δ + 4 * Fintype.card ι * (Fintype.card ι - 1 : ℕ) * p := by
  classical
  choose w hw hz heq using (fun ω => induced_duality G (W ω))
  let a : Ω → ℝ := fun ω => number (G.induce (W ω : Set V))
  let φ : Ω → V → ℝ := fun ω v => if 0 < a ω then w ω v / a ω else 0
  have hφ : ∀ ω v, 0 ≤ φ ω v := by
    intro ω v
    dsimp [φ]
    split_ifs with h
    · exact div_nonneg ((hw ω).1 v) h.le
    · exact le_rfl
  have hwtotal (ω : Ω) : (∑ v, w ω v) = a ω := by
    change (∑ v, w ω v) = number (G.induce (W ω : Set V))
    rw [← heq ω]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact hz ω v hv
  have hφsum : ∀ ω, ∑ v, φ ω v ≤ 1 := by
    intro ω
    by_cases ha : 0 < a ω
    · simp only [φ,ite_eq_left ha,← Finset.sum_div,hwtotal,div_self (ne_of_gt ha),le_refl]
    · simp [φ,ha]
  have hφW (ω : Ω) (ha : 0 < a ω) : (∑ v ∈ W ω, φ ω v) = 1 := by
    simp only [φ,ite_eq_left ha,← Finset.sum_div,heq]
    change a ω / a ω = 1
    exact div_self (ne_of_gt ha)
  let bad : ι → (ι → Ω) → Prop := fun i x =>
    a (x i) ≤ r/5 ∨ (1/4 : ℝ) ≤ collision W φ i x
  have hbad_sub (x : ι → Ω) :
      (∃ i, number (G.induce (privateCopy W i x : Set V)) ≤ r/8) → ∃ i, bad i x := by
    rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    by_contra hn
    have hh : r/5 < a (x i) := lt_of_not_ge (fun h => hn (Or.inl h))
    have hc : collision W φ i x < 1/4 := lt_of_not_ge (fun h => hn (Or.inr h))
    have ha : 0 < a (x i) := by linarith
    have hret := private_weight_loss W hφ i x
    rw [hφW (x i) ha] at hret
    have hweight : (∑ v ∈ privateCopy W i x, w (x i) v) ≤ r/8 :=
      ((hw (x i)).restrict_sum _).trans hi
    have hsum : (∑ v ∈ privateCopy W i x, φ (x i) v) =
        (∑ v ∈ privateCopy W i x, w (x i) v) / a (x i) := by
      simp only [φ,ite_eq_left ha,Finset.sum_div]
    rw [hsum] at hret
    have hpos : (3/4 : ℝ) <
        (∑ v ∈ privateCopy W i x, w (x i) v) / a (x i) := by linarith
    have hprod := (lt_div_iff₀ ha).mp hpos
    nlinarith
  have hbad (i : ι) : probability (productMass (fun _ : ι => μ)) (bad i) ≤
      δ + 4 * (Fintype.card ι - 1 : ℕ) * p := by
    have hor := probability_or_le (productMass_nonneg (fun _ => hμ))
      (fun x : ι → Ω => a (x i) ≤ r/5) (fun x => (1/4 : ℝ) ≤ collision W φ i x)
    have hfirst : probability (productMass (fun _ : ι => μ)) (fun x => a (x i) ≤ r/5) ≤ δ := by
      rw [probability_coordinate (μ := fun _ : ι => μ) (fun _ => hs) i
        (fun ω => a ω ≤ r/5)]
      exact hhigh
    have hmk := markov (productMass_nonneg (fun _ : ι => hμ)) (collision_nonneg W hφ i)
      (a := (1/4 : ℝ)) (by norm_num)
    have hexp := expectation_collision hμ hs W hφ hφsum hp hmarg i
    change probability (productMass (fun _ : ι => μ))
      (fun x => a (x i) ≤ r/5 ∨ (1/4 : ℝ) ≤ collision W φ i x) ≤ _
    linarith
  calc
    _ ≤ probability (productMass (fun _ : ι => μ)) (fun x => ∃ i, bad i x) :=
      probability_mono (productMass_nonneg (fun _ => hμ)) hbad_sub
    _ ≤ ∑ i, probability (productMass (fun _ : ι => μ)) (bad i) :=
      probability_union_le (productMass_nonneg (fun _ => hμ)) _
    _ ≤ ∑ _i : ι, (δ + 4 * (Fintype.card ι - 1 : ℕ) * p) :=
      Finset.sum_le_sum (fun i _ => hbad i)
    _ = _ := by simp; ring

end LinearListHadwiger.Sampling

end OAI
