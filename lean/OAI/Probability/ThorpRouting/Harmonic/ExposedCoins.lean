import Mathlib
import OAI.Probability.ThorpRouting.Harmonic.Coins

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

lemma card_routeDomain (d : ℕ) (x y : Card d) : (routeDomain d x y).card = d := by
  classical
  induction d with
  | zero => rfl
  | succ d ih =>
    change (insert (Sum.inl (Fin.tail y))
      ((routeDomain d (Fin.tail x) (Fin.tail y)).image
        (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
      Finset (Sum (Card d) (Bool × SwitchIndex d))).card = d + 1
    rw [Finset.card_insert_of_notMem (by simp)]
    rw [Finset.card_image_of_injective _ (by intro i j h; cases h; rfl), ih]

lemma xor_eq_iff (a b c : Bool) : Bool.xor a b = c ↔ b = Bool.xor a c := by
  cases a <;> cases b <;> cases c <;> decide

lemma butterfly_endpoint_iff (d : ℕ) (ω : SwitchIndex d → Bool) (x y : Card d) :
    butterflyPerm d (decodeButterfly d ω) x = y ↔
      ∀ i ∈ routeDomain d x y, ω i = routeValue d x y i := by
  classical
  induction d with
  | zero =>
    have he : butterflyPerm 0 (decodeButterfly 0 ω) x = y := Subsingleton.elim _ _
    simp [he, routeDomain]
  | succ d ih =>
    let v := butterflyPerm d (decodeButterfly d (fun i => ω (Sum.inr (x 0,i)))) (Fin.tail x)
    change Fin.cons (Bool.xor (x 0) (ω (Sum.inl v))) v = y ↔ _
    have hv : v = Fin.tail y ↔
        ∀ i ∈ routeDomain d (Fin.tail x) (Fin.tail y),
          ω (Sum.inr (x 0,i)) = routeValue d (Fin.tail x) (Fin.tail y) i :=
      ih _ _ _
    constructor
    · intro h i hi
      have ht : v = Fin.tail y := by simpa using congrArg Fin.tail h
      have hh : ω (Sum.inl (Fin.tail y)) = Bool.xor (x 0) (y 0) := by
        have he := congrFun h 0
        simp only [Fin.cons_zero, ht] at he
        exact (xor_eq_iff _ _ _).mp he
      rcases Finset.mem_insert.mp hi with htop | hchild
      · subst i
        exact hh
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hchild
        exact hv.mp ht j hj
    · intro h
      have hh := h (Sum.inl (Fin.tail y)) (Finset.mem_insert_self _ _)
      have ht : v = Fin.tail y := hv.mpr (fun i hi =>
        h (Sum.inr (x 0,i)) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)))
      have hh' : Bool.xor (x 0) (ω (Sum.inl (Fin.tail y))) = y 0 :=
        (xor_eq_iff _ _ _).mpr hh
      rw [ht, hh', Fin.cons_self_tail]

lemma finiteMean_congr {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : finiteMean f = finiteMean g := by
  unfold finiteMean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

lemma mean_coinCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (v : ι → Bool) :
    finiteMean (fun ω : ι → Bool => if ∀ i ∈ s, ω i = v i then (1 : ℝ) else 0) =
      1 / (2 : ℝ) ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp [finiteMean]
  | @insert i s hi ih =>
    let f := fun ω : ι → Bool => if ∀ j ∈ s, ω j = v j then (1 : ℝ) else 0
    have hf : ∀ ω, f (QueryTree.flipCoin i ω) = f ω := by
      intro ω
      have he : (∀ j ∈ s, QueryTree.flipCoin i ω j = v j) ↔ ∀ j ∈ s, ω j = v j := by
        apply forall₂_congr
        intro j hj
        rw [QueryTree.flipCoin_apply_ne i j (fun h => hi (h ▸ hj))]
      dsimp [f]
      simp only [he]
    have hm := QueryTree.mean_indicator_bit f i (v i) hf
    have he : (fun ω : ι → Bool => if ∀ j ∈ insert i s, ω j = v j then (1 : ℝ) else 0) =
        (fun ω => if ω i = v i then f ω else 0) := by
      funext ω
      by_cases h : ω i = v i <;> simp [f, h]
    rw [he, hm]
    change finiteMean (fun ω : ι → Bool => if ∀ j ∈ s, ω j = v j then (1 : ℝ) else 0) / 2 = _
    rw [ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

def exposedCoins {ι : Type*} [DecidableEq ι] (R : Finset ι) (η ω : ι → Bool) : ι → Bool :=
  fun i => if i ∈ R then η i else ω i

lemma mean_coinCylinder_exposed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s R : Finset ι) (v η : ι → Bool) :
    finiteMean (fun ω : ι → Bool =>
      if ∀ i ∈ s, exposedCoins R η ω i = v i then (1 : ℝ) else 0) =
    if (∀ i ∈ s ∩ R, η i = v i) then 1 / (2 : ℝ) ^ (s \ R).card else 0 := by
  have he (ω : ι → Bool) : (∀ i ∈ s, exposedCoins R η ω i = v i) ↔
      (∀ i ∈ s ∩ R, η i = v i) ∧ (∀ i ∈ s \ R, ω i = v i) := by
    constructor
    · intro h
      constructor
      · intro i hi
        simpa [exposedCoins, (Finset.mem_inter.mp hi).2] using h i (Finset.mem_inter.mp hi).1
      · intro i hi
        simpa [exposedCoins, (Finset.mem_sdiff.mp hi).2] using h i (Finset.mem_sdiff.mp hi).1
    · rintro ⟨ho, hf⟩ i hi
      by_cases hR : i ∈ R
      · simpa [exposedCoins, hR] using ho i (Finset.mem_inter.mpr ⟨hi,hR⟩)
      · simpa [exposedCoins, hR] using hf i (Finset.mem_sdiff.mpr ⟨hi,hR⟩)
  have hm : finiteMean (fun ω : ι → Bool =>
      if ∀ i ∈ s, exposedCoins R η ω i = v i then (1 : ℝ) else 0) =
      finiteMean (fun ω : ι → Bool =>
        if (∀ i ∈ s ∩ R, η i = v i) ∧ (∀ i ∈ s \ R, ω i = v i) then (1 : ℝ) else 0) :=
    finiteMean_congr (fun ω => by simp only [he ω])
  rw [hm]
  by_cases h : ∀ i ∈ s ∩ R, η i = v i
  · have hp : (∀ i ∈ s ∩ R, η i = v i) ↔ True := iff_true_intro h
    simp only [hp, true_and, ↓reduceIte]
    exact mean_coinCylinder (s \ R) v
  · have hp : (∀ i ∈ s ∩ R, η i = v i) ↔ False := iff_false_intro h
    simp only [hp, false_and, ↓reduceIte]
    simp [finiteMean]

lemma butterfly_closure_probability (d : ℕ) (x y : Card d)
    (R : Finset (SwitchIndex d)) (η : SwitchIndex d → Bool) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      if butterflyPerm d (decodeButterfly d (exposedCoins R η ω)) x = y then (1 : ℝ) else 0) =
      if (∀ i ∈ routeDomain d x y ∩ R, η i = routeValue d x y i) then
        (2 : ℝ) ^ (routeDomain d x y ∩ R).card / (2 : ℝ) ^ d else 0 := by
  have he : finiteMean (fun ω : SwitchIndex d → Bool =>
      if butterflyPerm d (decodeButterfly d (exposedCoins R η ω)) x = y then (1 : ℝ) else 0) =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        if ∀ i ∈ routeDomain d x y, exposedCoins R η ω i = routeValue d x y i then (1 : ℝ) else 0) :=
    finiteMean_congr (fun ω => by simp only [butterfly_endpoint_iff])
  rw [he, mean_coinCylinder_exposed]
  congr 1
  have hc : (routeDomain d x y \ R).card + (routeDomain d x y ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter, card_routeDomain]
  have hp : (2 : ℝ) ^ d = (2 : ℝ) ^ (routeDomain d x y \ R).card *
      (2 : ℝ) ^ (routeDomain d x y ∩ R).card := by
    rw [← pow_add]
    exact congrArg (fun n => (2 : ℝ) ^ n) hc.symm
  rw [hp]
  have hn : (2 : ℝ) ^ (routeDomain d x y ∩ R).card ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

lemma butterfly_single_card_uniform (d : ℕ) (x y : Card d) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      if butterflyPerm d (decodeButterfly d ω) x = y then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d := by
  have he : finiteMean (fun ω : SwitchIndex d → Bool =>
      if butterflyPerm d (decodeButterfly d ω) x = y then (1 : ℝ) else 0) =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        if ∀ i ∈ routeDomain d x y, ω i = routeValue d x y i then (1 : ℝ) else 0) :=
    finiteMean_congr (fun ω => by simp only [butterfly_endpoint_iff])
  rw [he, mean_coinCylinder, card_routeDomain]

def switchUsers : (d : ℕ) → Butterfly d → SwitchIndex d → Card d × Card d
  | 0, _, i => nomatch i
  | d + 1, b, Sum.inl y =>
      (Fin.cons false ((butterflyPerm d (b.2 false)).symm y),
       Fin.cons true ((butterflyPerm d (b.2 true)).symm y))
  | d + 1, b, Sum.inr (ε,i) =>
      (Fin.cons ε (switchUsers d (b.2 ε) i).1,
       Fin.cons ε (switchUsers d (b.2 ε) i).2)

lemma switchUsers_ne (d : ℕ) (b : Butterfly d) (i : SwitchIndex d) :
    (switchUsers d b i).1 ≠ (switchUsers d b i).2 := by
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      intro h
      have := congrFun h 0
      simp only [switchUsers, Fin.cons_zero] at this
      exact Bool.false_ne_true this
    | inr z =>
      intro h
      exact ih (b.2 z.1) z.2 (by simpa only [switchUsers, Fin.tail_cons] using congrArg Fin.tail h)

lemma cons_eq_iff {d : ℕ} (ε : Bool) (a : Card d) (x : Card (d + 1)) :
    Fin.cons ε a = x ↔ ε = x 0 ∧ a = Fin.tail x := by
  constructor
  · intro h
    exact ⟨by simpa only [Fin.cons_zero] using congrFun h 0,
      by simpa only [Fin.tail_cons] using congrArg Fin.tail h⟩
  · rintro ⟨rfl,rfl⟩
    exact Fin.cons_self_tail x

lemma mem_routeDomain_iff_user (d : ℕ) (b : Butterfly d) (x : Card d) (i : SwitchIndex d) :
    i ∈ routeDomain d x (butterflyPerm d b x) ↔
      (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x := by
  classical
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      change Sum.inl y ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inl.injEq, Finset.mem_image,
        Sum.inr_ne_inl, and_false, exists_false, or_false]
      change y = butterflyPerm d (b.2 (x 0)) (Fin.tail x) ↔ _
      simp only [switchUsers, cons_eq_iff]
      cases x 0 <;> simp [Equiv.symm_apply_eq]
    | inr z =>
      obtain ⟨ε,i⟩ := z
      change Sum.inr (ε,i) ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inr_ne_inl, false_or, Finset.mem_image,
        Sum.inr.injEq, Prod.mk.injEq]
      change (∃ j, j ∈ routeDomain d (Fin.tail x) (butterflyPerm d (b.2 (x 0)) (Fin.tail x)) ∧
        x 0 = ε ∧ j = i) ↔ _
      simp only [switchUsers, cons_eq_iff]
      constructor
      · rintro ⟨j,hj,hε,rfl⟩
        subst ε
        rcases (ih (b.2 (x 0)) (Fin.tail x) j).mp hj with h | h
        · exact Or.inl ⟨rfl,h⟩
        · exact Or.inr ⟨rfl,h⟩
      · rintro (⟨hε,h⟩ | ⟨hε,h⟩)
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inl h),rfl,rfl⟩
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inr h),rfl,rfl⟩

lemma card_switches_using (d : ℕ) (b : Butterfly d) (x : Card d) :
    (Finset.univ.filter (fun i : SwitchIndex d =>
      (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x)).card = d := by
  classical
  have he : Finset.univ.filter (fun i : SwitchIndex d =>
      (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x) =
      routeDomain d x (butterflyPerm d b x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_routeDomain_iff_user]
  rw [he,card_routeDomain]

lemma switch_incidence_sum (d : ℕ) (b : Butterfly d) (w : Card d → ℝ) :
    ∑ i : SwitchIndex d, (w (switchUsers d b i).1 + w (switchUsers d b i).2) =
      (d : ℝ) * ∑ x : Card d, w x := by
  classical
  calc
    _ = ∑ i : SwitchIndex d, ∑ x : Card d,
        if (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x then w x else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      have he : Finset.univ.filter (fun x : Card d =>
          (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x) =
          {(switchUsers d b i).1, (switchUsers d b i).2} := by
        ext x; simp [eq_comm]
      rw [he, Finset.sum_pair (switchUsers_ne d b i)]
    _ = ∑ x : Card d, ∑ i : SwitchIndex d,
        if (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x then w x else 0 :=
      Finset.sum_comm
    _ = ∑ x : Card d, (d : ℝ) * w x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        card_switches_using]
    _ = _ := by rw [Finset.mul_sum]

lemma weighted_switch_min_bound (d : ℕ) (b : Butterfly d) (w : Card d → ℝ) :
    ∑ i : SwitchIndex d, min (w (switchUsers d b i).1) (w (switchUsers d b i).2) ≤
      (d : ℝ) / 2 * ∑ x : Card d, w x := by
  have h : 2 * (∑ i : SwitchIndex d,
      min (w (switchUsers d b i).1) (w (switchUsers d b i).2)) ≤
      ∑ i : SwitchIndex d, (w (switchUsers d b i).1 + w (switchUsers d b i).2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    linarith [min_le_left (w (switchUsers d b i).1) (w (switchUsers d b i).2),
      min_le_right (w (switchUsers d b i).1) (w (switchUsers d b i).2)]
  rw [switch_incidence_sum] at h
  linarith

lemma mem_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) (x : Card d) :
    x ∈ childMarks s ε ↔ Fin.cons ε x ∈ s := by
  classical
  constructor
  · intro h
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hys,hyε⟩ := Finset.mem_filter.mp hy
    rw [← hxy, ← hyε, Fin.cons_self_tail]
    exact hys
  · intro h
    exact Finset.mem_image.mpr ⟨Fin.cons ε x,
      Finset.mem_filter.mpr ⟨h,by simp⟩,by simp⟩

lemma mem_topMeetings {d : ℕ} (b : Butterfly (d + 1))
    (s : Finset (Card (d + 1))) (y : Card d) :
    y ∈ topMeetings b s ↔
      (switchUsers (d+1) b (Sum.inl y)).1 ∈ s ∧
      (switchUsers (d+1) b (Sum.inl y)).2 ∈ s := by
  classical
  have he (ε : Bool) : y ∈ (childMarks s ε).image (butterflyPerm d (b.2 ε)) ↔
      (butterflyPerm d (b.2 ε)).symm y ∈ childMarks s ε := by
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      simpa only [Equiv.symm_apply_apply] using hx
    · intro h
      exact Finset.mem_image.mpr ⟨_,h,Equiv.apply_symm_apply _ _⟩
  simp only [topMeetings, Finset.mem_inter, he, mem_childMarks, switchUsers]

lemma encounters_eq_switch_sum (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    encounters d b s = ∑ i : SwitchIndex d,
      if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then 1 else 0 := by
  classical
  induction d with
  | zero =>
    simp only [encounters]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact Empty.elim i
  | succ d ih =>
    change encounters d (b.2 false) (childMarks s false) +
      encounters d (b.2 true) (childMarks s true) + (topMeetings b s).card =
        ∑ i : Sum (Card d) (Bool × SwitchIndex d), _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [ih,ih]
    have ht : (∑ y : Card d,
        if (switchUsers (d+1) b (Sum.inl y)).1 ∈ s ∧
          (switchUsers (d+1) b (Sum.inl y)).2 ∈ s then 1 else 0) =
        (topMeetings b s).card := by
      simp only [← mem_topMeetings]
      simp
    rw [ht]
    simp only [mem_childMarks, switchUsers]
    ac_rfl

lemma marked_switch_entropy_bound (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    (∑ i : SwitchIndex d,
      if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then (1:ℝ) else 0) ≤
      (s.card : ℝ) * Real.log s.card / (2 * Real.log 2) := by
  classical
  have he : (encounters d b s : ℝ) =
      ∑ i : SwitchIndex d,
        if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then (1:ℝ) else 0 := by
    rw [encounters_eq_switch_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [← he]
  exact butterfly_encounters d b s

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

def memo : QueryTree ι → Finset ι → (ι → Bool) → QueryTree ι
  | reject, _, _ => reject
  | accept, _, _ => accept
  | branch i zero one, R, η =>
      if i ∈ R then (if η i then memo one R η else memo zero R η) else
      branch i (memo zero (insert i R) (Function.update η i false))
        (memo one (insert i R) (Function.update η i true))
  | force i b next, R, η =>
      if i ∈ R then (if η i = b then memo next R η else reject) else
      force i b (memo next (insert i R) (Function.update η i b))

lemma memo_queries_disjoint (T : QueryTree ι) (R : Finset ι) (η : ι → Bool) :
    Disjoint (memo T R η).queries R := by
  induction T generalizing R η with
  | reject => simp [memo,queries]
  | accept => simp [memo,queries]
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      cases η i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η
      · exact ih₁ R η
    · simp only [memo,hi,↓reduceIte,queries,Finset.disjoint_insert_left,Finset.disjoint_union_left]
      exact ⟨by simp, (ih₀ (insert i R) _).mono_right (Finset.subset_insert _ _),
        (ih₁ (insert i R) _).mono_right (Finset.subset_insert _ _)⟩
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      by_cases hb : η i = b
      · simpa only [hb,↓reduceIte] using ih R η
      · simp [hb,queries]
    · simp only [memo,hi,↓reduceIte,queries,Finset.disjoint_insert_left]
      exact ⟨by simp,(ih (insert i R) _).mono_right (Finset.subset_insert _ _)⟩

lemma memo_fresh (T : QueryTree ι) (R : Finset ι) (η : ι → Bool) :
    (memo T R η).Fresh := by
  induction T generalizing R η with
  | reject => trivial
  | accept => trivial
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      cases η i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η
      · exact ih₁ R η
    · simp only [memo,hi,↓reduceIte,Fresh]
      exact ⟨fun hm => Finset.disjoint_left.mp (memo_queries_disjoint zero (insert i R) _) hm
          (Finset.mem_insert_self _ _),
        fun hm => Finset.disjoint_left.mp (memo_queries_disjoint one (insert i R) _) hm
          (Finset.mem_insert_self _ _), ih₀ _ _,ih₁ _ _⟩
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      by_cases hb : η i = b
      · simpa only [hb,↓reduceIte] using ih R η
      · simp [hb,Fresh]
    · simp only [memo,hi,↓reduceIte,Fresh]
      exact ⟨fun hm => Finset.disjoint_left.mp (memo_queries_disjoint next (insert i R) _) hm
        (Finset.mem_insert_self _ _),ih _ _⟩

lemma update_agrees {R : Finset ι} {η ω : ι → Bool}
    (h : ∀ i ∈ R, η i = ω i) (i : ι) :
    ∀ j ∈ insert i R, Function.update η i (ω i) j = ω j := by
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simp
  · by_cases hji : j = i
    · subst j; simp
    · rw [Function.update_of_ne hji]
      exact h j hj

lemma memo_succeeds (T : QueryTree ι) (R : Finset ι) (η ω : ι → Bool)
    (h : ∀ i ∈ R, η i = ω i) : (memo T R η).succeeds ω = T.succeeds ω := by
  induction T generalizing R η with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,succeeds,h i hi]
      cases ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η h
      · exact ih₁ R η h
    · simp only [memo,hi,↓reduceIte,succeeds]
      cases hb : ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ _ _ (by simpa only [hb] using update_agrees h i)
      · exact ih₁ _ _ (by simpa only [hb] using update_agrees h i)
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,h i hi]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte,succeeds]
        exact ih R η h
      · simp [hb,succeeds]
    · simp only [memo,hi,↓reduceIte,succeeds]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        exact ih _ _ (by simpa only [hb] using update_agrees h i)
      · simp [hb]

def freshCharge : QueryTree ι → Finset ι → (ι → Bool) → ℕ
  | reject, _, _ => 0
  | accept, _, _ => 0
  | branch i zero one, R, ω => if ω i then freshCharge one (insert i R) ω else freshCharge zero (insert i R) ω
  | force i b next, R, ω => if ω i = b then
      freshCharge next (insert i R) ω + (if i ∈ R then 0 else 1) else 0

lemma memo_charge (T : QueryTree ι) (R : Finset ι) (η ω : ι → Bool)
    (h : ∀ i ∈ R, η i = ω i) : (memo T R η).charge ω = freshCharge T R ω := by
  induction T generalizing R η with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,freshCharge,h i hi,Finset.insert_eq_of_mem hi]
      cases ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η h
      · exact ih₁ R η h
    · simp only [memo,hi,↓reduceIte,charge,freshCharge]
      cases hb : ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ _ _ (by simpa only [hb] using update_agrees h i)
      · exact ih₁ _ _ (by simpa only [hb] using update_agrees h i)
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,h i hi,freshCharge,Finset.insert_eq_of_mem hi,Nat.add_zero]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        exact ih R η h
      · simp [hb,charge]
    · simp only [memo,hi,↓reduceIte,charge,freshCharge]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        rw [ih _ _ (by simpa only [hb] using update_agrees h i)]
      · simp [hb]

lemma mean_freshCharge_le_one [Fintype ι] (T : QueryTree ι) :
    finiteMean (fun ω : ι → Bool =>
      if T.succeeds ω then (2:ℝ) ^ T.freshCharge ∅ ω else 0) ≤ 1 := by
  let η : ι → Bool := fun _ => false
  have hm := mean_weighted_le_one (memo T ∅ η) (memo_fresh T ∅ η)
  have he : finiteMean (memo T ∅ η).weighted =
      finiteMean (fun ω : ι → Bool =>
        if T.succeeds ω then (2:ℝ) ^ T.freshCharge ∅ ω else 0) := by
    apply finiteMean_congr
    intro ω
    rw [weighted_eq, memo_succeeds _ _ _ _ (by simp), memo_charge _ _ _ _ (by simp)]
  rw [he] at hm
  exact hm


def followPath : (d : ℕ) → (SwitchIndex d → ι) → Card d →
    (Card d → QueryTree ι) → QueryTree ι
  | 0, _, x, k => k x
  | d + 1, e, x, k => followPath d (fun i => e (Sum.inr (x 0,i))) (Fin.tail x)
      (fun y => branch (e (Sum.inl y))
        (k (Fin.cons (Bool.xor (x 0) false) y))
        (k (Fin.cons (Bool.xor (x 0) true) y)))

omit [DecidableEq ι] in
lemma followPath_succeeds (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (ω : ι → Bool) :
    (followPath d e x k).succeeds ω =
      (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).succeeds ω := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    change (if ω (e (Sum.inl y)) then
      (k (Fin.cons (Bool.xor (x 0) true) y)).succeeds ω else
      (k (Fin.cons (Bool.xor (x 0) false) y)).succeeds ω) =
      (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).succeeds ω
    cases ω (e (Sum.inl y)) <;> rfl

lemma followPath_charge (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    freshCharge (followPath d e x k) R ω =
      freshCharge (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
        (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω := by
  classical
  induction d generalizing R with
  | zero => simp only [followPath, routeDomain, Finset.image_empty, Finset.union_empty]; rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    let S := (routeDomain d (Fin.tail x) y).image (fun i => e (Sum.inr (x 0,i)))
    change (if ω (e (Sum.inl y)) then
      freshCharge (k (Fin.cons (Bool.xor (x 0) true) y)) (insert (e (Sum.inl y)) (R ∪ S)) ω else
      freshCharge (k (Fin.cons (Bool.xor (x 0) false) y)) (insert (e (Sum.inl y)) (R ∪ S)) ω) =
      freshCharge (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y))
        (R ∪ (routeDomain (d+1) x
          (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).image e) ω
    have hs : (routeDomain (d+1) x
        (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).image e =
        insert (e (Sum.inl y)) S := by
      let e' : Sum (Card d) (Bool × SwitchIndex d) → ι := e
      change (insert (Sum.inl y)
        ((routeDomain d (Fin.tail x) y).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
          Finset (Sum (Card d) (Bool × SwitchIndex d))).image e' = _
      rw [Finset.image_insert, Finset.image_image]
      rfl
    rw [hs,Finset.union_insert]
    cases ω (e (Sum.inl y)) <;> rfl

def forceList : List ι → (ι → Bool) → QueryTree ι → QueryTree ι
  | [], _, k => k
  | i :: L, v, k => force i (v i) (forceList L v k)

omit [DecidableEq ι] in
lemma forceList_succeeds (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool) :
    (forceList L v k).succeeds ω =
      if ∀ i ∈ L, ω i = v i then k.succeeds ω else false := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    simp only [forceList,succeeds,ih,List.mem_cons,forall_eq_or_imp]
    by_cases h : ω i = v i <;> simp [h]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


def staleCharge : QueryTree ι → Finset ι → (ι → Bool) → ℕ
  | reject, _, _ => 0
  | accept, _, _ => 0
  | branch i zero one, R, ω => if ω i then staleCharge one (insert i R) ω
      else staleCharge zero (insert i R) ω
  | force i b next, R, ω => if ω i = b then
      staleCharge next (insert i R) ω + (if i ∈ R then 1 else 0) else 0

lemma fresh_add_stale (T : QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    T.freshCharge R ω + T.staleCharge R ω = T.charge ω := by
  induction T generalizing R with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    cases hb : ω i <;> simp [freshCharge,staleCharge,charge,hb,ih₀,ih₁]
  | force i b next ih =>
    by_cases hb : ω i = b
    · simp only [freshCharge,staleCharge,charge,hb,↓reduceIte]
      have he := ih (insert i R)
      by_cases hi : i ∈ R <;> simp only [hi,↓reduceIte] <;> omega
    · simp [freshCharge,staleCharge,charge,hb]

omit [DecidableEq ι] in
lemma followPath_raw_charge (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (ω : ι → Bool) :
    (followPath d e x k).charge ω =
      (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).charge ω := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    change (if ω (e (Sum.inl y)) then
      (k (Fin.cons (Bool.xor (x 0) true) y)).charge ω else
      (k (Fin.cons (Bool.xor (x 0) false) y)).charge ω) =
      (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).charge ω
    cases ω (e (Sum.inl y)) <;> rfl

omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

noncomputable def closePath (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d)) :
    QueryTree (SwitchIndex d) :=
  forceList (routeDomain d x y).toList (routeValue d x y) k

lemma closePath_succeeds (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (ω : SwitchIndex d → Bool) :
    (closePath d x y k).succeeds ω =
      if butterflyPerm d (decodeButterfly d ω) x = y then k.succeeds ω else false := by
  unfold closePath
  rw [forceList_succeeds]
  simp only [Finset.mem_toList, ← butterfly_endpoint_iff]

lemma closePath_raw_charge (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (ω : SwitchIndex d → Bool) (h : butterflyPerm d (decodeButterfly d ω) x = y) :
    (closePath d x y k).charge ω = k.charge ω + d := by
  unfold closePath
  rw [forceList_raw_charge _ _ _ _ (by simpa only [Finset.mem_toList] using
    (butterfly_endpoint_iff d ω x y).mp h), Finset.length_toList, card_routeDomain]

lemma closePath_fresh_charge (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (R : Finset (SwitchIndex d)) (ω : SwitchIndex d → Bool)
    (h : butterflyPerm d (decodeButterfly d ω) x = y) :
    (closePath d x y k).freshCharge R ω =
      k.freshCharge (R ∪ routeDomain d x y) ω + (routeDomain d x y \ R).card := by
  unfold closePath
  rw [forceList_charge _ _ _ _ _ (by simpa only [Finset.mem_toList] using
    (butterfly_endpoint_iff d ω x y).mp h), Finset.toList_toFinset]

lemma closePath_stale_charge (d : ℕ) (x y : Card d) (k : QueryTree (SwitchIndex d))
    (R : Finset (SwitchIndex d)) (ω : SwitchIndex d → Bool)
    (h : butterflyPerm d (decodeButterfly d ω) x = y) :
    (closePath d x y k).staleCharge R ω =
      k.staleCharge (R ∪ routeDomain d x y) ω + (routeDomain d x y ∩ R).card := by
  have h₀ := fresh_add_stale (closePath d x y k) R ω
  have h₁ := fresh_add_stale k (R ∪ routeDomain d x y) ω
  rw [closePath_raw_charge _ _ _ _ _ h,closePath_fresh_charge _ _ _ _ _ _ h] at h₀
  have h₂ : (routeDomain d x y \ R).card + (routeDomain d x y ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_routeDomain]
  omega

noncomputable def seekCycle (d : ℕ) (S : Finset (Card d)) (a : Card d) :
    ℕ → Card d → Finset (Card d) → (Finset (Card d) → QueryTree (SwitchIndex d)) →
      QueryTree (SwitchIndex d)
  | 0, x, V, k => if x ∈ S ∧ x ∉ V then closePath d x a (k (insert x V)) else reject
  | r + 1, x, V, k => if x ∈ S ∧ x ∉ V then followPath d id x
      (fun y => seekCycle d S a r y (insert x V) k) else reject

lemma seekCycle_raw_charge (d : ℕ) (S : Finset (Card d)) (a : Card d) (r : ℕ)
    (x : Card d) (V : Finset (Card d)) (k : Finset (Card d) → QueryTree (SwitchIndex d))
    (ω : SwitchIndex d → Bool) (K : ℕ)
    (hK : ∀ V, (k V).succeeds ω = true → (k V).charge ω = K)
    (hs : (seekCycle d S a r x V k).succeeds ω = true) :
    (seekCycle d S a r x V k).charge ω = K + d := by
  induction r generalizing x V with
  | zero =>
    by_cases hv : x ∈ S ∧ x ∉ V
    · rw [seekCycle,ite_eq_left hv,closePath_succeeds] at hs
      split_ifs at hs with he
      · rw [seekCycle,ite_eq_left hv,closePath_raw_charge _ _ _ _ _ he,hK _ hs]
    · simp [seekCycle,hv,succeeds] at hs
  | succ r ih =>
    by_cases hv : x ∈ S ∧ x ∉ V
    · rw [seekCycle,ite_eq_left hv,followPath_succeeds] at hs
      rw [seekCycle,ite_eq_left hv,followPath_raw_charge]
      exact ih _ _ hs
    · simp [seekCycle,hv,succeeds] at hs

noncomputable def seekCycles (d : ℕ) (S : Finset (Card d)) :
    List (Card d × ℕ) → Finset (Card d) → QueryTree (SwitchIndex d)
  | [], _ => accept
  | (a,r) :: L, V => seekCycle d S a r a V (fun V => seekCycles d S L V)

lemma seekCycles_raw_charge (d : ℕ) (S : Finset (Card d)) (L : List (Card d × ℕ))
    (V : Finset (Card d)) (ω : SwitchIndex d → Bool)
    (hs : (seekCycles d S L V).succeeds ω = true) :
    (seekCycles d S L V).charge ω = L.length * d := by
  induction L generalizing V with
  | nil => simp [seekCycles,charge]
  | cons ar L ih =>
    obtain ⟨a,r⟩ := ar
    rw [seekCycles]
    rw [seekCycle_raw_charge d S a r a V (fun V => seekCycles d S L V) ω (L.length*d)
      (fun V hs => ih V hs) hs]
    simp [Nat.add_mul]

lemma cycles_weighted_success (d : ℕ) (S : Finset (Card d)) (L : List (Card d × ℕ)) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      if (seekCycles d S L ∅).succeeds ω then
        ((2:ℝ)^d)^L.length / (2:ℝ)^(seekCycles d S L ∅).staleCharge ∅ ω else 0) ≤ 1 := by
  let T := seekCycles d S L ∅
  have hh := mean_freshCharge_le_one T
  have he : finiteMean (fun ω : SwitchIndex d → Bool =>
      if T.succeeds ω then (2:ℝ)^T.freshCharge ∅ ω else 0) =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        if T.succeeds ω then ((2:ℝ)^d)^L.length / (2:ℝ)^T.staleCharge ∅ ω else 0) := by
    apply finiteMean_congr
    intro ω
    cases hs : T.succeeds ω
    · simp
    · simp only [↓reduceIte]
      have hc := fresh_add_stale T ∅ ω
      rw [seekCycles_raw_charge d S L ∅ ω hs] at hc
      have hp : ((2:ℝ)^d)^L.length = (2:ℝ)^T.freshCharge ∅ ω * (2:ℝ)^T.staleCharge ∅ ω := by
        rw [←pow_add,hc,←pow_mul,Nat.mul_comm]
      rw [hp,mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))]
  rw [← he]
  exact hh

end QueryTree

lemma finiteMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    finiteMean (fun ω => f ω + g ω) = finiteMean f + finiteMean g := by
  simp only [finiteMean,Finset.sum_add_distrib,add_div]

lemma finiteMean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    finiteMean (fun ω => f ω * c) = finiteMean f * c := by
  unfold finiteMean
  rw [← Finset.sum_mul]
  ring

lemma finiteMean_sum {Ω α : Type*} [Fintype Ω] (s : Finset α) (f : α → Ω → ℝ) :
    finiteMean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean,Finset.sum_div]
  exact Finset.sum_comm

lemma finiteMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

lemma finiteMean_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω → ℝ) :
    finiteMean f = finiteMean (fun ω => f (e.symm ω)) := by
  unfold finiteMean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun ω => by simp)

lemma finiteMean_prod_left {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω']
    (f : Ω → ℝ) : finiteMean (fun ω : Ω × Ω' => f ω.1) = finiteMean f := by
  simp only [finiteMean,Fintype.sum_prod_type,Finset.sum_const,nsmul_eq_mul,
    ← Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,Finset.card_univ]
  have hn : (Fintype.card Ω' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma finiteMean_pi_eval {C : Type*} [Fintype C] [DecidableEq C]
    {A : C → Type*} [∀ c, Fintype (A c)] [∀ c, Nonempty (A c)]
    (c : C) (g : A c → ℝ) :
    finiteMean (fun z : ∀ c, A c => g (z c)) = finiteMean g := by
  rw [finiteMean_equiv (Equiv.piSplitAt c A)]
  have he : (fun z : A c × ((j : {j // j ≠ c}) → A j) =>
      g ((Equiv.piSplitAt c A).symm z c)) = (fun z => g z.1) := by
    funext z
    simp [Equiv.piSplitAt]
  rw [he,finiteMean_prod_left]

lemma finiteMean_eq_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) :
    finiteMean (fun ω : Ω => if ω = a then (1:ℝ) else 0) = 1 / Fintype.card Ω := by
  simp [finiteMean]

lemma exp_finiteMean_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    Real.exp (finiteMean f) ≤ finiteMean (fun ω => Real.exp (f ω)) := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hw : ∑ ω : Ω, (1 / (Fintype.card Ω : ℝ)) = 1 := by simp [hn]
  have hj := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun _ : Ω => 1 / (Fintype.card Ω : ℝ)) (p := f)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  simpa only [finiteMean, div_eq_mul_inv, one_div, mul_comm, mul_one, one_mul] using hj

variable {d A : ℕ}

def cycleFiber (o : Card d → Option (Fin A)) (i : Fin A) : Finset (Card d) := by
  classical
  exact Finset.univ.filter (fun x => o x = some i)

@[simp] lemma mem_cycleFiber (o : Card d → Option (Fin A)) (i : Fin A) (x : Card d) :
    x ∈ cycleFiber o i ↔ o x = some i := by
  classical
  simp [cycleFiber]

abbrev Terminal (o : Card d → Option (Fin A)) := ∀ i : Fin A, {x : Card d // o x = some i}

noncomputable def slotWeight (o : Card d → Option (Fin A)) (i : Fin A) : ℝ :=
  1 / (cycleFiber o i).card

noncomputable def pathWeight (o : Card d → Option (Fin A)) (x : Card d) : ℝ :=
  match o x with
  | none => 0
  | some i => slotWeight o i

noncomputable def withinWeight (o : Card d → Option (Fin A)) (u v : Card d) : ℝ :=
  match o u, o v with
  | some i, some j => if i = j then slotWeight o i else 0
  | _, _ => 0

end Thorp

end ThorpNine.Harmonic

end OAI
