import OAI.Probability.CubeShuffle.Coin

namespace OAI

namespace CubeShuffle

open scoped BigOperators
open Filter

/-- One index for each independent coin of the recursive butterfly. -/
def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

/-- Decode an independent bit at every switch into the actual routing object. -/
def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

def encodeButterfly : (d : ℕ) → Butterfly d → SwitchIndex d → Bool
  | 0, _, i => nomatch i
  | _d + 1, b, Sum.inl y => b.1 y
  | d + 1, b, Sum.inr (ε,i) => encodeButterfly d (b.2 ε) i

lemma decode_encodeButterfly (d : ℕ) (b : Butterfly d) :
    decodeButterfly d (encodeButterfly d b) = b := by
  induction d with
  | zero => exact Unit.ext _ _
  | succ d ih =>
    apply Prod.ext
    · rfl
    · funext ε
      exact ih (b.2 ε)

lemma encode_decodeButterfly (d : ℕ) (ω : SwitchIndex d → Bool) :
    encodeButterfly d (decodeButterfly d ω) = ω := by
  induction d with
  | zero => funext i; exact Empty.elim i
  | succ d ih =>
    funext i
    cases i with
    | inl y => rfl
    | inr z => exact congrFun (ih (fun i => ω (Sum.inr (z.1,i)))) z.2

/-- Thus the bit experiment and independent recursive butterfly experiment
are exactly the same finite probability space, up to a bijection. -/
def butterflyCoinEquiv (d : ℕ) : (SwitchIndex d → Bool) ≃ Butterfly d where
  toFun := decodeButterfly d
  invFun := encodeButterfly d
  left_inv := encode_decodeButterfly d
  right_inv := decode_encodeButterfly d

/-- Switches on the unique possible route from `x` to `y`. -/
noncomputable def routeDomain : (d : ℕ) → Card d → Card d → Finset (SwitchIndex d)
  | 0, _, _ => ∅
  | d + 1, x, y => by
      classical
      exact insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image (fun i => Sum.inr (x 0,i)))

/-- Required coin values on the unique route. Values off its domain are unused. -/
def routeValue : (d : ℕ) → Card d → Card d → SwitchIndex d → Bool
  | 0, _, _, i => nomatch i
  | _d + 1, x, y, Sum.inl _ => Bool.xor (x 0) (y 0)
  | d + 1, x, y, Sum.inr (_,i) => routeValue d (Fin.tail x) (Fin.tail y) i

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

/-- The endpoint test is exactly a fixed set of coin requirements. The route
is UNIQUE; there is no sum over paths and no adaptively unspecified target. -/
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

/-- Exact probability of any prescribed collection of independent fair bits. -/
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

/-- Fix all previously exposed bits, leaving every other bit independent fair. -/
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

/-- Literal source closing-path formula: zero on inconsistent exposures,
otherwise `2^u/n`, with `u` the number of already exposed route switches and
`n = 2^d`. There is no supposition that a favorable route is independent. -/
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


/-- The two distinct INPUT labels whose paths traverse a given switch. This
records encounters without any independence or random-route assumption. -/
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

/-- A switch is on a label's actual route iff the label is one of its two
users. In particular all incidental meetings are accounted for exactly once. -/
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

/-- Every input path has degree exactly `d` in the multigraph of shared
switches. The identity also holds for arbitrary (not necessarily positive)
weights. -/
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

/-- The weighted threshold estimate in the rotation argument. It applies
to any weights and so in particular to `1/j` on selected length-j cycles. -/
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

/-- Both users marked is exactly the encounter predicate; its sum is the
recursive quantity already bounded by entropy. -/
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

end CubeShuffle

end OAI
