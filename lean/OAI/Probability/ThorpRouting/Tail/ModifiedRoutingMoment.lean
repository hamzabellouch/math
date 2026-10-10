import Mathlib
import OAI.Probability.ThorpRouting.Tail.InputTree

namespace OAI

namespace ThorpNine.Tail

namespace Thorp

noncomputable def modifiedRoutingMoment (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) (a : ℝ) : ℝ := by
  classical
  exact finiteMean (fun ω : ModifiedCoins L r =>
    if ∀ i, modifiedPerm L r E ω (e i) = f i then (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a) else 0)

lemma modifiedRoutingMoment_nonneg (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) (a : ℝ) :
    0 ≤ modifiedRoutingMoment L r E e f a := by
  classical
  exact finiteMean_nonneg (fun _ => by split_ifs <;> positivity)

lemma modifiedRoutingMoment_zero (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (a : ℝ) :
    modifiedRoutingMoment L 0 E e f a = PairRouting.tupleProbability (modifiedPerm L 0 E) e f := by
  simp only [modifiedRoutingMoment,modifiedCost_zero,Nat.cast_zero,zero_mul,Real.rpow_zero,
    PairRouting.tupleProbability]

lemma modified_pointwise_zero (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (he : Function.Surjective e) (a : ℝ) (ha : 0 ≤ a) :
    (PairRouting.tupleProbability (modifiedPerm L 0 E) e f)^(1+a) ≤
      centralFactor L 0 E a * modifiedRoutingMoment L 0 E e f a := by
  have hp := PairRouting.tupleProbability_nonneg (modifiedPerm L 0 E) e f
  rw [modifiedRoutingMoment_zero]
  have hbound := modified_probability_zero_le L E e f he
  have hpow := Real.rpow_le_rpow hp hbound ha
  have hfpos : (0:ℝ) < Nat.factorial (2^L) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have heq : (if (fun j => Fin.elim0 j : Card 0) ∈ E then (1:ℝ) else 1/(Nat.factorial (2^L):ℝ))^a =
      centralFactor L 0 E a := by
    rw [centralFactor_zero]
    split_ifs
    · exact Real.one_rpow _
    · rw [one_div,Real.inv_rpow (le_of_lt hfpos),Real.rpow_neg (le_of_lt hfpos)]
  rw [heq] at hpow
  rw [Real.rpow_add' hp (by linarith : (1+a:ℝ) ≠ 0),Real.rpow_one,mul_comm]
  exact mul_le_mul_of_nonneg_right hpow hp


lemma modified_matches_step (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*}
    (e f : ι ↪ Card (L+r+1)) (ω : ModifiedCoins L r × ModifiedCoins L r)
    (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    (∀ i, modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) (e i) = f i) ↔
    (∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1))
      ((e.trans (headTailEquiv (L+r)).toEmbedding) i) = ((f.trans (headTailEquiv (L+r)).toEmbedding) i)) := by
  apply forall_congr'
  intro i
  rw [←(headTailEquiv (L+r)).injective.eq_iff,modifiedPerm_coordinates]
  rfl

lemma modifiedRoutingMoment_step (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : ι ↪ Card (L+r+1)) (a : ℝ) :
    let x := e.trans (headTailEquiv (L+r)).toEmbedding
    let y := f.trans (headTailEquiv (L+r)).toEmbedding
    modifiedRoutingMoment L (r+1) E e f a = PairRouting.outerWeight x y *
      ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
        finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((modifiedAssignmentCost L r E x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0) := by
  classical
  intro x y
  let : Fintype (ModifiedCoins L r) := inferInstance
  rw [modifiedRoutingMoment,finiteMean_equiv (modifiedStepEquiv L r),finiteMean_prod]
  have he (ω : ModifiedCoins L r × ModifiedCoins L r) :
      finiteMean (fun coins : (Card (L+r) → Bool) × (Card (L+r) → Bool) =>
        if ∀ i, modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) (e i) = f i
        then (2:ℝ)^((modifiedCost L (r+1) E e ((modifiedStepEquiv L r).symm (ω,coins)):ℝ)*a) else 0) =
      PairRouting.outerWeight x y *
        ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((modifiedAssignmentCost L r E x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0 := by
    let W : (ι → Bool) → ℝ := fun c =>
      if hc : PairRouting.Compatible x c then (2:ℝ)^((modifiedAssignmentCost L r E x c hc ω:ℝ)*a) else 0
    calc
      _ = finiteMean (fun coins : (Card (L+r) → Bool) × (Card (L+r) → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1))
          (x i) = y i then W (PairRouting.colors x coins.1) else 0) := by
        apply finiteMean_congr
        intro coins
        simp only [modified_matches_step,modifiedCost_step]
        simp only [W,PairRouting.colors_compatible,↓reduceDIte]
        rfl
      _ = _ := by
        rw [PairRouting.sandwich_weighted_probability_subtype]
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        simp only [W,((PairRouting.mem_compatibleSet x y c.val).mp c.property).1,↓reduceDIte]
  simp_rw [he]
  simp_rw [mul_comm (PairRouting.outerWeight x y)]
  rw [finiteMean_mul_const,finiteMean_sum,mul_comm]

lemma modified_child_moment_product (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι]
    (x y : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ) :
    modifiedRoutingMoment L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a *
      modifiedRoutingMoment L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a =
    finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
      if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
      then (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
        modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  classical
  unfold modifiedRoutingMoment
  rw [←finiteMean_prod_mul]
  apply finiteMean_congr
  intro ω
  let M₀ := ∀ i : {i // c i = false}, modifiedPerm L r (exceptionChild E false) ω.1 (x i.val).2 = (y i.val).2
  let M₁ := ∀ i : {i // c i = true}, modifiedPerm L r (exceptionChild E true) ω.2 (x i.val).2 = (y i.val).2
  have hp : (fun b : Bool => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) =
      (fun b => if b then modifiedPerm L r (exceptionChild E true) ω.2 else modifiedPerm L r (exceptionChild E false) ω.1) := by
    funext b
    cases b <;> rfl
  have hs : PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c ↔
      M₀ ∧ M₁ := by rw [hp]; exact PairRouting.childMatches_split _ _ _ _ _
  change (if M₀ then _ else 0) * (if M₁ then _ else 0) = _
  by_cases h₀ : M₀ <;> by_cases h₁ : M₁
  · simp only [hs,h₀,h₁,true_and,↓reduceIte]
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  · simp only [hs,h₀,h₁,and_false,↓reduceIte,mul_zero]
  · simp only [hs,h₀,h₁,false_and,↓reduceIte,zero_mul]
  · simp only [hs,h₀,h₁,false_and,↓reduceIte,mul_zero]

lemma modified_probability_step (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (L+r+1)) :
    PairRouting.tupleProbability (modifiedPerm L (r+1) E) e f =
    finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
      finiteMean (fun coins : (Card (L+r) → Bool) × (Card (L+r) → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => if b then modifiedPerm L r (exceptionChild E true) ω.2 else modifiedPerm L r (exceptionChild E false) ω.1)
          ((e.trans (headTailEquiv (L+r)).toEmbedding) i) = ((f.trans (headTailEquiv (L+r)).toEmbedding) i)
        then (1:ℝ) else 0)) := by
  classical
  let : Fintype (ModifiedCoins L r) := inferInstance
  rw [PairRouting.tupleProbability,finiteMean_equiv (modifiedStepEquiv L r),finiteMean_prod]
  have hp (b : Bool) (p q : ModifiedCoins L r) :
      modifiedPerm L r (exceptionChild E b) (if b then p else q) =
      (if b then modifiedPerm L r (exceptionChild E true) p else modifiedPerm L r (exceptionChild E false) q) := by
    cases b <;> rfl
  simp only [modified_matches_step,hp]


lemma modified_assignment_moment_bound (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι ↪ Bool × Card (L+r)) (c : ι → Bool) (hc : c ∈ PairRouting.compatibleSet x y)
    (a : ℝ) (ha : 0 ≤ a) :
    let hcx := ((PairRouting.mem_compatibleSet x y c).mp hc).1
    PairRouting.outerWeight x y ^ a * ((PairRouting.compatibleSet x y).card:ℝ)^a *
      ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a) *
        finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
          then (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0)) ≤
    (2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a) *
      finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
        if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^((modifiedAssignmentCost L r E x c hcx ω:ℝ)*a) else 0) := by
  classical
  intro hcx
  have hscale (q : ℝ) (F : ModifiedCoins L r × ModifiedCoins L r → ℝ) :
      q * finiteMean F = finiteMean (fun ω => q * F ω) := by
    simp_rw [mul_comm q,finiteMean_mul_const]
  rw [←mul_assoc,hscale,hscale]
  apply finiteMean_mono
  intro ω
  split_ifs with hm
  · have hh := PairRouting.assignment_factor_bound x y c hc
      (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) hm a ha
    calc
      _ ≤ ((2:ℝ)^(((PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hcx)
          (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)):ℝ)-Fintype.card ι)*a) *
          (2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)) *
          (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
      _ = _ := by
        simp only [←Real.rpow_add (by norm_num : (0:ℝ)<2),modifiedAssignmentCost,Nat.cast_add]
        congr 1
        ring
  · simp only [mul_zero]
    exact le_rfl


lemma modified_child_power_product_bound (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (x y : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ)
    (hfalse : (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E false))
        (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) ≤
      ((2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = false}*a)*centralFactor L r (exceptionChild E false) a) *
        modifiedRoutingMoment L r (exceptionChild E false)
          (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a)
    (htrue : (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E true))
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
      ((2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = true}*a)*centralFactor L r (exceptionChild E true) a) *
        modifiedRoutingMoment L r (exceptionChild E true)
          (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a) :
    (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E false))
      (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) *
      (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E true))
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
    ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)*centralFactor L (r+1) E a) *
      finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
        if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
          modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  have hh := mul_le_mul hfalse htrue
    (Real.rpow_nonneg (PairRouting.tupleProbability_nonneg _ _ _) _)
    (mul_nonneg (mul_nonneg (by positivity) (centralFactor_nonneg _ _ _ _))
      (modifiedRoutingMoment_nonneg _ _ _ _ _ _))
  have he : -(r:ℝ)*Fintype.card {i // c i = false}*a + -(r:ℝ)*Fintype.card {i // c i = true}*a =
      -(r:ℝ)*Fintype.card ι*a := by
    rw [←add_mul,←mul_add,←Nat.cast_add,PairRouting.color_card_add]
  calc
    _ ≤ _ := hh
    _ = ((2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = false}*a)*
        (2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = true}*a)) *
      (centralFactor L r (exceptionChild E false) a * centralFactor L r (exceptionChild E true) a) *
      (modifiedRoutingMoment L r (exceptionChild E false)
        (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a *
      modifiedRoutingMoment L r (exceptionChild E true)
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a) := by ring
    _ = _ := by rw [←Real.rpow_add (by norm_num : (0:ℝ)<2),he,←centralFactor_step,modified_child_moment_product]


theorem modified_pointwise_moment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (L+r)) (he : Function.Surjective e) (a : ℝ) (ha : 0 ≤ a) :
    (PairRouting.tupleProbability (modifiedPerm L r E) e f)^(1+a) ≤
      ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)*centralFactor L r E a) * modifiedRoutingMoment L r E e f a := by
  classical
  induction r generalizing ι with
  | zero =>
      simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.rpow_zero,one_mul] using
        modified_pointwise_zero L E e f he a ha
  | succ r ih =>
      let x := e.trans (headTailEquiv (L+r)).toEmbedding
      let y := f.trans (headTailEquiv (L+r)).toEmbedding
      let W := PairRouting.outerWeight x y
      let C := PairRouting.compatibleSet x y
      let p : (ι → Bool) → ℝ := fun c =>
        (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E false))
          (fun i : {i // c i = false} => (x i.val).2)
          (fun i : {i // c i = false} => (y i.val).2))^(1+a) *
        (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E true))
          (fun i : {i // c i = true} => (x i.val).2)
          (fun i : {i // c i = true} => (y i.val).2))^(1+a)
      let m : {c // c ∈ C} → ℝ := fun c =>
        finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((modifiedAssignmentCost L r E x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0)
      have hp (c : {c // c ∈ C}) : W^a * (C.card:ℝ)^a * p c.val ≤
          ((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * m c := by
        obtain ⟨hcx,hcy⟩ := (PairRouting.mem_compatibleSet x y c.val).mp c.property
        have h₀ := ih (exceptionChild E false) (PairRouting.childEmbedding x c.val hcx false)
          (PairRouting.childEmbedding y c.val hcy false)
          (PairRouting.childEmbedding_surjective x ((headTailEquiv (L+r)).surjective.comp he) c.val hcx false)
        have h₁ := ih (exceptionChild E true) (PairRouting.childEmbedding x c.val hcx true)
          (PairRouting.childEmbedding y c.val hcy true)
          (PairRouting.childEmbedding_surjective x ((headTailEquiv (L+r)).surjective.comp he) c.val hcx true)
        have hh := modified_child_power_product_bound L r E x y c.val hcx hcy a h₀ h₁
        have hh' := mul_le_mul_of_nonneg_left hh
          (mul_nonneg (Real.rpow_nonneg (le_of_lt (PairRouting.outerWeight_pos x y)) a)
            (Real.rpow_nonneg (Nat.cast_nonneg C.card) a))
        apply hh'.trans
        have hm := modified_assignment_moment_bound L r E x y c.val c.property a ha
        convert mul_le_mul_of_nonneg_left hm (centralFactor_nonneg L (r+1) E a) using 1 <;> ring
      have hnode := PairRouting.sandwich_power_bound (modifiedPerm L r (exceptionChild E false)) (modifiedPerm L r (exceptionChild E true)) x y a ha
      rw [←modified_probability_step L r E e f] at hnode
      change (PairRouting.tupleProbability (modifiedPerm L (r+1) E) e f)^(1+a) ≤
        W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c at hnode
      have hsum : ∑ c ∈ C, p c = ∑ c : {c // c ∈ C}, p c.val := by
        rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
      have hW : 0 < W := PairRouting.outerWeight_pos x y
      calc
        _ ≤ W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c := hnode
        _ = W * ∑ c : {c // c ∈ C}, W^a * (C.card:ℝ)^a * p c.val := by
          rw [Real.rpow_add hW,Real.rpow_one,hsum,←Finset.mul_sum]
          ring
        _ ≤ W * ∑ c : {c // c ∈ C}, ((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * m c :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hp c)) (le_of_lt hW)
        _ = _ := by
          rw [←Finset.mul_sum,modifiedRoutingMoment_step]
          simp only [Nat.cast_add,Nat.cast_one]
          change W * (((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * ∑ c, m c) =
            ((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * (W * ∑ c, m c)
          ring


lemma modifiedRoutingMoment_sum (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (a : ℝ) :
    (∑ f : ι ↪ Card (L+r), modifiedRoutingMoment L r E e f a) =
      finiteMean (fun ω : ModifiedCoins L r => (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a)) := by
  classical
  unfold modifiedRoutingMoment
  rw [←finiteMean_sum]
  apply finiteMean_congr
  intro ω
  let f₀ : ι ↪ Card (L+r) := e.trans (modifiedPerm L r E ω).toEmbedding
  rw [Finset.sum_eq_single f₀]
  · have hm : ∀ i, modifiedPerm L r E ω (e i) = f₀ i := fun _ => rfl
    simp only [hm,implies_true,↓reduceIte]
  · intro f _ hf
    have hm : ¬ ∀ i, modifiedPerm L r E ω (e i) = f i := by
      intro hh
      apply hf
      ext i : 1
      exact (hh i).symm
    exact ite_eq_right hm
  · simp

noncomputable def modifiedRowMoment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (a : ℝ) : ℝ :=
  finiteMean (fun f : ι ↪ Card (L+r) =>
    ((Fintype.card (ι ↪ Card (L+r)):ℝ)*PairRouting.tupleProbability (modifiedPerm L r E) e f)^(1+a))

lemma full_tuple_card (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (he : Function.Surjective e) : Fintype.card ι = 2^d := by
  rw [←card_positions d]
  exact Fintype.card_congr (Equiv.ofBijective e ⟨e.injective,he⟩)

lemma exception_card_le (r : ℕ) (E : Finset (Card r)) : E.card ≤ 2^r := by
  simpa only [card_positions] using E.card_le_univ

noncomputable def modifiedNormalization (L r : ℕ) (E : Finset (Card r)) : ℝ :=
  (Nat.factorial (2^(L+r)):ℝ) /
    (((2:ℝ)^r)^(2^(L+r)) * (Nat.factorial (2^L):ℝ)^(2^r-E.card))

lemma modifiedNormalization_pos (L r : ℕ) (E : Finset (Card r)) :
    0 < modifiedNormalization L r E := by unfold modifiedNormalization; positivity

lemma modified_normalization_identity (L r : ℕ) (E : Finset (Card r)) (a : ℝ) :
    (Nat.factorial (2^(L+r)):ℝ)^a *
      ((2:ℝ)^(-(r:ℝ)*(2^(L+r):ℕ)*a)*centralFactor L r E a) =
    modifiedNormalization L r E ^ a := by
  rw [←mul_assoc,density_normalization,centralFactor,modifiedNormalization,
    Real.div_rpow (by positivity) (by positivity),Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  have hc : ((2^r-E.card:ℕ):ℝ) = (2:ℝ)^r-E.card := by
    rw [Nat.cast_sub (exception_card_le r E),Nat.cast_pow,Nat.cast_ofNat]
  rw [←Real.rpow_natCast (Nat.factorial (2^L):ℝ),←Real.rpow_mul (by positivity),hc,
    show -((2:ℝ)^r-E.card)*a = -(((2:ℝ)^r-E.card)*a) by ring,
    Real.rpow_neg (by positivity)]
  ring

theorem modified_row_density_moment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (he : Function.Surjective e) (a : ℝ) (ha : 0 ≤ a) :
    modifiedRowMoment L r E e a ≤ modifiedNormalization L r E ^ a *
      finiteMean (fun ω : ModifiedCoins L r => (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a)) := by
  classical
  have : Nonempty (ι ↪ Card (L+r)) := ⟨e⟩
  rw [modifiedRowMoment,finite_row_power _ (fun f => PairRouting.tupleProbability_nonneg _ _ _)]
  calc
    _ ≤ (Fintype.card (ι ↪ Card (L+r)):ℝ)^a *
      ∑ f : ι ↪ Card (L+r), ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)*centralFactor L r E a) *
        modifiedRoutingMoment L r E e f a :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun f _ => modified_pointwise_moment L r E e f he a ha))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by
      rw [←Finset.mul_sum,modifiedRoutingMoment_sum,←mul_assoc,Fintype.card_embedding_eq,
        card_positions,full_tuple_card (L+r) e he,Nat.descFactorial_self,modified_normalization_identity]

lemma modified_total_cost_mgf (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) :
    finiteMean (fun ω : ModifiedCoins L r => momentBase^(modifiedCost L r E e ω)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase) := by
  let B := Real.exp (Fintype.card ι*heightDecay L +
    3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase)
  rw [finiteMean_prod]
  apply le_trans (finiteMean_mono (fun U => ?_)) (finiteMean_const B).le
  rw [finiteMean_prod,finiteMean_comm]
  apply le_trans (finiteMean_mono (fun X => ?_)) (finiteMean_const B).le
  exact modified_cost_mgf L r hL E U X e momentBase momentBase_one_le (momentBase_log.trans (by norm_num))

lemma modifiedRowMoment_bound (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (he : Function.Surjective e) :
    modifiedRowMoment L r E e (1/1000) ≤
      modifiedNormalization L r E ^ (1/1000:ℝ) *
        Real.exp ((2^(L+r):ℕ)*heightDecay L +
          3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase) := by
  have hm := modified_row_density_moment L r E e he (1/1000) (by norm_num)
  simp_rw [←momentBase_pow] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (modifiedNormalization_pos L r E).le _)
  simpa only [full_tuple_card (L+r) e he] using modified_total_cost_mgf L r hL E e


lemma log_factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n) ≤ (n:ℝ)*Real.log n-n+Real.log n+1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hz : n = 0
      · subst n; norm_num
      have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
      have hn1 : (0:ℝ) < n+1 := by positivity
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn0)
      rw [Real.log_div (ne_of_gt hn1) (ne_of_gt hn0),inv_div] at h
      have hh := mul_le_mul_of_nonneg_left h hn1.le
      have hcancel : ((n:ℝ)+1)*(1-(n:ℝ)/(n+1)) = 1 := by field_simp; ring
      rw [hcancel] at hh
      have hi := ih (by omega)
      rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
      nlinarith

lemma log_modifiedNormalization (L r : ℕ) (E : Finset (Card r)) :
    Real.log (modifiedNormalization L r E) =
      Real.log (Nat.factorial (2^(L+r))) -
        ((2^(L+r):ℕ)*((r:ℝ)*Real.log 2)+((2:ℝ)^r-E.card)*Real.log (Nat.factorial (2^L))) := by
  unfold modifiedNormalization
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow,
    Nat.cast_sub (exception_card_le r E),Nat.cast_pow,Nat.cast_ofNat]
  simp only [Nat.cast_pow,Nat.cast_ofNat]

lemma log_modifiedNormalization_le (L r : ℕ) (E : Finset (Card r)) :
    Real.log (modifiedNormalization L r E) ≤
      ((L+r:ℕ):ℝ)*Real.log 2+1+E.card*Real.log (Nat.factorial (2^L)) := by
  have hN : 1 ≤ 2^(L+r) := one_le_pow₀ (by norm_num)
  have hS : 1 ≤ 2^L := one_le_pow₀ (by norm_num)
  have hu := log_factorial_upper hN
  have hl := mul_le_mul_of_nonneg_left (log_factorial_lower hS) (by positivity : (0:ℝ) ≤ (2:ℝ)^r)
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add] at hu hl ⊢
  rw [log_modifiedNormalization]
  simp only [pow_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hu hl ⊢
  nlinarith

lemma modified_moment_exponential (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (he : Function.Surjective e) :
    modifiedRowMoment L r E e (1/1000) ≤
      Real.exp (((L+r:ℕ)*Real.log 2+1+E.card*Real.log (Nat.factorial (2^L)))/1000 +
        (2^(L+r):ℕ)*heightDecay L+3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase) := by
  apply (modifiedRowMoment_bound L r hL E e he).trans
  rw [Real.rpow_def_of_pos (modifiedNormalization_pos L r E),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := log_modifiedNormalization_le L r E
  linarith

lemma log_power_factorial_le (L : ℕ) :
    Real.log (Nat.factorial (2^L)) ≤ (2:ℝ)^L*L := by
  have hf : (Nat.factorial (2^L):ℝ) ≤ ((2^L:ℕ):ℝ)^(2^L) := by
    exact_mod_cast Nat.factorial_le_pow (2^L)
  have hh := Real.log_le_log (by positivity) hf
  rw [Real.log_pow,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
  apply hh.trans
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hn : 0 ≤ (2:ℝ)^L*(L:ℝ) := by positivity
  nlinarith

lemma modified_moment_exception_bound (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (he : Function.Surjective e)
    (ε : ℝ) (hE : (E.card:ℝ) ≤ ε*(2:ℝ)^r) :
    modifiedRowMoment L r E e (1/1000) ≤
      Real.exp (((L+r:ℕ)*Real.log 2+1)/1000 +
        (2:ℝ)^(L+r)*(heightDecay L+ε*L/250)) := by
  apply (modified_moment_exponential L r hL E e he).trans
  apply Real.exp_le_exp.mpr
  have hs := mul_le_mul_of_nonneg_left (log_power_factorial_le L) (Nat.cast_nonneg E.card)
  have hb := mul_le_mul_of_nonneg_left momentBase_log
    (by positivity : (0:ℝ) ≤ 3*((L*E.card*2^L:ℕ):ℝ))
  have hexc := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ (2:ℝ)^L*L/250)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add] at hs hb hexc ⊢
  nlinarith


lemma heightDecay_tendsto : Filter.Tendsto heightDecay Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun L : ℕ => (-(1:ℝ)/64)*(L:ℝ)) Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (by norm_num : -(1:ℝ)/64 < 0)).mpr
      tendsto_natCast_atTop_atTop
  have ht := ((Real.tendsto_exp_atBot.comp h).const_mul 68).div_const (1-Real.exp (-(1:ℝ)/64))
  convert ht using 1
  · funext L
    unfold heightDecay
    dsimp only [Function.comp_apply]
    rw [show -(L:ℝ)/64 = (-(1:ℝ)/64)*(L:ℝ) by ring]
  · simp

noncomputable def modifiedOverhead (L r : ℕ) : ℝ :=
  (((L+r:ℕ):ℝ)*Real.log 2+1)/((2:ℝ)^(L+r)*1000)

lemma modifiedOverhead_tendsto (L : ℕ) :
    Filter.Tendsto (modifiedOverhead L) Filter.atTop (nhds 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  simp only [pow_one] at h₁
  simp only [pow_zero] at h₀
  have ht := ((h₁.const_mul (Real.log 2)).add (h₀.const_mul ((L:ℝ)*Real.log 2+1))).div_const
    ((2:ℝ)^L*1000)
  convert ht using 1
  · funext r
    simp only [modifiedOverhead,Nat.cast_add,pow_add]
    field_simp
    ring
  · simp

theorem modified_arbitrarily_small_rate (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧
      ∀ᶠ r : ℕ in Filter.atTop, ∀ (E : Finset (Card r)), (E.card:ℝ) ≤ ε*(2:ℝ)^r →
        ∀ (e : Card (L+r) ↪ Card (L+r)),
          modifiedRowMoment L r E e (1/1000) ≤ Real.exp (η*(2:ℝ)^(L+r)) := by
  have hsmall : ∀ᶠ L : ℕ in Filter.atTop, heightDecay L < η/3 :=
    heightDecay_tendsto.eventually (gt_mem_nhds (by linarith : (0:ℝ)<η/3))
  obtain ⟨L,hdec,hL⟩ := (hsmall.and (Filter.eventually_ge_atTop 1)).exists
  have hL0 : (0:ℝ) < L := Nat.cast_pos.mpr hL
  let ε : ℝ := min (1/4) (η*250/(3*L))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεL : ε*L/250 ≤ η/3 := by
    have h := min_le_right (1/4:ℝ) (η*250/(3*L))
    change ε ≤ η*250/(3*L) at h
    have hh := mul_le_mul_of_nonneg_right h hL0.le
    have he : (η*250/(3*(L:ℝ)))*(L:ℝ)/250 = η/3 := by field_simp
    exact (div_le_div_of_nonneg_right hh (by norm_num)).trans he.le
  refine ⟨L,hL,ε,hε,hε1,?_⟩
  have hr : ∀ᶠ r : ℕ in Filter.atTop, modifiedOverhead L r < η/3 :=
    (modifiedOverhead_tendsto L).eventually (gt_mem_nhds (by linarith : (0:ℝ)<η/3))
  filter_upwards [hr] with r hr
  intro E hE e
  have he := Finite.surjective_of_injective e.injective
  apply (modified_moment_exception_bound L r hL E e he ε hE).trans
  apply Real.exp_le_exp.mpr
  have hn : (0:ℝ) < (2:ℝ)^(L+r) := by positivity
  have hd : modifiedOverhead L r * (2:ℝ)^(L+r) =
      (((L+r:ℕ):ℝ)*Real.log 2+1)/1000 := by
    unfold modifiedOverhead
    field_simp
  have hh := mul_le_mul_of_nonneg_right hr.le hn.le
  rw [hd] at hh
  have ht := mul_le_mul_of_nonneg_left (show heightDecay L+ε*L/250 ≤ 2*η/3 by linarith) hn.le
  linarith


namespace DensityTransfer
open scoped BigOperators

noncomputable def applyKernel {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)

lemma applyKernel_apply {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) (x : X) :
    applyKernel P v x = ∑ y, (P x y : ℂ)*v y := rfl

lemma applyKernel_add {X : Type*} [Fintype X] (P Q : X → X → ℝ)
    (v : EuclideanSpace ℂ X) :
    applyKernel (fun x y => P x y+Q x y) v = applyKernel P v+applyKernel Q v := by
  ext x
  simp only [applyKernel_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]
  rfl

lemma kernel_component_sq {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (v : EuclideanSpace ℂ X) (x : X) :
    ‖applyKernel P v x‖^2 ≤ (∑ y, P x y) * ∑ y, P x y*‖v y‖^2 := by
  have hs : ‖applyKernel P v x‖ ≤ ∑ y, P x y*‖v y‖ := by
    rw [applyKernel_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro y _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hP x y)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun y _ => hP x y) (fun y _ => mul_nonneg (hP x y) (sq_nonneg _))
    (fun y _ => by ring_nf; exact le_rfl)

lemma schur_bound {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ x, ∑ y, P x y ≤ δ) (hcol : ∀ y, ∑ x, P x y ≤ δ)
    (v : EuclideanSpace ℂ X) : ‖applyKernel P v‖ ≤ δ*‖v‖ := by
  have hsq : ‖applyKernel P v‖^2 ≤ δ^2*‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ x, δ * ∑ y, P x y*‖v y‖^2 := by
        apply Finset.sum_le_sum
        intro x _
        apply (kernel_component_sq P hP v x).trans
        exact mul_le_mul_of_nonneg_right (hrow x)
          (Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (sq_nonneg _)))
      _ = δ * ∑ y, (∑ x, P x y)*‖v y‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        exact (Finset.sum_mul Finset.univ _ _).symm
      _ ≤ δ * ∑ y, δ*‖v y‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _))
      _ = _ := by rw [←Finset.mul_sum]; ring
  have hn := norm_nonneg (applyKernel P v)
  have hr := mul_nonneg hδ (norm_nonneg v)
  nlinarith

lemma hilbert_schmidt_family {X I : Type*} [Fintype X] [Fintype I]
    (P : X → X → ℝ) (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v) :
    (∑ i, ‖applyKernel P (v i)‖^2) ≤ ∑ x, ∑ y, (P x y)^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  let w : EuclideanSpace ℂ X := WithLp.toLp 2 (fun y => (P x y : ℂ))
  have he (i : I) : ‖applyKernel P (v i) x‖ = ‖inner ℂ (v i) w‖ := by
    rw [norm_inner_symm]
    congr 1
    simp only [applyKernel_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp [w,RCLike.inner_apply,mul_comm]
  simp_rw [he]
  have h := hv.sum_inner_products_le (s := Finset.univ) w
  apply h.trans_eq
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro y _
  simp [w,Complex.norm_real,Real.norm_eq_abs,sq_abs]


lemma tail_density_pointwise (t a z : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hz : 0 < z) :
    (if z < t then t else 0) ≤ t^(1+a)*z^(-a) := by
  split_ifs with h
  · rw [Real.rpow_neg hz.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz a)).mpr
    rw [Real.rpow_add (lt_trans hz h),Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.le h.le ha) ht
  · positivity

lemma tail_density_mean {X : Type*} [Fintype X] (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a z : ℝ) (ha : 0 ≤ a) (hz : 0 < z) :
    finiteMean (fun x => if z < f x then f x else 0) ≤ finiteMean (fun x => f x^(1+a))*z^(-a) := by
  rw [←finiteMean_mul_const]
  exact finiteMean_mono (fun x => tail_density_pointwise (f x) a z (hf x) ha hz)

noncomputable def tailKernel {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) : X → X → ℝ :=
  fun x y => if z < (Fintype.card X:ℝ)*P x y then P x y else 0

noncomputable def headKernel {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) : X → X → ℝ :=
  fun x y => if z < (Fintype.card X:ℝ)*P x y then 0 else P x y

lemma tail_add_head {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) :
    (fun x y => tailKernel P z x y+headKernel P z x y) = P := by
  funext x y
  unfold tailKernel headKernel
  split_ifs <;> simp

lemma tailKernel_nonneg {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) : 0 ≤ tailKernel P z x y := by
  unfold tailKernel
  split_ifs <;> simp only [hP,le_refl]

lemma tailKernel_row {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M) (x : X) :
    ∑ y, tailKernel P z x y ≤ M*z^(-a) := by
  have hn : (Fintype.card X:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : finiteMean (fun y => if z < (Fintype.card X:ℝ)*P x y then
      (Fintype.card X:ℝ)*P x y else 0) = ∑ y, tailKernel P z x y := by
    unfold finiteMean
    calc
      _ = (∑ y, (Fintype.card X:ℝ)*tailKernel P z x y)/(Fintype.card X:ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : z < (Fintype.card X:ℝ)*P x y
        · simp only [tailKernel,hy,↓reduceIte]
        · simp only [tailKernel,hy,↓reduceIte,mul_zero]
      _ = _ := by rw [←Finset.mul_sum]; field_simp
  rw [←he]
  exact (tail_density_mean _ (fun y => mul_nonneg (Nat.cast_nonneg _) (hP x y)) a z ha hz).trans
    (mul_le_mul_of_nonneg_right (hM x) (Real.rpow_nonneg hz.le _))

lemma tailKernel_schur {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : EuclideanSpace ℂ X) :
    ‖applyKernel (tailKernel P z) v‖ ≤ (M*z^(-a))*‖v‖ := by
  apply schur_bound _ (tailKernel_nonneg P z hP) _ (by positivity)
    (tailKernel_row P hP a z M ha hz hM)
  intro y
  have hs : (fun x => tailKernel P z x y) = (fun x => tailKernel P z y x) := by
    funext x
    simp only [tailKernel,hsym x y]
  rw [hs]
  exact tailKernel_row P hP a z M ha hz hM y

lemma headKernel_hs {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (z : ℝ) (hz : 0 ≤ z) :
    (∑ x, ∑ y, (headKernel P z x y)^2) ≤ z := by
  have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have he (x y : X) : (headKernel P z x y)^2 ≤ (z/(Fintype.card X:ℝ))*P x y := by
    unfold headKernel
    split_ifs with h
    · simp only [zero_pow (by omega : (2:ℕ) ≠ 0)]
      exact mul_nonneg (div_nonneg hz hn.le) (hP x y)
    · have h' : (Fintype.card X:ℝ)*P x y ≤ z := le_of_not_gt h
      have hh := mul_le_mul_of_nonneg_right h' (hP x y)
      rw [show (z/(Fintype.card X:ℝ))*P x y = (z*P x y)/(Fintype.card X:ℝ) by ring]
      apply (le_div_iff₀ hn).mpr
      nlinarith
  calc
    _ ≤ ∑ x, ∑ y, (z/(Fintype.card X:ℝ))*P x y :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => he x y))
    _ = z := by
      simp only [←Finset.mul_sum,hrow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp


theorem multiplicity_amplification {X I : Type*} [Fintype X] [Nonempty X]
    [Fintype I] [Nonempty I] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (hrow : ∀ x, ∑ y, P x y = 1) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v)
    (μ : ℝ) (hvμ : ∀ i, μ ≤ ‖applyKernel P (v i)‖) :
    μ ≤ M*z^(-a)+Real.sqrt (z/(Fintype.card I:ℝ)) := by
  let δ : ℝ := M*z^(-a)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hm : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  change μ ≤ δ+_
  by_cases hμ : μ ≤ δ
  · exact hμ.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hmd : 0 ≤ μ-δ := by linarith
  have hsmall (i : I) : μ-δ ≤ ‖applyKernel (headKernel P z) (v i)‖ := by
    have hr := tailKernel_schur P hP hsym a z M ha hz hM0 hM (v i)
    rw [hv.norm_eq_one i,mul_one] at hr
    have he := applyKernel_add (tailKernel P z) (headKernel P z) (v i)
    rw [tail_add_head] at he
    have hn := norm_add_le (applyKernel (tailKernel P z) (v i)) (applyKernel (headKernel P z) (v i))
    rw [←he] at hn
    have hh := hvμ i
    change ‖applyKernel (tailKernel P z) (v i)‖ ≤ δ at hr
    linarith
  have hsum : (Fintype.card I:ℝ)*(μ-δ)^2 ≤ z := by
    calc
      _ = ∑ i : I, (μ-δ)^2 := by simp
      _ ≤ ∑ i : I, ‖applyKernel (headKernel P z) (v i)‖^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hmd (hsmall i) 2)
      _ ≤ ∑ x, ∑ y, (headKernel P z x y)^2 := hilbert_schmidt_family _ v hv
      _ ≤ z := headKernel_hs P hP hrow z hz.le
  have hsq : (μ-δ)^2 ≤ z/(Fintype.card I:ℝ) := (le_div_iff₀ hm).mpr (by nlinarith)
  have hs := (Real.le_sqrt hmd (div_nonneg hz.le hm.le)).mpr hsq
  linarith

end DensityTransfer
namespace PairRouting
open scoped BigOperators

lemma tupleProbability_row_sum {ι β Ω : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] [Fintype Ω] [Nonempty Ω]
    (P : Ω → Equiv.Perm β) (e : ι ↪ β) :
    (∑ f : ι ↪ β, tupleProbability P e f) = 1 := by
  classical
  simp only [tupleProbability]
  rw [←finiteMean_sum]
  have h (ω : Ω) (f : ι ↪ β) : (∀ i, P ω (e i) = f i) ↔ e.trans (P ω).toEmbedding = f := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congrArg (fun g : ι ↪ β => g i) h
  simp_rw [h]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

lemma tupleProbability_inverse {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (e f : ι → β) :
    tupleProbability (fun ω => (P ω)⁻¹) e f = tupleProbability P f e := by
  classical
  apply finiteMean_congr
  intro ω
  congr 1
  apply propext
  constructor
  · intro h i
    have hh := congrArg (P ω) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm
  · intro h i
    have hh := congrArg (fun x => (P ω).symm x) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm

lemma tupleProbability_equiv {ι β Ω Ω' : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] [Fintype Ω'] (P : Ω → Equiv.Perm β) (τ : Ω ≃ Ω') (e f : ι → β) :
    tupleProbability P e f = tupleProbability (fun ω => P (τ.symm ω)) e f :=
  finiteMean_equiv τ _

lemma tupleProbability_symmetric {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (τ : Equiv.Perm Ω)
    (hτ : ∀ ω, P (τ ω) = (P ω)⁻¹) (e f : ι → β) :
    tupleProbability P e f = tupleProbability P f e := by
  rw [tupleProbability_equiv P τ.symm]
  simp only [Equiv.symm_symm,hτ]
  exact tupleProbability_inverse P e f

end PairRouting

lemma palindromePerm_reverse (d : ℕ) (ω : BenesCoins d) :
    palindromePerm d (ω.2,ω.1) = (palindromePerm d ω)⁻¹ := by
  simp only [palindromePerm,mul_inv_rev]
  rfl

lemma palindrome_kernel_symmetric (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) :
    PairRouting.tupleProbability (palindromePerm d) e f =
      PairRouting.tupleProbability (palindromePerm d) f e :=
  PairRouting.tupleProbability_symmetric _ (Equiv.prodComm _ _) (palindromePerm_reverse d) e f

theorem palindrome_density_transfer (d : ℕ) {ι I : Type*} [Fintype ι] [Fintype I]
    [Nonempty I] (e₀ : ι ↪ Card d) (hk : 0 < Fintype.card ι)
    (v : I → EuclideanSpace ℂ (ι ↪ Card d)) (hv : Orthonormal ℂ v)
    (μ : ℝ) (hvμ : ∀ i, μ ≤ ‖DensityTransfer.applyKernel
      (fun e f : ι ↪ Card d => PairRouting.tupleProbability (palindromePerm d) e f) (v i)‖)
    (z : ℝ) (hz : 0 < z) :
    μ ≤ Real.exp (densityConstant*Fintype.card ι*
      ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*z^(-(1/1000:ℝ))+
      Real.sqrt (z/(Fintype.card I:ℝ)) := by
  let : Nonempty (ι ↪ Card d) := ⟨e₀⟩
  apply DensityTransfer.multiplicity_amplification
    (fun e f : ι ↪ Card d => PairRouting.tupleProbability (palindromePerm d) e f)
    (fun e f => PairRouting.tupleProbability_nonneg _ e f)
    (palindrome_kernel_symmetric d) (PairRouting.tupleProbability_row_sum _)
    (1/1000) z _ (by norm_num) hz (Real.exp_nonneg _) _ v hv μ hvμ
  intro e
  exact palindrome_row_moment_bound d e hk


noncomputable def modifiedReverseCoins (L : ℕ) : (r : ℕ) → ModifiedCoins L r → ModifiedCoins L r
  | 0, ω => ((fun u => butterflyPerm L (decodeButterfly L ω.2.1) * (ω.1 u)⁻¹ *
      butterflyPerm L (decodeButterfly L ω.2.1)),ω.2)
  | r+1, ω =>
      let z := modifiedStepEquiv L r ω
      (modifiedStepEquiv L r).symm
        ((modifiedReverseCoins L r z.1.1,modifiedReverseCoins L r z.1.2),(z.2.2,z.2.1))

lemma modifiedReverseCoins_involutive (L r : ℕ) :
    Function.Involutive (modifiedReverseCoins L r) := by
  induction r with
  | zero =>
      intro ω
      apply Prod.ext
      · funext u
        simp only [modifiedReverseCoins,mul_inv_rev,inv_inv]
        simp [mul_assoc]
      · rfl
  | succ r ih =>
      change ∀ ω, modifiedReverseCoins L r (modifiedReverseCoins L r ω) = ω at ih
      intro ω
      simp only [modifiedReverseCoins,Equiv.apply_symm_apply,ih]
      exact (modifiedStepEquiv L r).symm_apply_apply ω

end Thorp

end ThorpNine.Tail

end OAI
