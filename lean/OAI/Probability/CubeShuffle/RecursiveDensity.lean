import OAI.Probability.CubeShuffle.PairRouting
import OAI.Probability.CubeShuffle.ParallelLayers

namespace OAI

namespace CubeShuffle

open scoped BigOperators
open Filter

noncomputable def assignmentCost (d : ℕ) {ι : Type*} [Fintype ι]
    (x : ι ↪ Bool × Card d) (c : ι → Bool) (hc : PairRouting.Compatible x c)
    (ω : BenesCoins d × BenesCoins d) : ℕ :=
  PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hc)
      (fun b => palindromePerm d (if b then ω.2 else ω.1)) +
    palindromeCost d (PairRouting.childEmbedding x c hc false) ω.1 +
    palindromeCost d (PairRouting.childEmbedding x c hc true) ω.2

lemma palindromeCost_eq (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (σ : BenesCoins (d+1)) :
    palindromeCost (d+1) e σ =
      assignmentCost d (e.trans (headTailEquiv d).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) (benesStepEquiv d σ).2.1)
        (PairRouting.colors_compatible _ _) (benesStepEquiv d σ).1 := by
  unfold palindromeCost assignmentCost
  dsimp only
  rw [PairRouting.switchedEmbedding_eq_colored _ _ (PairRouting.colors_compatible _ _) _ rfl]

lemma palindromeCost_step (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (ω : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) :
    palindromeCost (d+1) e ((benesStepEquiv d).symm (ω,coins)) =
      assignmentCost d (e.trans (headTailEquiv d).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) coins.1)
        (PairRouting.colors_compatible _ _) ω := by
  rw [palindromeCost_eq]
  simp only [Equiv.apply_symm_apply]

noncomputable def routingMoment (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) : ℝ := by
  classical
  exact finiteMean (fun ω : BenesCoins d =>
    if ∀ i, palindromePerm d ω (e i) = f i then (2:ℝ)^((palindromeCost d e ω:ℝ)*a) else 0)

lemma routingMoment_nonneg (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) : 0 ≤ routingMoment d e f a := by
  classical
  exact finiteMean_nonneg (fun _ => by split_ifs <;> positivity)

lemma palindrome_matches_step (d : ℕ) {ι : Type*}
    (e f : ι ↪ Card (d+1)) (ω : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) :
    (∀ i, palindromePerm (d+1) ((benesStepEquiv d).symm (ω,coins)) (e i) = f i) ↔
    (∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then ω.2 else ω.1))
      ((e.trans (headTailEquiv d).toEmbedding) i) = ((f.trans (headTailEquiv d).toEmbedding) i)) := by
  apply forall_congr'
  intro i
  rw [←(headTailEquiv d).injective.eq_iff,palindromePerm_coordinates]
  rfl

lemma routingMoment_step (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : ι ↪ Card (d+1)) (a : ℝ) :
    let x := e.trans (headTailEquiv d).toEmbedding
    let y := f.trans (headTailEquiv d).toEmbedding
    routingMoment (d+1) e f a = PairRouting.outerWeight x y *
      ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
        finiteMean (fun ω : BenesCoins d × BenesCoins d =>
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((assignmentCost d x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0) := by
  classical
  intro x y
  rw [routingMoment,finiteMean_equiv (benesStepEquiv d),finiteMean_prod]
  have he (ω : BenesCoins d × BenesCoins d) :
      finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, palindromePerm (d+1) ((benesStepEquiv d).symm (ω,coins)) (e i) = f i
        then (2:ℝ)^((palindromeCost (d+1) e ((benesStepEquiv d).symm (ω,coins)):ℝ)*a) else 0) =
      PairRouting.outerWeight x y *
        ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((assignmentCost d x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0 := by
    let W : (ι → Bool) → ℝ := fun c =>
      if hc : PairRouting.Compatible x c then (2:ℝ)^((assignmentCost d x c hc ω:ℝ)*a) else 0
    calc
      _ = finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then ω.2 else ω.1))
          (x i) = y i then W (PairRouting.colors x coins.1) else 0) := by
        apply finiteMean_congr
        intro coins
        simp only [palindrome_matches_step,palindromeCost_step]
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

lemma child_moment_product (d : ℕ) {ι : Type*} [Fintype ι]
    (x y : ι ↪ Bool × Card d) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ) :
    routingMoment d (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a *
      routingMoment d (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a =
    finiteMean (fun ω : BenesCoins d × BenesCoins d =>
      if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
      then (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
        palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  classical
  unfold routingMoment
  rw [←finiteMean_prod_mul]
  apply finiteMean_congr
  intro ω
  let M₀ := ∀ i : {i // c i = false}, palindromePerm d ω.1 (x i.val).2 = (y i.val).2
  let M₁ := ∀ i : {i // c i = true}, palindromePerm d ω.2 (x i.val).2 = (y i.val).2
  have hp : (fun b : Bool => palindromePerm d (if b then ω.2 else ω.1)) =
      (fun b => if b then palindromePerm d ω.2 else palindromePerm d ω.1) := by
    funext b
    cases b <;> rfl
  have hs : PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c ↔
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

lemma palindrome_probability_step (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (d+1)) :
    PairRouting.tupleProbability (palindromePerm (d+1)) e f =
    finiteMean (fun ω : BenesCoins d × BenesCoins d =>
      finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => if b then palindromePerm d ω.2 else palindromePerm d ω.1)
          ((e.trans (headTailEquiv d).toEmbedding) i) = ((f.trans (headTailEquiv d).toEmbedding) i)
        then (1:ℝ) else 0)) := by
  classical
  rw [PairRouting.tupleProbability,finiteMean_equiv (benesStepEquiv d),finiteMean_prod]
  have hp (b : Bool) (p q : BenesCoins d) :
      palindromePerm d (if b then p else q) = (if b then palindromePerm d p else palindromePerm d q) := by
    cases b <;> rfl
  simp only [palindrome_matches_step,hp]

lemma child_power_product_bound (d : ℕ) {ι : Type*} [Fintype ι]
    (x y : ι ↪ Bool × Card d) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ)
    (hfalse : (PairRouting.tupleProbability (palindromePerm d)
        (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) ≤
      (2:ℝ)^(-(d:ℝ)*Fintype.card {i // c i = false}*a) *
        routingMoment d (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a)
    (htrue : (PairRouting.tupleProbability (palindromePerm d)
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
      (2:ℝ)^(-(d:ℝ)*Fintype.card {i // c i = true}*a) *
        routingMoment d (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a) :
    (PairRouting.tupleProbability (palindromePerm d)
      (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) *
      (PairRouting.tupleProbability (palindromePerm d)
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
    (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) *
      finiteMean (fun ω : BenesCoins d × BenesCoins d =>
        if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
          palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  have hh := mul_le_mul hfalse htrue
    (Real.rpow_nonneg (PairRouting.tupleProbability_nonneg _ _ _) _)
    (mul_nonneg (by positivity) (routingMoment_nonneg _ _ _ _))
  rw [mul_mul_mul_comm,child_moment_product,←Real.rpow_add (by norm_num : (0:ℝ)<2)] at hh
  have he : -(d:ℝ)*Fintype.card {i // c i = false}*a + -(d:ℝ)*Fintype.card {i // c i = true}*a =
      -(d:ℝ)*Fintype.card ι*a := by
    rw [←add_mul,←mul_add,←Nat.cast_add,PairRouting.color_card_add]
  rwa [he] at hh

lemma assignment_moment_bound (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι ↪ Bool × Card d) (c : ι → Bool) (hc : c ∈ PairRouting.compatibleSet x y)
    (a : ℝ) (ha : 0 ≤ a) :
    let hcx := ((PairRouting.mem_compatibleSet x y c).mp hc).1
    PairRouting.outerWeight x y ^ a * ((PairRouting.compatibleSet x y).card:ℝ)^a *
      ((2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) *
        finiteMean (fun ω : BenesCoins d × BenesCoins d =>
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
          then (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0)) ≤
    (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) *
      finiteMean (fun ω : BenesCoins d × BenesCoins d =>
        if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^((assignmentCost d x c hcx ω:ℝ)*a) else 0) := by
  classical
  intro hcx
  have hscale (q : ℝ) (F : BenesCoins d × BenesCoins d → ℝ) :
      q * finiteMean F = finiteMean (fun ω => q * F ω) := by
    simp_rw [mul_comm q,finiteMean_mul_const]
  rw [←mul_assoc,hscale,hscale]
  apply finiteMean_mono
  intro ω
  split_ifs with hm
  · have hh := PairRouting.assignment_factor_bound x y c hc
      (fun b => palindromePerm d (if b then ω.2 else ω.1)) hm a ha
    calc
      _ ≤ ((2:ℝ)^(((PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hcx)
          (fun b => palindromePerm d (if b then ω.2 else ω.1)):ℝ)-Fintype.card ι)*a) *
          (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a)) *
          (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
      _ = _ := by
        simp only [←Real.rpow_add (by norm_num : (0:ℝ)<2),assignmentCost,Nat.cast_add]
        congr 1
        ring
  · simp only [mul_zero]
    exact le_rfl

/-- The precise recursive pointwise density estimate: the surviving power is
under the actual, independent fair switch law, never an auxiliary coloring law. -/
theorem palindrome_pointwise_moment (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) (ha : 0 ≤ a) :
    (PairRouting.tupleProbability (palindromePerm d) e f)^(1+a) ≤
      (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) * routingMoment d e f a := by
  classical
  induction d generalizing ι with
  | zero =>
      have he : ∀ (ω : BenesCoins 0) (i : ι), palindromePerm 0 ω (e i) = f i :=
        fun _ _ => Subsingleton.elim _ _
      simp [PairRouting.tupleProbability,routingMoment,he,palindromeCost,finiteMean_const]
  | succ d ih =>
      let x := e.trans (headTailEquiv d).toEmbedding
      let y := f.trans (headTailEquiv d).toEmbedding
      let W := PairRouting.outerWeight x y
      let C := PairRouting.compatibleSet x y
      let p : (ι → Bool) → ℝ := fun c =>
        (PairRouting.tupleProbability (palindromePerm d)
          (fun i : {i // c i = false} => (x i.val).2)
          (fun i : {i // c i = false} => (y i.val).2))^(1+a) *
        (PairRouting.tupleProbability (palindromePerm d)
          (fun i : {i // c i = true} => (x i.val).2)
          (fun i : {i // c i = true} => (y i.val).2))^(1+a)
      let m : {c // c ∈ C} → ℝ := fun c =>
        finiteMean (fun ω : BenesCoins d × BenesCoins d =>
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((assignmentCost d x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0)
      have hp (c : {c // c ∈ C}) : W^a * (C.card:ℝ)^a * p c.val ≤
          (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * m c := by
        obtain ⟨hcx,hcy⟩ := (PairRouting.mem_compatibleSet x y c.val).mp c.property
        have h₀ := ih (PairRouting.childEmbedding x c.val hcx false)
          (PairRouting.childEmbedding y c.val hcy false)
        have h₁ := ih (PairRouting.childEmbedding x c.val hcx true)
          (PairRouting.childEmbedding y c.val hcy true)
        have hh := child_power_product_bound d x y c.val hcx hcy a h₀ h₁
        have hh' := mul_le_mul_of_nonneg_left hh
          (mul_nonneg (Real.rpow_nonneg (le_of_lt (PairRouting.outerWeight_pos x y)) a)
            (Real.rpow_nonneg (Nat.cast_nonneg C.card) a))
        exact hh'.trans (assignment_moment_bound d x y c.val c.property a ha)
      have hnode := PairRouting.sandwich_power_bound (palindromePerm d) (palindromePerm d) x y a ha
      rw [←palindrome_probability_step d e f] at hnode
      change (PairRouting.tupleProbability (palindromePerm (d+1)) e f)^(1+a) ≤
        W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c at hnode
      have hsum : ∑ c ∈ C, p c = ∑ c : {c // c ∈ C}, p c.val := by
        rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
      have hW : 0 < W := PairRouting.outerWeight_pos x y
      calc
        _ ≤ W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c := hnode
        _ = W * ∑ c : {c // c ∈ C}, W^a * (C.card:ℝ)^a * p c.val := by
          rw [Real.rpow_add hW,Real.rpow_one,hsum,←Finset.mul_sum]
          ring
        _ ≤ W * ∑ c : {c // c ∈ C}, (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * m c :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hp c)) (le_of_lt hW)
        _ = _ := by
          rw [←Finset.mul_sum,routingMoment_step]
          simp only [Nat.cast_add,Nat.cast_one]
          change W * ((2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * ∑ c, m c) =
            (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * (W * ∑ c, m c)
          ring

lemma routingMoment_sum (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) :
    (∑ f : ι ↪ Card d, routingMoment d e f a) =
      finiteMean (fun ω : BenesCoins d => (2:ℝ)^((palindromeCost d e ω:ℝ)*a)) := by
  classical
  unfold routingMoment
  rw [←finiteMean_sum]
  apply finiteMean_congr
  intro ω
  let f₀ : ι ↪ Card d := e.trans (palindromePerm d ω).toEmbedding
  rw [Finset.sum_eq_single f₀]
  · have hm : ∀ i, palindromePerm d ω (e i) = f₀ i := fun _ => rfl
    simp only [hm,implies_true,↓reduceIte]
  · intro f _ hf
    have hm : ¬ ∀ i, palindromePerm d ω (e i) = f i := by
      intro hh
      apply hf
      ext i : 1
      exact (hh i).symm
    exact ite_eq_right hm
  · simp

lemma finite_row_power {X : Type*} [Fintype X] [Nonempty X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (a : ℝ) :
    finiteMean (fun x => ((Fintype.card X:ℝ)*p x)^(1+a)) =
      (Fintype.card X:ℝ)^a * ∑ x, (p x)^(1+a) := by
  have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  simp only [finiteMean,Real.mul_rpow (le_of_lt hn) (hp _),←Finset.mul_sum]
  rw [Real.rpow_add hn,Real.rpow_one]
  field_simp

noncomputable def palindromeRowMoment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) : ℝ :=
  finiteMean (fun f : ι ↪ Card d =>
    ((Fintype.card (ι ↪ Card d):ℝ)*PairRouting.tupleProbability (palindromePerm d) e f)^(1+a))

lemma density_normalization (d h n : ℕ) (a : ℝ) :
    (n:ℝ)^a * (2:ℝ)^(-(d:ℝ)*h*a) = ((n:ℝ)/((2:ℝ)^d)^h)^a := by
  rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity),←pow_mul,
    ←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Nat.cast_mul]
  rw [show -(d:ℝ)*h*a = -((d:ℝ)*h*a) by ring,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv]

/-- Source FAC.1, for every labelled distinct tuple, with the exact falling-
factorial normalization and the genuine fair-coin palindrome routing cost. -/
theorem palindrome_row_density_moment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) (ha : 0 ≤ a) :
    palindromeRowMoment d e a ≤
      (((2^d).descFactorial (Fintype.card ι):ℝ)/((2^d:ℕ):ℝ)^(Fintype.card ι))^a *
        finiteMean (fun ω : BenesCoins d => (2:ℝ)^((palindromeCost d e ω:ℝ)*a)) := by
  classical
  have : Nonempty (ι ↪ Card d) := ⟨e⟩
  rw [palindromeRowMoment,finite_row_power _ (fun f => PairRouting.tupleProbability_nonneg _ _ _)]
  calc
    _ ≤ (Fintype.card (ι ↪ Card d):ℝ)^a *
      ∑ f : ι ↪ Card d, (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) * routingMoment d e f a :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun f _ => palindrome_pointwise_moment d e f a ha))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by
      rw [←Finset.mul_sum,routingMoment_sum,←mul_assoc,density_normalization,
        Fintype.card_embedding_eq,card_positions]
      norm_cast

end CubeShuffle

namespace CubeShuffle

lemma subset_biUnion_indicator {α β : Type*} [DecidableEq α] [Fintype β]
    (A : Finset α) (T : β → Finset α) :
    (if Finset.univ.biUnion T ⊆ A then (1:ℝ) else 0) =
      ∏ b, if T b ⊆ A then (1:ℝ) else 0 := by
  classical
  by_cases h : Finset.univ.biUnion T ⊆ A
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro b _
    rw [ite_eq_left]
    exact (Finset.subset_biUnion_of_mem T (Finset.mem_univ b)).trans h
  · rw [ite_eq_right h]
    obtain ⟨x,hx,hxA⟩ := Finset.not_subset.mp h
    obtain ⟨b,_,hxb⟩ := Finset.mem_biUnion.mp hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    rw [ite_eq_right]
    exact fun hb => hxA (hb hxb)

/-- Positive multilinear block-polynomials are dominated by product measure
whenever their supports are disjoint and all joint inclusion bounds hold. -/
lemma cylinder_block_polynomial {α β Ω : Type*} [DecidableEq α] [Fintype β]
    [Fintype Ω] (τ : β → Type*) [∀ b, Fintype (τ b)]
    (F : Ω → Finset α) (p : α → ℝ)
    (hF : CylinderBound (inclusionMoment F) p)
    (T : ∀ b, τ b → Finset α) (c : ∀ b, τ b → ℝ)
    (hc : ∀ b s, 0 ≤ c b s)
    (hd : ∀ b b', b ≠ b' → ∀ s s', Disjoint (T b s) (T b' s')) :
    finiteMean (fun ω => ∏ b, ∑ s, c b s * if T b s ⊆ F ω then 1 else 0) ≤
      ∏ b, ∑ s, c b s * ∏ x ∈ T b s, p x := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [finiteMean_sum]
  apply Finset.sum_le_sum
  intro s _
  let U := Finset.univ.biUnion (fun b => T b (s b))
  have he : (fun ω => ∏ b, c b (s b) * if T b (s b) ⊆ F ω then 1 else 0) =
      fun ω => (if U ⊆ F ω then 1 else 0) * ∏ b, c b (s b) := by
    funext ω
    rw [Finset.prod_mul_distrib,←subset_biUnion_indicator]
    exact mul_comm _ _
  rw [he,finiteMean_mul_const]
  have hdis : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint (fun b => T b (s b)) := by
    intro b _ b' _ hbb
    exact hd b b' hbb (s b) (s b')
  have hmean : finiteMean (fun ω => if U ⊆ F ω then 1 else 0) = inclusionMoment F U := by
    unfold inclusionMoment
    apply finiteMean_congr
    intro ω
    by_cases hh : U ⊆ F ω <;> simp [hh]
  calc
    _ ≤ (∏ x ∈ U, p x) * ∏ b, c b (s b) :=
      mul_le_mul_of_nonneg_right (hmean.le.trans (hF U)) (Finset.prod_nonneg (fun b _ => hc b (s b)))
    _ = _ := by
      dsimp only [U]
      rw [Finset.prod_biUnion hdis,←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro b _
      exact mul_comm _ _

end CubeShuffle
namespace CubeShuffle

noncomputable def sparseCoefficient {α : Type*} (w : ℝ) (T : Finset α) : ℝ :=
  if T.card = 1 then 0 else w^T.card

lemma sparseCoefficient_nonneg {α : Type*} (w : ℝ) (hw : 0 ≤ w) (T : Finset α) :
    0 ≤ sparseCoefficient w T := by
  unfold sparseCoefficient
  split_ifs <;> positivity

lemma sparse_block_pointwise {α : Type*} [DecidableEq α] (A D : Finset α)
    (w : ℝ) (hw : 0 ≤ w) :
    w^(if 2 ≤ (D ∩ A).card then (D ∩ A).card else 0) ≤
      ∑ T : ↑D.powerset, sparseCoefficient w T.val * if T.val ⊆ A then 1 else 0 := by
  classical
  let V := D ∩ A
  let T : ↑D.powerset := if 2 ≤ V.card then
    ⟨V,Finset.mem_powerset.mpr Finset.inter_subset_left⟩ else
    ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset D)⟩
  calc
    _ = sparseCoefficient w T.val * (if T.val ⊆ A then 1 else 0) := by
      by_cases h : 2 ≤ V.card
      · have hn : V.card ≠ 1 := by omega
        simp [T,ite_eq_left h,sparseCoefficient,hn,show V ⊆ A from Finset.inter_subset_right,V]
      · simp [T,ite_eq_right h,sparseCoefficient,V] at *
    _ ≤ _ := Finset.single_le_sum (f := fun S : ↑D.powerset =>
      sparseCoefficient w S.val * (if S.val ⊆ A then 1 else 0))
      (fun S _ => mul_nonneg (sparseCoefficient_nonneg w hw S.val)
        (by split_ifs <;> norm_num)) (Finset.mem_univ T)

lemma geometric_sum_half (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1/2) :
    ∑ i ∈ Finset.range n, x^i ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ',pow_zero]
    simp only [pow_succ',←Finset.mul_sum]
    nlinarith

lemma sparse_binomial_bound (R : ℕ) (z : ℝ) (hz : 0 ≤ z) (hr : (R:ℝ)*z ≤ 1/2) :
    ∑ i ∈ Finset.range (R+1), (R.choose i:ℝ) * (if i = 1 then 0 else z^i) ≤
      1 + 2*((R:ℝ)*z)^2 := by
  classical
  let x := (R:ℝ)*z
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hz
  have hbound (i : ℕ) : (R.choose i:ℝ)*(if i=1 then 0 else z^i) ≤
      if i=1 then 0 else x^i := by
    by_cases h : i=1
    · simp [h]
    · simp only [ite_eq_right h]
      dsimp [x]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hz i)
      exact_mod_cast Nat.choose_le_pow R i
  calc
    _ ≤ ∑ i ∈ Finset.range (R+1), if i=1 then 0 else x^i :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ ≤ 1+2*x^2 := by
      rcases R with _ | R
      · simp [x]
      rcases R with _ | R
      · norm_num [Finset.sum_range_succ]
        positivity
      have he : ∑ i ∈ Finset.range (R+2+1), (if i=1 then 0 else x^i) =
          1 + x^2*∑ i ∈ Finset.range (R+1), x^i := by
        rw [show R+2+1=2+(R+1) by omega,Finset.sum_range_add]
        have hn (i : ℕ) : 2+i ≠ 1 := by omega
        simp only [hn,ite_false,pow_add,←Finset.mul_sum]
        norm_num [Finset.sum_range_succ]
      rw [he]
      have hg := geometric_sum_half (R+1) hx hr
      nlinarith [sq_nonneg x]

lemma sparse_block_product_bound {α : Type*} [DecidableEq α]
    (D : Finset α) (p w : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hr : (D.card:ℝ)*(p*w) ≤ 1/2) :
    ∑ T : ↑D.powerset, sparseCoefficient w T.val * p^T.val.card ≤
      Real.exp (2*((D.card:ℝ)*(p*w))^2) := by
  classical
  have he : ∑ T : ↑D.powerset, sparseCoefficient w T.val * p^T.val.card =
      ∑ i ∈ Finset.range (D.card+1), (D.card.choose i:ℝ)*(if i=1 then 0 else (p*w)^i) := by
    rw [Finset.sum_coe_sort D.powerset (fun T => sparseCoefficient w T*p^T.card)]
    have hh : (fun T : Finset α => sparseCoefficient w T*p^T.card) =
        fun T => if T.card=1 then 0 else (p*w)^T.card := by
      funext T
      unfold sparseCoefficient
      split_ifs <;> simp [mul_pow,mul_comm]
    change (∑ T ∈ D.powerset, (fun T : Finset α => sparseCoefficient w T*p^T.card) T) = _
    rw [hh,Finset.sum_powerset_apply_card (fun i => if i=1 then (0:ℝ) else (p*w)^i)]
    simp only [nsmul_eq_mul]
  rw [he]
  exact (sparse_binomial_bound D.card (p*w) (mul_nonneg hp hw) hr).trans
    (by simpa only [add_comm] using Real.add_one_le_exp (2*((D.card:ℝ)*(p*w))^2))

end CubeShuffle
namespace CubeShuffle

noncomputable def sparseMass {α β : Type*} [DecidableEq α] [Fintype β]
    (D : β → Finset α) (A : Finset α) : ℕ :=
  ∑ b, if 2 ≤ (D b ∩ A).card then (D b ∩ A).card else 0

/-- The sparse low-block moment bound uses only actual joint inclusion, not
independence or a negative-association assumption. -/
theorem sparse_block_mgf {α β Ω : Type*} [DecidableEq α] [Fintype β] [Fintype Ω]
    (D : β → Finset α) (hd : Pairwise (fun b b' => Disjoint (D b) (D b')))
    (F : Ω → Finset α) (p w : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hF : ∀ T, inclusionMoment F T ≤ p^T.card)
    (hr : ∀ b, ((D b).card:ℝ)*(p*w) ≤ 1/2) :
    finiteMean (fun ω => w^(sparseMass D (F ω))) ≤
      Real.exp (∑ b, 2*(((D b).card:ℝ)*(p*w))^2) := by
  classical
  have hc : CylinderBound (inclusionMoment F) (fun _ => p) := by
    intro T
    simpa only [Finset.prod_const] using hF T
  have hb := cylinder_block_polynomial (fun b => ↑(D b).powerset) F (fun _ => p) hc
    (fun _ S => S.val) (fun _ S => sparseCoefficient w S.val)
    (fun _ S => sparseCoefficient_nonneg w hw S.val)
    (fun b b' h S S' => (hd h).mono
      (Finset.mem_powerset.mp S.property) (Finset.mem_powerset.mp S'.property))
  calc
    _ ≤ finiteMean (fun ω => ∏ b, ∑ S : ↑(D b).powerset,
        sparseCoefficient w S.val * if S.val ⊆ F ω then 1 else 0) := by
      apply finiteMean_mono
      intro ω
      rw [sparseMass,←Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_le_prod₀ (fun _ _ => pow_nonneg hw _)
      intro b _
      exact sparse_block_pointwise (F ω) (D b) w hw
    _ ≤ ∏ b, ∑ S : ↑(D b).powerset, sparseCoefficient w S.val * p^S.val.card := by
      simpa only [Finset.prod_const] using hb
    _ ≤ _ := by
      rw [Real.exp_sum]
      apply Finset.prod_le_prod₀
      · intro b _
        exact Finset.sum_nonneg (fun S _ => mul_nonneg
          (sparseCoefficient_nonneg w hw S.val) (pow_nonneg hp _))
      · intro b _
        exact sparse_block_product_bound (D b) p w hp hw (hr b)

/-- In particular this holds for central marks of the genuine input butterfly. -/
theorem inverseButterfly_sparse_mgf (d : ℕ) {β : Type*} [Fintype β]
    (D : β → Finset (Card d)) (hd : Pairwise (fun b b' => Disjoint (D b) (D b')))
    (A : Finset (Card d)) (w : ℝ) (hw : 0 ≤ w)
    (hr : ∀ b, ((D b).card:ℝ)*((A.card/(2:ℝ)^d)*w) ≤ 1/2) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      w^(sparseMass D (inverseButterflyMarks d A ω))) ≤
      Real.exp (∑ b, 2*(((D b).card:ℝ)*((A.card/(2:ℝ)^d)*w))^2) := by
  apply sparse_block_mgf D hd (inverseButterflyMarks d A) (A.card/(2:ℝ)^d) w
    (by positivity) hw
  · exact inverseButterflyMarks_inclusion d A
  · exact hr

end CubeShuffle
namespace CubeShuffle

def crowdedMass (h : ℕ) : ℕ := if 2 ≤ h then h else 0

lemma crowdedMass_le (h : ℕ) : crowdedMass h ≤ h := by
  unfold crowdedMass
  split_ifs <;> omega

lemma crowdedMass_add (u v : ℕ) : crowdedMass u + crowdedMass v ≤ crowdedMass (u+v) := by
  unfold crowdedMass
  split_ifs <;> omega

lemma alternatingCycles_le_crowded {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤ crowdedMass (Fintype.card ι) := by
  unfold crowdedMass
  split_ifs with h
  · have hh := PairRouting.alternatingCycles_double e p
    omega
  · rw [PairRouting.alternatingCycles_zero e p (by omega)]

lemma palindromeCost_le_crowded (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeCost d e ω ≤ d*crowdedMass (Fintype.card ι) := by
  classical
  induction d generalizing ι with
  | zero => simp [palindromeCost]
  | succ d ih =>
    let σ := benesStepEquiv d ω
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    have h₀ := ih (PairRouting.childEmbedding x c hc false) σ.1.1
    have h₁ := ih (PairRouting.childEmbedding x c hc true) σ.1.2
    have hz := alternatingCycles_le_crowded (PairRouting.switchedEmbedding x σ.2.1)
      (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1))
    have hs := crowdedMass_add (Fintype.card {i // c i = false})
      (Fintype.card {i // c i = true})
    rw [PairRouting.color_card_add] at hs
    change PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
        (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2 ≤ _
    nlinarith

/-- The exact sum of FAC.1 node costs through height H. -/
noncomputable def palindromeLowCost (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if d+1 ≤ H then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc true) σ.1.2

/-- Colliding mass in the size-2^H central blocks, read along the actual input routes. -/
noncomputable def cutoffMass (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, ι, _, e, ω =>
      if d+1 ≤ H then crowdedMass (Fintype.card ι) else
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      cutoffMass H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        cutoffMass H d (PairRouting.childEmbedding x c hc true) σ.1.2

lemma palindromeLowCost_eq (H d : ℕ) (h : d ≤ H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω = palindromeCost d e ω := by
  classical
  induction d generalizing ι with
  | zero => rfl
  | succ d ih =>
    rw [palindromeLowCost,palindromeCost,ite_eq_left h]
    congr 2 <;> exact ih (by omega) _ _

lemma palindromeLowCost_le_cutoff (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω ≤ H*cutoffMass H d e ω := by
  classical
  induction d generalizing ι with
  | zero => simp [palindromeLowCost,cutoffMass]
  | succ d ih =>
    by_cases h : d+1 ≤ H
    · rw [palindromeLowCost_eq H (d+1) h,cutoffMass,ite_eq_left h]
      exact (palindromeCost_le_crowded (d+1) e ω).trans (Nat.mul_le_mul_right _ h)
    · rw [palindromeLowCost,cutoffMass,ite_eq_right h,ite_eq_right h,zero_add,Nat.mul_add]
      exact Nat.add_le_add (ih _ _) (ih _ _)

end CubeShuffle
namespace CubeShuffle

noncomputable def centralBlock (r H : ℕ) (b : Card r) : Finset (Card (H+r)) :=
  Finset.univ.image (fun z : Card H => (cardSplit r H).symm (b,z))

lemma mem_centralBlock (r H : ℕ) (b : Card r) (x : Card (H+r)) :
    x ∈ centralBlock r H b ↔ (cardSplit r H x).1 = b := by
  classical
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h
    simp only [Equiv.apply_symm_apply]
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(cardSplit r H x).2,Finset.mem_univ _,?_⟩
    rw [←h,Prod.mk.eta,Equiv.symm_apply_apply]

lemma centralBlock_card (r H : ℕ) (b : Card r) : (centralBlock r H b).card = 2^H := by
  classical
  rw [centralBlock,Finset.card_image_of_injective]
  · exact card_positions H
  · intro x y h
    exact congrArg Prod.snd ((cardSplit r H).symm.injective h)

lemma centralBlock_disjoint (r H : ℕ) :
    Pairwise (fun b b' => Disjoint (centralBlock r H b) (centralBlock r H b')) := by
  classical
  intro b b' h
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_centralBlock r H b x).mp hx).symm.trans
    ((mem_centralBlock r H b' x).mp hy))

lemma centralBlock_zero (H : ℕ) (b : Card 0) : centralBlock 0 H b = Finset.univ := by
  classical
  ext x
  simp only [mem_centralBlock,Finset.mem_univ,iff_true]
  exact Subsingleton.elim _ _

lemma centralBlock_step (r H : ℕ) (b : Bool) (c : Card r) :
    centralBlock (r+1) H (Fin.cons b c) = (centralBlock r H c).image (Fin.cons b) := by
  classical
  simp only [centralBlock,Finset.image_image,cardSplit,Equiv.coe_fn_symm_mk,
    Fin.cons_zero,Fin.tail_cons,Function.comp_def]

lemma block_inter_step (r H : ℕ) (b : Bool) (c : Card r) (A : Finset (Card (H+(r+1)))) :
    centralBlock (r+1) H (Fin.cons b c) ∩ A =
      (centralBlock r H c ∩ childMarks A b).image (Fin.cons b) := by
  classical
  rw [centralBlock_step]
  ext x
  constructor
  · intro hx
    obtain ⟨hxB,hxA⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hxB
    exact Finset.mem_image.mpr ⟨y,Finset.mem_inter.mpr ⟨hy,(mem_childMarks A b y).mpr hxA⟩,rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y,(Finset.mem_inter.mp hy).1,rfl⟩,
      (mem_childMarks A b y).mp (Finset.mem_inter.mp hy).2⟩

lemma sparseMass_central_zero (H : ℕ) (A : Finset (Card H)) :
    sparseMass (centralBlock 0 H) A = crowdedMass A.card := by
  classical
  simp only [sparseMass,centralBlock_zero,Finset.univ_inter,crowdedMass,
    Finset.sum_const,Finset.card_univ,card_positions,pow_zero,one_nsmul]

lemma sparseMass_central_step (r H : ℕ) (A : Finset (Card (H+(r+1)))) :
    sparseMass (centralBlock (r+1) H) A =
      sparseMass (centralBlock r H) (childMarks A false) +
        sparseMass (centralBlock r H) (childMarks A true) := by
  classical
  unfold sparseMass
  rw [←Equiv.sum_comp (headTailEquiv r).symm,Fintype.sum_prod_type]
  have ht (b : Bool) (c : Card r) : (headTailEquiv r).symm (b,c) = Fin.cons b c := rfl
  simp only [Fintype.sum_bool,ht]
  have hc (b : Bool) (c : Card r) :
      (centralBlock (r+1) H (Fin.cons b c) ∩ A).card =
      (centralBlock r H c ∩ childMarks A b).card := by
    rw [block_inter_step]
    apply Finset.card_image_of_injective
    intro x y h
    simpa only [Fin.tail_cons] using congrArg Fin.tail h
  simp only [hc]
  exact add_comm _ _

end CubeShuffle
namespace CubeShuffle

lemma inverseButterfly_coordinates_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool)
    (x : Card (d+1)) :
    headTailEquiv d ((butterflyPerm (d+1)
      (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ)))).symm x) =
      (Bool.xor (x 0) (ξ (Fin.tail x)),
        (butterflyPerm d (decodeButterfly d
          (if Bool.xor (x 0) (ξ (Fin.tail x)) then c.2 else c.1))).symm (Fin.tail x)) := by
  rw [butterflyPerm_step]
  rfl

lemma inverseButterflyMarks_child (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1))
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) (b : Bool) :
    childMarks (inverseButterflyMarks (d+1) (Finset.univ.image e)
      ((coinStepEquiv d).symm (c,ξ))) b =
      inverseButterflyMarks d
        (Finset.univ.image (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ)
            (PairRouting.colors_compatible _ _) b)) (if b then c.2 else c.1) := by
  classical
  let x := e.trans (headTailEquiv d).toEmbedding
  let col := PairRouting.colors x ξ
  let child := PairRouting.childEmbedding x col (PairRouting.colors_compatible x ξ) b
  have hp (i : ι) : headTailEquiv d ((butterflyPerm (d+1)
      (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ)))).symm (e i)) =
      (col i,(butterflyPerm d (decodeButterfly d (if col i then c.2 else c.1))).symm (x i).2) :=
    inverseButterfly_coordinates_step d c ξ (e i)
  ext y
  simp only [mem_childMarks,inverseButterflyMarks,Finset.image_image,
    Finset.mem_image,Finset.mem_univ,true_and,Function.comp_def]
  constructor
  · rintro ⟨i,hi⟩
    have he := congrArg (headTailEquiv d) hi
    rw [hp i] at he
    change (col i,_) = (b,y) at he
    have hb := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only at hb hy
    refine ⟨⟨i,hb⟩,?_⟩
    change (butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))).symm (x i).2 = y
    simpa only [hb] using hy
  · rintro ⟨i,hi⟩
    refine ⟨i.val,?_⟩
    apply (headTailEquiv d).injective
    rw [hp]
    change (col i.val,_) = (b,y)
    have hb : col i.val = b := i.property
    rw [hb]
    exact Prod.ext rfl hi

lemma inverseButterflyMarks_card (d : ℕ) (A : Finset (Card d)) (ω : SwitchIndex d → Bool) :
    (inverseButterflyMarks d A ω).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (butterflyPerm d (decodeButterfly d ω)).symm.injective

lemma benes_input_coordinates (d : ℕ) (ω : BenesCoins (d+1)) :
    ω.2 = (coinStepEquiv d).symm
      (((benesStepEquiv d ω).1.1.2,(benesStepEquiv d ω).1.2.2),(benesStepEquiv d ω).2.1) := by
  change ω.2 = (coinStepEquiv d).symm (coinStepEquiv d ω.2)
  exact ((coinStepEquiv d).symm_apply_apply ω.2).symm

lemma cutoffMass_central (r H : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (ω : BenesCoins (H+r)) :
    cutoffMass H (H+r) e ω =
      sparseMass (centralBlock r H) (inverseButterflyMarks (H+r) (Finset.univ.image e) ω.2) := by
  classical
  induction r generalizing ι with
  | zero =>
    rw [sparseMass_central_zero,inverseButterflyMarks_card,
      Finset.card_image_of_injective _ e.injective,Finset.card_univ]
    cases H with
    | zero =>
      have hcard : Fintype.card ι ≤ 1 := by
        have hh := Fintype.card_le_of_injective e e.injective
        simpa only [Nat.add_zero,card_positions,pow_zero] using hh
      simp [cutoffMass,crowdedMass,show ¬2≤Fintype.card ι by omega]
    | succ H => simp only [cutoffMass,le_refl,ite_true]
  | succ r ih =>
    simp only [Nat.add_succ] at *
    rw [cutoffMass,ite_eq_right (by omega : ¬H+r+1≤H)]
    let σ := benesStepEquiv (H+r) ω
    let x := e.trans (headTailEquiv (H+r)).toEmbedding
    let col := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    change cutoffMass H (H+r) (PairRouting.childEmbedding x col hc false) σ.1.1 +
      cutoffMass H (H+r) (PairRouting.childEmbedding x col hc true) σ.1.2 = _
    rw [ih,ih,sparseMass_central_step,benes_input_coordinates (H+r) ω]
    rw [inverseButterflyMarks_child,inverseButterflyMarks_child]
    rfl

end CubeShuffle
namespace CubeShuffle

/-- Actual low-height cycle mass of the Beneš routing, with fair input coins.
There is no independence assumption on marked positions. -/
theorem palindrome_low_mgf (r H : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (q : ℝ) (hq : 1 ≤ q)
    (hr : (2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*q^H) ≤ 1/2) :
    finiteMean (fun ω : BenesCoins (H+r) => q^(palindromeLowCost H (H+r) e ω)) ≤
      Real.exp ((2:ℝ)^r * (2 * ((2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*q^H))^2)) := by
  classical
  have hec : (Finset.univ.image e).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ e.injective,Finset.card_univ]
  have hm := inverseButterfly_sparse_mgf (H+r) (centralBlock r H)
    (centralBlock_disjoint r H) (Finset.univ.image e) (q^H)
    (pow_nonneg (by linarith) _) (fun b => by
      simpa only [centralBlock_card,hec,Nat.cast_pow,Nat.cast_ofNat] using hr)
  calc
    _ ≤ finiteMean (fun ω : BenesCoins (H+r) => (q^H)^(cutoffMass H (H+r) e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [←pow_mul]
      exact pow_le_pow_right₀ hq (palindromeLowCost_le_cutoff H (H+r) e ω)
    _ = finiteMean (fun ω : SwitchIndex (H+r) → Bool =>
        (q^H)^(sparseMass (centralBlock r H)
          (inverseButterflyMarks (H+r) (Finset.univ.image e) ω))) := by
      simp_rw [cutoffMass_central]
      simp only [finiteMean_prod,finiteMean_const]
    _ ≤ _ := by
      simpa only [centralBlock_card,hec,Nat.cast_pow,Nat.cast_ofNat,Finset.sum_const,
        Finset.card_univ,card_positions,nsmul_eq_mul] using hm

end CubeShuffle

end OAI
