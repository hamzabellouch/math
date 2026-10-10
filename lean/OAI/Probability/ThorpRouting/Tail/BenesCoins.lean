import Mathlib
import OAI.Probability.ThorpRouting.Tail.AlternatingPerm

namespace OAI

namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

def sandwichShuffle {A B C D E F : Type*} :
    ((A × B) × C) × ((D × E) × F) ≃ ((A × D) × (B × E)) × (F × C) where
  toFun x := (((x.1.1.1,x.2.1.1),(x.1.1.2,x.2.1.2)),(x.2.2,x.1.2))
  invFun x := (((x.1.1.1,x.1.2.1),x.2.2),((x.1.1.2,x.1.2.2),x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def benesStepEquiv (d : ℕ) : BenesCoins (d+1) ≃
    (BenesCoins d × BenesCoins d) × ((Card d → Bool) × (Card d → Bool)) :=
  (Equiv.prodCongr (coinStepEquiv d) (coinStepEquiv d)).trans sandwichShuffle

lemma childLift_mul (d : ℕ) (p q : Bool → Equiv.Perm (Card d)) :
    childLift p * childLift q = childLift (fun b => p b * q b) := by
  ext x i
  simp only [Equiv.Perm.mul_apply,childLift,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons]

lemma childLift_inv (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    (childLift p)⁻¹ = childLift (fun b => (p b)⁻¹) := rfl

lemma pairSwitch_inv (d : ℕ) (ξ : Card d → Bool) : (pairSwitch ξ)⁻¹ = pairSwitch ξ := rfl

lemma palindromePerm_step (d : ℕ) (c : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) :
    palindromePerm (d+1) ((benesStepEquiv d).symm (c,coins)) =
      pairSwitch coins.2 * childLift (fun b => palindromePerm d (if b then c.2 else c.1)) *
        pairSwitch coins.1 := by
  change (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((c.1.1,c.2.1),coins.2)))) *
    (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((c.1.2,c.2.2),coins.1))))⁻¹ = _
  rw [butterflyPerm_step,butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
  rw [mul_assoc (pairSwitch coins.2),←mul_assoc (childLift _),childLift_mul,←mul_assoc]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

lemma headTail_switch (d : ℕ) (ξ : Card d → Bool) (x : Card (d+1)) :
    headTailEquiv d (pairSwitch ξ x) = pairLayer ξ (headTailEquiv d x) := rfl

lemma headTail_child (d : ℕ) (p : Bool → Equiv.Perm (Card d)) (x : Card (d+1)) :
    headTailEquiv d (childLift p x) = PairRouting.lift p (headTailEquiv d x) := rfl

lemma palindromePerm_coordinates (d : ℕ) (c : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) (x : Card (d+1)) :
    headTailEquiv d (palindromePerm (d+1) ((benesStepEquiv d).symm (c,coins)) x) =
      PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then c.2 else c.1))
        (headTailEquiv d x) := by
  rw [palindromePerm_step]
  simp only [Equiv.Perm.mul_apply,headTail_switch,headTail_child]
  rfl

noncomputable def palindromeCost : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma alternating_cycle_two (p : Equiv.Perm α) (S : Finset (Bool × α))
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) S) : 2 ≤ C.val.card := by
  obtain ⟨x,hx⟩ := C.nonempty
  have hpx : alternatingPerm p x ∈ C.val := by
    rw [←C.orbit_eq hx,mem_orbitSet]
    exact (Equiv.Perm.SameCycle.refl _ _).apply_right
  have hne : x ≠ alternatingPerm p x := by
    intro he
    have hh := congrArg Prod.fst he
    rw [alternatingPerm_flip] at hh
    cases hb : x.1 <;> simp only [hb, Bool.not_false, Bool.not_true] at hh <;> cases hh
  have hs : {x,alternatingPerm p x} ⊆ C.val := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  have hh := Finset.card_le_card hs
  simpa only [Finset.card_pair hne] using hh

lemma alternating_cycle_count_double (p : Equiv.Perm α) (S : Finset (Bool × α)) :
    2 * Fintype.card (RoutingNetwork.SelectedCycle (alternatingPerm p) S) ≤ S.card := by
  classical
  calc
    _ = ∑ _C : RoutingNetwork.SelectedCycle (alternatingPerm p) S, 2 := by simp [Nat.mul_comm]
    _ ≤ RoutingNetwork.cycleMass (alternatingPerm p) S :=
      Finset.sum_le_sum (fun C _ => alternating_cycle_two p S C)
    _ ≤ _ := RoutingNetwork.cycleMass_le _ _

lemma alternating_cycle_count_zero (p : Equiv.Perm α) (S : Finset (Bool × α))
    (hS : S.card ≤ 1) : Fintype.card (RoutingNetwork.SelectedCycle (alternatingPerm p) S) = 0 := by
  have h := alternating_cycle_count_double p S
  omega

end CycleColoring

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

lemma alternatingCycles_double (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    2 * alternatingCycles e p ≤ Fintype.card ι := by
  have hh := CycleColoring.alternating_cycle_count_double (alternatingProjection p) (labelSet e)
  simpa only [alternatingCycles, card_labelSet] using hh

lemma alternatingCycles_zero (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α)
    (hι : Fintype.card ι ≤ 1) : alternatingCycles e p = 0 := by
  have hh := alternatingCycles_double e p
  omega

end
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

omit [Fintype α] [DecidableEq ι] in
lemma colors_chosenCoin (x : ι → Bool × α) (c : ι → Bool) (hc : Compatible x c) :
    colors x (chosenCoin x c) = c := by
  funext i
  simp only [colors,chosenCoin_apply x c hc i,required]
  cases (x i).1 <;> cases c i <;> rfl

noncomputable def coloredEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (_hc : Compatible x c) :
    ι ↪ Bool × α := switchedEmbedding x (chosenCoin x c)

omit [Fintype α] [DecidableEq ι] in
lemma coloredEmbedding_apply (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (i : ι) :
    coloredEmbedding x c hc i = (c i,(x i).2) := by
  apply Prod.ext
  · exact congrFun (colors_chosenCoin x c hc) i
  · rfl

omit [Fintype α] [DecidableEq ι] in
lemma switchedEmbedding_eq_colored (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c)
    (ξ : α → Bool) (he : colors x ξ = c) :
    switchedEmbedding x ξ = coloredEmbedding x c hc := by
  ext i : 1
  rw [coloredEmbedding_apply]
  apply Prod.ext
  · exact congrFun he i
  · rfl

lemma assignments_match_bound (x y : ι ↪ Bool × α) (c : ι → Bool)
    (hc : c ∈ compatibleSet x y) (p : Bool → Equiv.Perm α) (hm : ChildMatches p x y c) :
    (compatibleSet x y).card ≤
      2 ^ ((occupied x).card + (occupied y).card - Fintype.card ι +
        alternatingCycles (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p) := by
  obtain ⟨hcx,hcy⟩ := (mem_compatibleSet x y c).mp hc
  let ξ := chosenCoin x c
  let η := chosenCoin y c
  have he : routedEmbedding x ξ η p = y := by
    ext i : 1
    have h := (sandwich_matches_iff ξ η p x y).mpr
      ⟨(colors_chosenCoin x c hcx).trans (colors_chosenCoin y c hcy).symm,by
        simpa only [ξ,colors_chosenCoin x c hcx] using hm⟩
    exact h i
  have hh := assignments_actual_bound x ξ η p
  rw [he] at hh
  rw [card_compatibleSet]
  exact hh

omit [Fintype α] [DecidableEq ι] in
lemma occupied_sum_ge (x y : ι ↪ Bool × α) :
    Fintype.card ι ≤ (occupied x).card + (occupied y).card := by
  have h₀ := occupied_card_double x
  have h₁ := occupied_card_double y
  omega

lemma assignment_weight_bound (x y : ι ↪ Bool × α) (c : ι → Bool)
    (hc : c ∈ compatibleSet x y) (p : Bool → Equiv.Perm α) (hm : ChildMatches p x y c) :
    ((compatibleSet x y).card:ℝ) * outerWeight x y ≤
      (2:ℝ)^((alternatingCycles
        (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p : ℝ) - Fintype.card ι) := by
  let z := alternatingCycles (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p
  let b := (occupied x).card+(occupied y).card
  let h := Fintype.card ι
  have hb : h ≤ b := occupied_sum_ge x y
  have hn : ((compatibleSet x y).card:ℝ) ≤ (2:ℝ)^(b-h+z) := by
    exact_mod_cast assignments_match_bound x y c hc p hm
  change ((compatibleSet x y).card:ℝ) * (1/(2:ℝ)^b) ≤ (2:ℝ)^((z:ℝ)-h)
  rw [mul_one_div]
  calc
    _ ≤ (2:ℝ)^(b-h+z)/(2:ℝ)^b := div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
      congr 1
      rw [Nat.cast_add,Nat.cast_sub hb]
      ring

lemma assignment_factor_bound (x y : ι ↪ Bool × α) (c : ι → Bool)
    (hc : c ∈ compatibleSet x y) (p : Bool → Equiv.Perm α) (hm : ChildMatches p x y c)
    (a : ℝ) (ha : 0 ≤ a) :
    (outerWeight x y)^a * ((compatibleSet x y).card:ℝ)^a ≤
      (2:ℝ)^(((alternatingCycles
        (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p : ℝ) - Fintype.card ι)*a) := by
  have h := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (outerWeight_pos x y)))
    (assignment_weight_bound x y c hc p hm) ha
  rw [Real.mul_rpow (Nat.cast_nonneg _) (le_of_lt (outerWeight_pos x y)),
    ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)] at h
  simpa only [mul_comm] using h


lemma sandwich_weighted_probability_subtype (p : Bool → Equiv.Perm α) (x y : ι → Bool × α)
    (W : (ι → Bool) → ℝ) :
    finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then W (colors x coins.1) else 0) =
    outerWeight x y * ∑ c : {c // c ∈ compatibleSet x y},
      if ChildMatches p x y c.val then W c.val else 0 := by
  rw [sandwich_weighted_probability]
  congr 1
  rw [Finset.sum_subtype (compatibleSet x y) (fun _ => Iff.rfl)]

omit [Fintype α] [DecidableEq α] [DecidableEq ι] in
lemma color_card_add (c : ι → Bool) :
    Fintype.card {i // c i = false} + Fintype.card {i // c i = true} = Fintype.card ι := by
  have he : {i // c i = true} ≃ {i // ¬c i = false} := Equiv.subtypeEquivRight fun i => by
    cases c i <;> simp
  rw [Fintype.card_congr he]
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

end PairRouting

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

end Thorp
namespace Thorp

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


noncomputable def sparseMass {α β : Type*} [DecidableEq α] [Fintype β]
    (D : β → Finset α) (A : Finset α) : ℕ :=
  ∑ b, if 2 ≤ (D b ∩ A).card then (D b ∩ A).card else 0

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


noncomputable def centralBlock (r H : ℕ) (b : Card r) : Finset (Card (H+r)) :=
  Finset.univ.image (fun z : Card H => (cardSplit r H).symm (b,z))

end Thorp

end ThorpNine.Tail

end OAI
