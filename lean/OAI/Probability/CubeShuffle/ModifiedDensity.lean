import OAI.Probability.CubeShuffle.ModifiedRouting

namespace OAI

namespace CubeShuffle

noncomputable def exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) : Finset (Card r) :=
  Finset.univ.filter (fun u => Fin.cons b u ∈ E)

lemma mem_exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) (u : Card r) :
    u ∈ exceptionChild E b ↔ Fin.cons b u ∈ E := by
  classical
  simp only [exceptionChild,Finset.mem_filter,Finset.mem_univ,true_and]

lemma exceptionChild_card_add {r : ℕ} (E : Finset (Card (r+1))) :
    (exceptionChild E false).card+(exceptionChild E true).card = E.card := by
  classical
  have he : (∑ u : Card (r+1), if u ∈ E then 1 else 0) = E.card := by simp
  rw [Fintype.sum_equiv (headTailEquiv r) _
    (fun x : Bool × Card r => if Fin.cons x.1 x.2 ∈ E then 1 else 0)
    (fun x => by change (if x ∈ E then 1 else 0) = (if Fin.cons (x 0) (Fin.tail x) ∈ E then 1 else 0); rw [Fin.cons_self_tail])] at he
  simp only [Fintype.sum_prod_type,Fintype.sum_bool] at he
  simpa only [exceptionChild,Finset.card_filter,add_comm] using he

def seedSplitEquiv (r : ℕ) (A : Type*) : (Card (r+1) → A) ≃ (Card r → A) × (Card r → A) where
  toFun U := (fun u => U (Fin.cons false u),fun u => U (Fin.cons true u))
  invFun U := fun u => if u 0 then U.2 (Fin.tail u) else U.1 (Fin.tail u)
  left_inv U := by
    funext u
    dsimp only
    split_ifs with h
    · rw [←h,Fin.cons_self_tail]
    · have h' : u 0 = false := by cases hh : u 0 <;> simp_all
      rw [←h',Fin.cons_self_tail]
  right_inv U := by simp only [Fin.cons_zero,Fin.tail_cons,Bool.false_eq_true,↓reduceIte]

def seedSandwichShuffle {A B C D E : Type*} :
    (A × B) × ((C × D) × E) ≃ ((A × C) × (B × D)) × E where
  toFun x := (((x.1.1,x.2.1.1),(x.1.2,x.2.1.2)),x.2.2)
  invFun x := ((x.1.1.1,x.1.2.1),((x.1.1.2,x.1.2.2),x.2))
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ModifiedCoins (L r : ℕ) := (Card r → Equiv.Perm (Card L)) × BenesCoins (L+r)

def modifiedStepEquiv (L r : ℕ) : ModifiedCoins L (r+1) ≃
    (ModifiedCoins L r × ModifiedCoins L r) × ((Card (L+r) → Bool) × (Card (L+r) → Bool)) :=
  (Equiv.prodCongr (seedSplitEquiv r (Equiv.Perm (Card L))) (benesStepEquiv (L+r))).trans
    seedSandwichShuffle

noncomputable def modifiedPerm (L r : ℕ) (E : Finset (Card r)) (ω : ModifiedCoins L r) :
    Equiv.Perm (Card (L+r)) :=
  butterflyPerm (L+r) (decodeButterfly (L+r) ω.2.1) *
    (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1).perm⁻¹

noncomputable def modifiedCost (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : ModifiedCoins L r) : ℕ :=
  InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1) e ω.2.1

lemma modifiedBoundary_cons (L r : ℕ) (E : Finset (Card (r+1)))
    (U : Card (r+1) → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r+1) → Bool) (b : Bool) :
    (fun u => modifiedBoundary L (r+1) E U Y (Fin.cons b u)) =
    modifiedBoundary L r (exceptionChild E b) (fun u => U (Fin.cons b u))
      (if b then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) := by
  funext u
  simp only [modifiedBoundary,mem_exceptionChild,boundaryOutput,Fin.cons_zero,Fin.tail_cons]

lemma modifiedInputTree_node (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    let z := (modifiedStepEquiv L r).symm (ω,coins)
    modifiedInputTree L (r+1) E z.1 z.2.2 z.2.1 =
      InputTree.node coins.1 (fun b =>
        let w := if b then ω.2 else ω.1
        modifiedInputTree L r (exceptionChild E b) w.1 w.2.2 w.2.1) := by
  dsimp only
  unfold modifiedInputTree
  rw [boundaryTree]
  change InputTree.node coins.1 (fun b => boundaryTree L r _ _) = _
  congr 1
  funext b
  rw [modifiedBoundary_cons]
  cases b <;> rfl

lemma modifiedPerm_step (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) =
      pairSwitch coins.2 * childLift (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) * pairSwitch coins.1 := by
  rw [modifiedPerm,modifiedInputTree_node,InputTree.perm,mul_inv_rev,pairSwitch_inv,childLift_inv]
  change (butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)))) * _ = _
  rw [butterflyPerm_step,mul_assoc,←mul_assoc (childLift _),childLift_mul,←mul_assoc]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

lemma modifiedPerm_coordinates (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool))
    (x : Card (L+r+1)) :
    headTailEquiv (L+r) (modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) x) =
      PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) (headTailEquiv (L+r) x) := by
  rw [modifiedPerm_step]
  simp only [Equiv.Perm.mul_apply,headTail_switch,headTail_child]
  rfl

lemma InputTree.lowCost_node (d : ℕ) (ξ : Card d → Bool) (T : Bool → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (d+1)) (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool))
    (η : Card d → Bool) :
    InputTree.lowCost (d+1) (d+1) (.node ξ T) e ((coinStepEquiv d).symm (Y,η)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => if b then butterflyPerm d (decodeButterfly d Y.2) * (T true).perm⁻¹
          else butterflyPerm d (decodeButterfly d Y.1) * (T false).perm⁻¹) +
        InputTree.lowCost d d (T false) (PairRouting.childEmbedding x c hc false) Y.1 +
        InputTree.lowCost d d (T true) (PairRouting.childEmbedding x c hc true) Y.2 := by
  dsimp only
  rw [InputTree.lowCost,Finset.sum_range_succ,InputTree.levelCost_node,ite_eq_left rfl]
  have he : (∑ i ∈ Finset.range d,
      (.node ξ T : InputTree (d+1)).levelCost (i+1) e ((coinStepEquiv d).symm (Y,η))) =
      InputTree.lowCost d d (T false)
        (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ) (PairRouting.colors_compatible _ _) false) Y.1 +
      InputTree.lowCost d d (T true)
        (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ) (PairRouting.colors_compatible _ _) true) Y.2 := by
    rw [InputTree.lowCost,InputTree.lowCost,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [InputTree.levelCost_node,ite_eq_right (by simp only [Finset.mem_range] at hi; omega : i+1 ≠ d+1)]
  rw [he]
  omega

noncomputable def modifiedAssignmentCost (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (x : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hc : PairRouting.Compatible x c) (ω : ModifiedCoins L r × ModifiedCoins L r) : ℕ :=
  PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hc)
    (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) +
  modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hc false) ω.1 +
  modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hc true) ω.2

lemma modifiedCost_step (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r+1))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedCost L (r+1) E e ((modifiedStepEquiv L r).symm (ω,coins)) =
      modifiedAssignmentCost L r E (e.trans (headTailEquiv (L+r)).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) coins.1)
        (PairRouting.colors_compatible _ _) ω := by
  rw [modifiedCost,modifiedInputTree_node]
  change InputTree.lowCost (L+r+1) (L+r+1) _ e
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)) = _
  rw [InputTree.lowCost_node]
  unfold modifiedAssignmentCost
  dsimp only
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [PairRouting.switchedEmbedding_eq_colored _ _ (PairRouting.colors_compatible _ _) _ rfl]
  congr 2

end CubeShuffle

namespace CubeShuffle
namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

omit [Fintype α] [DecidableEq ι] in
lemma childEmbedding_surjective (x : ι ↪ Bool × α) (hx : Function.Surjective x)
    (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    Function.Surjective (childEmbedding x c hc b) := by
  intro y
  have hs : Function.Surjective (coloredEmbedding x c hc) :=
    (pairLayer (chosenCoin x c)).surjective.comp hx
  obtain ⟨i,hi⟩ := hs (b,y)
  rw [coloredEmbedding_apply] at hi
  exact ⟨⟨i,congrArg Prod.fst hi⟩,congrArg Prod.snd hi⟩

omit [DecidableEq ι] in
lemma uniformPerm_tuple_upper (e f : ι ↪ α) (he : Function.Surjective e) (p : Equiv.Perm α) :
    finiteMean (fun u : Equiv.Perm α => if ∀ i, (p*u⁻¹) (e i) = f i then (1:ℝ) else 0) ≤
      1/(Fintype.card (Equiv.Perm α):ℝ) := by
  classical
  let M : Equiv.Perm α → Prop := fun u => ∀ i, (p*u⁻¹) (e i) = f i
  have huniq (u v : Equiv.Perm α) (hu : M u) (hv : M v) : u = v := by
    have hh : p*u⁻¹ = p*v⁻¹ := by
      ext x
      obtain ⟨i,rfl⟩ := he x
      exact (hu i).trans (hv i).symm
    exact inv_injective (mul_left_cancel hh)
  unfold finiteMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  change (∑ u, if M u then (1:ℝ) else 0) ≤ 1
  by_cases h : ∃ u, M u
  · obtain ⟨u,hu⟩ := h
    rw [Finset.sum_eq_single u]
    · simp only [hu,↓reduceIte,le_refl]
    · intro v _ hv
      exact ite_eq_right (fun hh => hv (huniq v u hh hu))
    · simp
  · push Not at h
    simp only [h,ite_false,Finset.sum_const_zero,zero_le_one]

end PairRouting

noncomputable def centralFactor (L r : ℕ) (E : Finset (Card r)) (a : ℝ) : ℝ :=
  (Nat.factorial (2^L):ℝ)^(-((2:ℝ)^r-E.card)*a)

lemma centralFactor_nonneg (L r : ℕ) (E : Finset (Card r)) (a : ℝ) :
    0 ≤ centralFactor L r E a := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma centralFactor_step (L r : ℕ) (E : Finset (Card (r+1))) (a : ℝ) :
    centralFactor L (r+1) E a =
      centralFactor L r (exceptionChild E false) a * centralFactor L r (exceptionChild E true) a := by
  unfold centralFactor
  rw [←Real.rpow_add (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  congr 1
  have he : ((exceptionChild E false).card:ℝ)+(exceptionChild E true).card = E.card := by
    exact_mod_cast exceptionChild_card_add E
  rw [pow_succ,←he]
  ring

lemma modifiedPerm_zero (L : ℕ) (E : Finset (Card 0)) (ω : ModifiedCoins L 0) :
    modifiedPerm L 0 E ω =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1
      else butterflyPerm L (decodeButterfly L ω.2.1)*(ω.1 (fun j => Fin.elim0 j))⁻¹ := by
  unfold modifiedPerm modifiedInputTree boundaryTree InputTree.perm modifiedBoundary boundaryOutput
  split_ifs
  · exact mul_inv_cancel _
  · rfl

lemma modifiedCost_zero (L : ℕ) (E : Finset (Card 0)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card L) (ω : ModifiedCoins L 0) : modifiedCost L 0 E e ω = 0 := by
  simp only [modifiedCost,modifiedInputTree,boundaryTree,InputTree.lowCost,
    InputTree.levelCost,Finset.sum_const_zero]

lemma centralFactor_zero (L : ℕ) (E : Finset (Card 0)) (a : ℝ) :
    centralFactor L 0 E a =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else (Nat.factorial (2^L):ℝ)^(-a) := by
  classical
  let z : Card 0 := fun j => Fin.elim0 j
  have he : (E.card:ℝ) = if z ∈ E then 1 else 0 := by
    by_cases hz : z ∈ E
    · have he : E = {z} := by
        ext u
        rw [Subsingleton.elim u z]
        simp only [hz,Finset.mem_singleton]
      rw [he,ite_eq_left (by simpa only [he] using hz),Finset.card_singleton,Nat.cast_one]
    · have he : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun u hu => hz (Subsingleton.elim u z ▸ hu))
      rw [he,Finset.card_empty,Nat.cast_zero,ite_eq_right (by simp)]
  unfold centralFactor
  rw [pow_zero,he]
  split_ifs <;> simp

lemma modified_probability_zero_le (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (he : Function.Surjective e) :
    PairRouting.tupleProbability (modifiedPerm L 0 E) e f ≤
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else 1/(Nat.factorial (2^L):ℝ) := by
  classical
  rw [PairRouting.tupleProbability,finiteMean_prod,finiteMean_comm]
  let B : ℝ := if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else 1/(Nat.factorial (2^L):ℝ)
  change _ ≤ B
  calc
    _ ≤ finiteMean (fun _ω : BenesCoins L => B) := by
      apply finiteMean_mono
      intro ω
      simp only [modifiedPerm_zero]
      by_cases h : (fun j => Fin.elim0 j : Card 0) ∈ E
      · simp only [h,↓reduceIte,Equiv.Perm.one_apply,finiteMean_const,B]
        split_ifs <;> norm_num
      · simp only [h,↓reduceIte,B]
        rw [finiteMean_pi_eval (A := fun _ : Card 0 => Equiv.Perm (Card L)) (fun j => Fin.elim0 j) (fun u : Equiv.Perm (Card L) =>
          if ∀ i, (butterflyPerm L (decodeButterfly L ω.1)*u⁻¹) (e i) = f i then (1:ℝ) else 0)]
        convert PairRouting.uniformPerm_tuple_upper e f he (butterflyPerm L (decodeButterfly L ω.1)) using 1
        rw [Fintype.card_perm,card_positions]
    _ = _ := finiteMean_const B

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

end CubeShuffle

namespace CubeShuffle

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


end CubeShuffle

namespace CubeShuffle

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


end CubeShuffle

namespace CubeShuffle

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

end CubeShuffle

namespace CubeShuffle

/-- The precise recursive pointwise density estimate: the surviving power is
under the actual, independent fair switch law, never an auxiliary coloring law. -/
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


end CubeShuffle

namespace CubeShuffle

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

/-- FAC.2 with the exact finite factorial normalization and actual modified law. -/
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

end CubeShuffle

namespace CubeShuffle

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

end CubeShuffle

namespace CubeShuffle

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

/-- The second quantitative row-density assertion: after fixing the absolute
block size and then the exceptional fraction, every sufficiently large full
permutation row has logarithmic moment rate as small as prescribed. -/
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

end CubeShuffle

end OAI
