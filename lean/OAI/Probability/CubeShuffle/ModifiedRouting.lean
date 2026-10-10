import OAI.Probability.CubeShuffle.DensityMoments

namespace OAI

namespace CubeShuffle
section CyclePerturbation
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_eq_of_agree (p q : Equiv.Perm α) (x : α)
    (h : ∀ z ∈ orbitSet p x, p z = q z) : orbitSet p x = orbitSet q x := by
  have hp (n : ℕ) : (p^n) x ∈ orbitSet p x := by
    apply (mem_orbitSet _ _ _).mpr
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have he (n : ℕ) : (p^n) x = (q^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,←ih]
      exact h _ (hp n)
  ext y
  simp only [mem_orbitSet]
  constructor
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,←he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

noncomputable def survivingCycle (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S)
    (hC : ∀ x ∈ C.val, x ∉ B) : RoutingNetwork.SelectedCycle q S := by
  refine ⟨C.val,?_,C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  refine ⟨x,hx.trans (orbitSet_eq_of_agree p q x ?_)⟩
  intro z hz
  exact h z (hC z (hx ▸ hz))

noncomputable def perturbCycleMap (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle q S ⊕ {x // x ∈ B} := by
  classical
  by_cases hb : ∃ x ∈ C.val, x ∈ B
  · exact Sum.inr ⟨hb.choose,hb.choose_spec.2⟩
  · exact Sum.inl (survivingCycle p q S B h C (by simpa only [not_exists,not_and] using hb))

lemma perturbCycleMap_injective (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) : Function.Injective (perturbCycleMap p q S B h) := by
  classical
  intro C D he
  by_cases hC : ∃ x ∈ C.val, x ∈ B <;>
    by_cases hD : ∃ x ∈ D.val, x ∈ B
  · simp only [perturbCycleMap,dite_eq_left hC,dite_eq_left hD,Sum.inr.injEq] at he
    have hx : hC.choose = hD.choose := congrArg Subtype.val he
    exact RoutingNetwork.SelectedCycle.eq_of_mem C D hC.choose_spec.1
      (hx.symm ▸ hD.choose_spec.1)
  · simp only [perturbCycleMap,dite_eq_left hC,dite_eq_right hD] at he
    cases he
  · simp only [perturbCycleMap,dite_eq_right hC,dite_eq_left hD] at he
    cases he
  · simp only [perturbCycleMap,dite_eq_right hC,dite_eq_right hD,Sum.inl.injEq] at he
    have hval : C.val = D.val := congrArg (fun Z : RoutingNetwork.SelectedCycle q S => Z.val) he
    exact Subtype.ext hval

/-- Changing a permutation on at most b specified inputs can destroy at most
b of its wholly marked cycles. This is the exceptional-block loss in FAC.2. -/
theorem selectedCycle_perturb_le (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) :
    Fintype.card (RoutingNetwork.SelectedCycle p S) ≤
      Fintype.card (RoutingNetwork.SelectedCycle q S)+B.card := by
  have hh := Fintype.card_le_of_injective _ (perturbCycleMap_injective p q S B h)
  simpa only [Fintype.card_sum,Fintype.card_coe] using hh

end CyclePerturbation
end CubeShuffle
namespace CubeShuffle
section PermDistance
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def permDistance (p q : Equiv.Perm α) : ℕ :=
  (Finset.univ.filter (fun x => p x ≠ q x)).card

lemma permDistance_sum (p q : Equiv.Perm α) :
    permDistance p q = ∑ x : α, if p x = q x then 0 else 1 := by
  classical
  simp [permDistance,Finset.card_filter]

lemma permDistance_refl (p : Equiv.Perm α) : permDistance p p = 0 := by
  simp [permDistance]

lemma permDistance_le (p q : Equiv.Perm α) : permDistance p q ≤ Fintype.card α :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma permDistance_symm (p q : Equiv.Perm α) : permDistance p q = permDistance q p := by
  simp only [permDistance,ne_comm]

lemma permDistance_triangle (p q r : Equiv.Perm α) :
    permDistance p r ≤ permDistance p q+permDistance q r := by
  classical
  simp only [permDistance_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hpq : p x = q x <;> by_cases hqr : q x = r x <;>
    by_cases hpr : p x = r x <;> simp only [hpq,hqr,hpr,↓reduceIte] <;>
    omega

lemma permDistance_mul_left (p q g : Equiv.Perm α) :
    permDistance (g*p) (g*q) = permDistance p q := by
  classical
  unfold permDistance
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr g.injective.eq_iff

lemma permDistance_mul_right (p q g : Equiv.Perm α) :
    permDistance (p*g) (q*g) = permDistance p q := by
  classical
  simp only [permDistance_sum,Equiv.Perm.mul_apply]
  exact Fintype.sum_equiv g _ _ (fun _ => rfl)

lemma permDistance_inv (p q : Equiv.Perm α) : permDistance p⁻¹ q⁻¹ = permDistance p q := by
  have hh := permDistance_mul_left p⁻¹ q⁻¹ q
  have hhh := permDistance_mul_right (q*p⁻¹) 1 p
  simp only [mul_inv_cancel,one_mul,inv_mul_cancel_right] at hh hhh
  rw [←hhh] at hh
  rw [←hh,permDistance_symm]

lemma permDistance_mul_le (p q g h : Equiv.Perm α) :
    permDistance (p*g) (q*h) ≤ permDistance p q+permDistance g h := by
  have hh := permDistance_triangle (p*g) (q*g) (q*h)
  simpa only [permDistance_mul_left,permDistance_mul_right] using hh

lemma selectedCycle_distance_le (p q : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle p S) ≤
      Fintype.card (RoutingNetwork.SelectedCycle q S)+permDistance p q := by
  apply selectedCycle_perturb_le
  intro x hx
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx

lemma permDistance_alternating (p q : Equiv.Perm α) :
    permDistance (CycleColoring.alternatingPerm p) (CycleColoring.alternatingPerm q) = permDistance p q := by
  classical
  simp only [permDistance_sum,Fintype.sum_prod_type,Fintype.sum_bool]
  simp [CycleColoring.alternatingPerm]

lemma alternatingCycles_distance_le {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × α) (p q : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤ PairRouting.alternatingCycles e q+
      (permDistance (p false) (q false)+permDistance (p true) (q true)) := by
  have hh := selectedCycle_distance_le
    (CycleColoring.alternatingPerm (PairRouting.alternatingProjection p))
    (CycleColoring.alternatingPerm (PairRouting.alternatingProjection q)) (PairRouting.labelSet e)
  rw [permDistance_alternating] at hh
  apply hh.trans
  apply Nat.add_le_add_left
  dsimp only [PairRouting.alternatingProjection]
  exact (permDistance_mul_le _ _ _ _).trans_eq (by
    change permDistance (p false)⁻¹ (q false)⁻¹ + _ = _
    rw [permDistance_inv])

end PermDistance
end CubeShuffle
namespace CubeShuffle

/-- An arbitrary independent permutation on each fixed central size-2^L block. -/
def centralBlockPerm (L : ℕ) : (r : ℕ) → (Card r → Equiv.Perm (Card L)) →
    Equiv.Perm (Card (L+r))
  | 0, C => C (fun j => Fin.elim0 j)
  | r+1, C => childLift (fun b => centralBlockPerm L r (fun u => C (Fin.cons b u)))

/-- A genuine palindrome with a specified permutation inserted in each central
block. Fair coins below that boundary will later be absorbed or cancelled. -/
def centralPalindromePerm (L r : ℕ) (C : Card r → Equiv.Perm (Card L))
    (ω : BenesCoins (L+r)) : Equiv.Perm (Card (L+r)) :=
  butterflyPerm (L+r) (decodeButterfly (L+r) ω.1) * centralBlockPerm L r C *
    (butterflyPerm (L+r) (decodeButterfly (L+r) ω.2))⁻¹

lemma centralPalindromePerm_step (L r : ℕ) (C : Card (r+1) → Equiv.Perm (Card L))
    (c : BenesCoins (L+r) × BenesCoins (L+r))
    (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    centralPalindromePerm L (r+1) C ((benesStepEquiv (L+r)).symm (c,coins)) =
      pairSwitch coins.2 * childLift (fun b => centralPalindromePerm L r
        (fun u => C (Fin.cons b u)) (if b then c.2 else c.1)) * pairSwitch coins.1 := by
  change ((butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
      ((coinStepEquiv (L+r)).symm ((c.1.1,c.2.1),coins.2))))) *
    childLift (fun b => centralBlockPerm L r (fun u => C (Fin.cons b u))) *
    (butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
      ((coinStepEquiv (L+r)).symm ((c.1.2,c.2.2),coins.1))))⁻¹ = _
  rw [butterflyPerm_step,butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
  simp only [mul_assoc]
  rw [←mul_assoc (childLift _),childLift_mul,←mul_assoc (childLift _),childLift_mul]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

/-- The actual alternating cycles at one expanded height, with the central
permutations left arbitrary. No low-level cycles are counted. -/
noncomputable def centralLevelCost (t L : ℕ) : (r : ℕ) →
    (Card r → Equiv.Perm (Card L)) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card (L+r)) → BenesCoins (L+r) → ℕ
  | 0, _, _, _, _, _ => 0
  | r+1, C, _, _, e, ω =>
    let σ := benesStepEquiv (L+r) ω
    let x := e.trans (headTailEquiv (L+r)).toEmbedding
    let c := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    if t = L+r+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
      (fun b => centralPalindromePerm L r (fun u => C (Fin.cons b u)) (if b then σ.1.2 else σ.1.1))
    else centralLevelCost t L r (fun u => C (Fin.cons false u))
      (PairRouting.childEmbedding x c hc false) σ.1.1 +
      centralLevelCost t L r (fun u => C (Fin.cons true u))
      (PairRouting.childEmbedding x c hc true) σ.1.2

noncomputable def centralSlabCost (l L r : ℕ) (C : Card r → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : BenesCoins (L+r)) : ℕ :=
  ∑ i : Fin l, centralLevelCost (l+i.val+1) L r C e ω

lemma permDistance_childLift (d : ℕ) (p q : Bool → Equiv.Perm (Card d)) :
    permDistance (childLift p) (childLift q) =
      permDistance (p false) (q false)+permDistance (p true) (q true) := by
  classical
  rw [permDistance_sum]
  have hh : (∑ x : Card (d+1), if childLift p x = childLift q x then 0 else 1) =
      ∑ x : Bool × Card d, if p x.1 x.2 = q x.1 x.2 then 0 else 1 := by
    apply Fintype.sum_equiv (headTailEquiv d)
    intro x
    have hx : (headTailEquiv d) x = (x 0,Fin.tail x) := rfl
    rw [hx]
    congr 1
    apply propext
    constructor
    · intro h
      have ht := congrArg Fin.tail h
      simpa only [childLift,Equiv.coe_fn_mk,Fin.tail_cons] using ht
    · intro h
      dsimp only [childLift,Equiv.coe_fn_mk]
      exact congrArg (fun z : Card d => (Fin.cons (x 0) z : Card (d+1))) h
  rw [hh]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,permDistance_sum]
  omega

noncomputable def centralDistance (L r : ℕ) (C D : Card r → Equiv.Perm (Card L)) : ℕ :=
  ∑ u : Card r, permDistance (C u) (D u)

lemma centralDistance_step (L r : ℕ) (C D : Card (r+1) → Equiv.Perm (Card L)) :
    centralDistance L (r+1) C D =
      centralDistance L r (fun u => C (Fin.cons false u)) (fun u => D (Fin.cons false u))+
      centralDistance L r (fun u => C (Fin.cons true u)) (fun u => D (Fin.cons true u)) := by
  classical
  unfold centralDistance
  rw [Fintype.sum_equiv (headTailEquiv r) _
    (fun x : Bool × Card r => permDistance (C (Fin.cons x.1 x.2)) (D (Fin.cons x.1 x.2)))
      (fun x => by
        change permDistance (C x) (D x) =
          permDistance (C (Fin.cons (x 0) (Fin.tail x))) (D (Fin.cons (x 0) (Fin.tail x)))
        rw [Fin.cons_self_tail])]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  omega

lemma permDistance_centralBlock (L r : ℕ) (C D : Card r → Equiv.Perm (Card L)) :
    permDistance (centralBlockPerm L r C) (centralBlockPerm L r D) = centralDistance L r C D := by
  induction r with
  | zero =>
    simp only [centralBlockPerm,centralDistance,Fintype.sum_unique]
    congr 1
  | succ r ih =>
    rw [centralBlockPerm,centralBlockPerm,permDistance_childLift,centralDistance_step,ih,ih]

lemma permDistance_centralPalindrome (L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    (ω : BenesCoins (L+r)) :
    permDistance (centralPalindromePerm L r C ω) (centralPalindromePerm L r D ω) =
      centralDistance L r C D := by
  rw [centralPalindromePerm,centralPalindromePerm,permDistance_mul_right,
    permDistance_mul_left,permDistance_centralBlock]

lemma centralLevelCost_step (t L r : ℕ) (C : Card (r+1) → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r+1))
    (ω : BenesCoins (L+r) × BenesCoins (L+r))
    (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    centralLevelCost t L (r+1) C e ((benesStepEquiv (L+r)).symm (ω,coins)) =
      let x := e.trans (headTailEquiv (L+r)).toEmbedding
      let c := PairRouting.colors x coins.1
      let hc := PairRouting.colors_compatible x coins.1
      if t = L+r+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x coins.1)
        (fun b => centralPalindromePerm L r (fun u => C (Fin.cons b u)) (if b then ω.2 else ω.1))
      else centralLevelCost t L r (fun u => C (Fin.cons false u))
        (PairRouting.childEmbedding x c hc false) ω.1 +
        centralLevelCost t L r (fun u => C (Fin.cons true u))
        (PairRouting.childEmbedding x c hc true) ω.2 := by
  rw [centralLevelCost]
  rfl

lemma centralLevelCost_perturb (t L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : BenesCoins (L+r)) :
    centralLevelCost t L r C e ω ≤ centralLevelCost t L r D e ω+centralDistance L r C D := by
  induction r generalizing ι with
  | zero => simp only [centralLevelCost,Nat.zero_add,Nat.zero_le]
  | succ r ih =>
    rw [←(benesStepEquiv (L+r)).symm_apply_apply ω,centralLevelCost_step,centralLevelCost_step]
    dsimp only
    split_ifs with ht
    · have hh := alternatingCycles_distance_le
        (PairRouting.switchedEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (benesStepEquiv (L+r) ω).2.1)
        (fun b => centralPalindromePerm L r (fun u => C (Fin.cons b u))
          (if b then (benesStepEquiv (L+r) ω).1.2 else (benesStepEquiv (L+r) ω).1.1))
        (fun b => centralPalindromePerm L r (fun u => D (Fin.cons b u))
          (if b then (benesStepEquiv (L+r) ω).1.2 else (benesStepEquiv (L+r) ω).1.1))
      simpa only [Bool.false_eq_true,↓reduceIte,permDistance_centralPalindrome,←centralDistance_step] using hh
    · rw [centralDistance_step]
      have h₀ := ih (fun u => C (Fin.cons false u)) (fun u => D (Fin.cons false u))
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (benesStepEquiv (L+r) ω).2.1)
          (PairRouting.colors_compatible _ _) false)
        (benesStepEquiv (L+r) ω).1.1
      have h₁ := ih (fun u => C (Fin.cons true u)) (fun u => D (Fin.cons true u))
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (benesStepEquiv (L+r) ω).2.1)
          (PairRouting.colors_compatible _ _) true)
        (benesStepEquiv (L+r) ω).1.2
      omega

lemma centralSlabCost_perturb (l L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : BenesCoins (L+r)) :
    centralSlabCost l L r C e ω ≤ centralSlabCost l L r D e ω+l*centralDistance L r C D := by
  have hh := Finset.sum_le_sum (fun (i : Fin l) (_ : i ∈ Finset.univ) =>
    centralLevelCost_perturb (l+i.val+1) L r C D e ω)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,centralSlabCost] using hh

lemma centralDistance_exceptional (L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    (E : Finset (Card r)) (h : ∀ u ∉ E, C u = D u) :
    centralDistance L r C D ≤ E.card*2^L := by
  classical
  calc
    _ ≤ ∑ u : Card r, if u ∈ E then 2^L else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs with hu
      · simpa only [card_positions] using permDistance_le (C u) (D u)
      · rw [h u hu,permDistance_refl]
    _ = _ := by simp

end CubeShuffle
namespace CubeShuffle

/-- A recursively paired input routing that may stop at any central block.
The leaf maps are genuine permutations, not probabilistic hypotheses. -/
inductive InputTree : ℕ → Type
  | tip {d : ℕ} (p : Equiv.Perm (Card d)) : InputTree d
  | node {d : ℕ} (ξ : Card d → Bool) (T : Bool → InputTree d) : InputTree (d+1)

def InputTree.perm : {d : ℕ} → InputTree d → Equiv.Perm (Card d)
  | _, .tip p => p
  | _, .node ξ T => pairSwitch ξ * childLift (fun b => (T b).perm)

noncomputable def InputTree.levelCost (t : ℕ) : {d : ℕ} → InputTree d →
    {ι : Type*} → [Fintype ι] → (ι ↪ Card d) → (SwitchIndex d → Bool) → ℕ
  | _, .tip _, _, _, _, _ => 0
  | d+1, .node ξ T, _, _, e, Y =>
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x ξ
    let hc := PairRouting.colors_compatible x ξ
    let σ := coinStepEquiv d Y
    if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
      (fun b => if b then butterflyPerm d (decodeButterfly d σ.1.2) * (T true).perm⁻¹
        else butterflyPerm d (decodeButterfly d σ.1.1) * (T false).perm⁻¹)
    else (T false).levelCost t (PairRouting.childEmbedding x c hc false) σ.1.1 +
      (T true).levelCost t (PairRouting.childEmbedding x c hc true) σ.1.2

lemma InputTree.levelCost_node (t d : ℕ) (ξ : Card d → Bool) (T : Bool → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (d+1))
    (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (η : Card d → Bool) :
    (InputTree.node ξ T).levelCost t e ((coinStepEquiv d).symm (Y,η)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => if b then butterflyPerm d (decodeButterfly d Y.2) * (T true).perm⁻¹
          else butterflyPerm d (decodeButterfly d Y.1) * (T false).perm⁻¹)
      else (T false).levelCost t (PairRouting.childEmbedding x c hc false) Y.1 +
        (T true).levelCost t (PairRouting.childEmbedding x c hc true) Y.2 := by
  rw [InputTree.levelCost]
  rfl

lemma InputTree.levelCost_gt (t d : ℕ) (T : InputTree d) (ht : d < t)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    T.levelCost t e Y = 0 := by
  induction T generalizing ι with
  | tip p => rfl
  | @node d ξ T ih =>
    rw [InputTree.levelCost,ite_eq_right (by omega : t ≠ d+1),ih false (by omega),ih true (by omega)]

lemma InputTree.levelCost_adapted (t d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (t-1) (fun Y => T.levelCost t e Y) := by
  induction T generalizing ι with
  | tip p => intro Y Y' _; rfl
  | @node d ξ T ih =>
    intro Y Y' h
    dsimp only
    conv_lhs => rw [←(coinStepEquiv d).symm_apply_apply Y]
    conv_rhs => rw [←(coinStepEquiv d).symm_apply_apply Y']
    rw [InputTree.levelCost_node t d ξ T e ((coinStepEquiv d Y).1) ((coinStepEquiv d Y).2),
      InputTree.levelCost_node t d ξ T e ((coinStepEquiv d Y').1) ((coinStepEquiv d Y').2)]
    by_cases ht : t = d+1
    · subst t
      rw [ite_eq_left rfl,ite_eq_left rfl]
      have he₀ : (coinStepEquiv d Y).1.1 = (coinStepEquiv d Y').1.1 := by
        funext i
        exact h (Sum.inr (false,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      have he₁ : (coinStepEquiv d Y).1.2 = (coinStepEquiv d Y').1.2 := by
        funext i
        exact h (Sum.inr (true,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      rw [he₀,he₁]
    · rw [ite_eq_right ht,ite_eq_right ht]
      congr 1
      · apply ih false
        intro i hi
        exact h (Sum.inr (false,i)) hi
      · apply ih true
        intro i hi
        exact h (Sum.inr (true,i)) hi

/-- The same fresh-layer bound is valid with arbitrary fixed central input
maps. This is needed for, and preserves, the exceptional-block construction. -/
theorem InputTree.level_partial_mgf (r s u : ℕ) (hu : u < r)
    (T : InputTree (s+r)) {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r))
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(T.levelCost (s+u+1) e (assembleBits r s lo hi))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient u J q) := by
  classical
  induction r generalizing u ι with
  | zero => omega
  | succ r ih =>
    simp only [Nat.add_succ] at *
    cases T with
    | tip p =>
      simp only [InputTree.levelCost,pow_zero,finiteMean_const]
      exact Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (cycleCoefficient_nonneg u J q hq))
    | node ξ T =>
      let x := e.trans (headTailEquiv (s+r)).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      let e₀ := PairRouting.childEmbedding x c hc false
      let e₁ := PairRouting.childEmbedding x c hc true
      let e' := PairRouting.switchedEmbedding x ξ
      let lo₀ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons false j.1,j.2)
      let lo₁ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons true j.1,j.2)
      let Y₀ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₀ hi
      let Y₁ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₁ hi
      let N := fun hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool) =>
        PairRouting.alternatingCycles e' (fun b =>
          if b then butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi.2)) * (T true).perm⁻¹
          else butterflyPerm (s+r) (decodeButterfly (s+r) (Y₀ hi.1)) * (T false).perm⁻¹)
      let L₀ := fun hi : Card s × SwitchIndex r → Bool =>
        (T false).levelCost (s+u+1) e₀ (Y₀ hi)
      let L₁ := fun hi : Card s × SwitchIndex r → Bool =>
        (T true).levelCost (s+u+1) e₁ (Y₁ hi)
      have hs (hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool))
          (η : Card s × Card r → Bool) :
          (InputTree.node ξ T).levelCost (s+u+1) e
            (assembleBits (r+1) s lo ((highStepEquiv r s).symm (hi,η))) =
            if u = r then N hi else L₀ hi.1 + L₁ hi.2 := by
        rw [assembleBits_step]
        rw [InputTree.levelCost_node (s+u+1) (s+r) ξ T e (Y₀ hi.1,Y₁ hi.2) (fun y => η (((cardSplit r s) y).2,((cardSplit r s) y).1))]
        simp only [Nat.add_right_cancel_iff,Nat.add_left_cancel_iff]
        rfl
      rw [finiteMean_equiv (highStepEquiv r s),finiteMean_prod]
      simp_rw [hs,finiteMean_const]
      by_cases hur : u = r
      · subst u
        simp only [ite_true]
        rw [finiteMean_prod,finiteMean_comm]
        calc
          _ ≤ finiteMean (fun _hi : Card s × SwitchIndex r → Bool =>
            Real.exp (Fintype.card ι * cycleCoefficient r J q)) := by
            apply finiteMean_mono
            intro hi
            have hn := node_partial_mgf r s e' (T false).perm (T true).perm
              (butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi))) lo₀ J hJ q hq
            exact hn
          _ = _ := finiteMean_const _
      · simp only [ite_eq_right hur,pow_add]
        rw [finiteMean_prod_mul (fun hi => q ^ L₀ hi) (fun hi => q ^ L₁ hi)]
        have hu' : u < r := by omega
        have h₀ := ih u hu' (T false) e₀ lo₀
        have h₁ := ih u hu' (T true) e₁ lo₁
        have hp := mul_le_mul h₀ h₁ (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.exp_nonneg _)
        refine hp.trans_eq ?_
        rw [←Real.exp_add]
        congr 1
        have hcount := PairRouting.color_card_add c
        have hcount' : (Fintype.card {i : ι // c i = false} : ℝ) +
            Fintype.card {i : ι // c i = true} = Fintype.card ι := by exact_mod_cast hcount
        change (Fintype.card {i : ι // c i = false} : ℝ) * cycleCoefficient u J q +
            Fintype.card {i : ι // c i = true} * cycleCoefficient u J q = _
        rw [←add_mul,hcount']

end CubeShuffle
namespace CubeShuffle

/-- Sum over a slab, padded by its actual zero costs when its levels exceed d. -/
noncomputable def InputTree.slabCost (l d : ℕ) (T : InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ i : Fin l, T.levelCost (l+i.1+1) e Y

lemma InputTree.slabCost_adapted (l d : ℕ) (T : InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) :
    LayerAdapted d (2*l) (fun Y => InputTree.slabCost l d T e Y) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (InputTree.levelCost_adapted (l+i.1+1) d T e) (by omega)

/-- The genuine conditional slab estimate: no independence is asserted among
node cycles or among levels in the slab. Jensen costs l on the exponent. -/
theorem InputTree.slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l) (T : InputTree (s+r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r))
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(InputTree.slabCost l (s+r) T e (assembleBits r s lo hi))) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  classical
  let : NeZero l := ⟨ne_of_gt hl⟩
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      finiteMean (fun i : Fin l => q^(l*T.levelCost (l+i.1+1) e
        (assembleBits r s lo hi)))) := by
      apply finiteMean_mono
      intro hi
      simpa only [InputTree.slabCost,Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin l => T.levelCost (l+i.1+1) e
          (assembleBits r s lo hi)) q hqp
    _ = finiteMean (fun i : Fin l => finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(l*T.levelCost (l+i.1+1) e (assembleBits r s lo hi)))) := finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin l =>
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64)))) := by
      apply finiteMean_mono
      intro i
      by_cases ht : l+i.1+1 ≤ s+r
      · have hs' : s ≤ l+i.1 := by omega
        have he : l+i.1+1 = s+(l+i.1-s)+1 := by omega
        have hu : l+i.1-s < r := by omega
        have hm := InputTree.level_partial_mgf r s (l+i.1-s) hu T e lo
          ⌈Real.exp ((l:ℝ)/32)⌉₊ (cycleCutoff_pos l) (q^l) (one_le_pow₀ hq)
        have hc := cycleCoefficient_decay l (l+i.1-s) (by
          rw [Nat.cast_sub hs',Nat.cast_add]
          have hsr : (2:ℝ)*s ≤ l := by exact_mod_cast hs
          have hi : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
          linarith) (q^l) (one_le_pow₀ hq) (by
            rw [Real.log_pow]
            nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l)])
        simp_rw [he,pow_mul]
        exact hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
      · have hz := InputTree.levelCost_gt (l+i.1+1) (s+r) T (by omega) e
        simp only [hz,Nat.mul_zero,pow_zero,finiteMean_const]
        exact Real.one_le_exp_iff.mpr (by positivity)
    _ = _ := finiteMean_const _

end CubeShuffle
namespace CubeShuffle

/-- A fixed central map in every block, with the genuine input-side fair
layers above the boundary. The coins below L are ignored on this side. -/
def boundaryTree (L : ℕ) : (r : ℕ) → (Card r → Equiv.Perm (Card L)) →
    (SwitchIndex (L+r) → Bool) → InputTree (L+r)
  | 0, U, _ => .tip (U (fun j => Fin.elim0 j))
  | r+1, U, X => .node (coinStepEquiv (L+r) X).2 (fun b =>
      boundaryTree L r (fun u => U (Fin.cons b u))
        (if b then (coinStepEquiv (L+r) X).1.2 else (coinStepEquiv (L+r) X).1.1))

/-- The actual output butterfly in one central block. -/
def boundaryOutput (L : ℕ) : (r : ℕ) → (SwitchIndex (L+r) → Bool) →
    Card r → Equiv.Perm (Card L)
  | 0, Y, _ => butterflyPerm L (decodeButterfly L Y)
  | r+1, Y, u => boundaryOutput L r
      (if u 0 then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) (Fin.tail u)

lemma boundaryOutput_adapted (L r : ℕ) :
    LayerAdapted (L+r) L (boundaryOutput L r) := by
  induction r with
  | zero =>
    intro Y Y' h
    have he : Y = Y' := funext (fun i => h i (by simpa only [Nat.add_zero] using switchHeight_le L i))
    rw [he]
  | succ r ih =>
    intro Y Y' h
    funext u
    dsimp only [boundaryOutput]
    cases hb : u 0 <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact congrFun (ih _ _ (fun i hi => h (Sum.inr (false,i)) hi)) (Fin.tail u)
    · exact congrFun (ih _ _ (fun i hi => h (Sum.inr (true,i)) hi)) (Fin.tail u)

/-- In an exceptional block the input map equals its output map, so the
central permutation is exactly identity. Elsewhere its inverse is uniform. -/
noncomputable def modifiedBoundary (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    Card r → Equiv.Perm (Card L) := fun u => if u ∈ E then boundaryOutput L r Y u else U u

lemma modifiedBoundary_adapted (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) :
    LayerAdapted (L+r) L (modifiedBoundary L r E U) := by
  intro Y Y' h
  unfold modifiedBoundary
  rw [boundaryOutput_adapted L r Y Y' h]

lemma permDistance_boundaryTree (L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) :
    permDistance (boundaryTree L r U X).perm (boundaryTree L r V X).perm =
      centralDistance L r U V := by
  induction r with
  | zero =>
    simp only [boundaryTree,InputTree.perm,centralDistance,Fintype.sum_unique]
    congr 1
  | succ r ih =>
    simp only [boundaryTree,InputTree.perm,permDistance_mul_left]
    rw [permDistance_childLift,centralDistance_step,ih,ih]

lemma boundaryTree_levelCost_perturb (t L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    (boundaryTree L r U X).levelCost t e Y ≤
      (boundaryTree L r V X).levelCost t e Y + centralDistance L r U V := by
  induction r generalizing ι with
  | zero => simp only [boundaryTree,InputTree.levelCost,Nat.zero_add,Nat.zero_le]
  | succ r ih =>
    rw [boundaryTree,boundaryTree,InputTree.levelCost,InputTree.levelCost]
    by_cases ht : t = L+r+1
    · simp only [ite_eq_left ht]
      have hh := alternatingCycles_distance_le
        (PairRouting.switchedEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (coinStepEquiv (L+r) X).2)
        (fun b => if b then butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.2) *
            (boundaryTree L r (fun u => U (Fin.cons true u)) (coinStepEquiv (L+r) X).1.2).perm⁻¹
          else butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.1) *
            (boundaryTree L r (fun u => U (Fin.cons false u)) (coinStepEquiv (L+r) X).1.1).perm⁻¹)
        (fun b => if b then butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.2) *
            (boundaryTree L r (fun u => V (Fin.cons true u)) (coinStepEquiv (L+r) X).1.2).perm⁻¹
          else butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.1) *
            (boundaryTree L r (fun u => V (Fin.cons false u)) (coinStepEquiv (L+r) X).1.1).perm⁻¹)
      simpa only [Bool.false_eq_true,↓reduceIte,permDistance_mul_left,permDistance_inv,
        permDistance_boundaryTree,←centralDistance_step] using hh
    · simp only [ite_eq_right ht,Bool.false_eq_true,↓reduceIte]
      rw [centralDistance_step]
      have h₀ := ih (fun u => U (Fin.cons false u)) (fun u => V (Fin.cons false u))
        (coinStepEquiv (L+r) X).1.1
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (coinStepEquiv (L+r) X).2)
          (PairRouting.colors_compatible _ _) false) (coinStepEquiv (L+r) Y).1.1
      have h₁ := ih (fun u => U (Fin.cons true u)) (fun u => V (Fin.cons true u))
        (coinStepEquiv (L+r) X).1.2
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (coinStepEquiv (L+r) X).2)
          (PairRouting.colors_compatible _ _) true) (coinStepEquiv (L+r) Y).1.2
      omega

lemma boundaryTree_slabCost_perturb (l L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y ≤
      InputTree.slabCost l (L+r) (boundaryTree L r V X) e Y + l*centralDistance L r U V := by
  have hh := Finset.sum_le_sum (fun (i : Fin l) (_ : i ∈ Finset.univ) =>
    boundaryTree_levelCost_perturb (l+i.val+1) L r U V X e Y)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,InputTree.slabCost] using hh

lemma modifiedBoundary_distance_le (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    centralDistance L r (modifiedBoundary L r E U Y) U ≤ E.card*2^L := by
  apply centralDistance_exceptional
  intro u hu
  exact ite_eq_right hu

end CubeShuffle
namespace CubeShuffle

lemma InputTree.slabCost_gt (l d : ℕ) (T : InputTree d) (hd : d ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.slabCost l d T e Y = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact InputTree.levelCost_gt _ _ T (by omega) _ _

lemma InputTree.random_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (F : (SwitchIndex d → Bool) → ℝ) (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => F Y*q^(InputTree.slabCost l d (T Y) e Y)) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  apply adapted_mul_mean_le r s F _ hF hA
  intro lo
  let hi₀ : Card s × SwitchIndex r → Bool := fun _ => false
  have he (hi : Card s × SwitchIndex r → Bool) :
      T (assembleBits r s lo hi) = T (assembleBits r s lo hi₀) :=
    hT _ _ (assembleBits_agree r s lo hi hi₀)
  simp_rw [he]
  exact InputTree.slab_partial_mgf r s l hl hs _ e lo q hq hlog

lemma InputTree.slab_mgf (l d : ℕ) (hl : 0 < l) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.slabCost l d T e Y)) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  have hh := InputTree.random_slab_adapted_mul_le d 0 l (Nat.zero_le _) hl (Nat.zero_le _)
    (fun _ => T) (fun _ _ _ => rfl) e (fun _ => 1) (fun _ => by norm_num)
    (fun _ _ _ => rfl) q hq hlog
  simpa only [one_mul,finiteMean_const] using hh

noncomputable def InputTree.familyCost (L n d : ℕ)
    (T : (SwitchIndex d → Bool) → InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ j ∈ Finset.range n, InputTree.slabCost (L*4^j) d (T Y) e Y

lemma InputTree.random_slabCost_adapted (l d s : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (max s (2*l)) (fun Y => InputTree.slabCost l d (T Y) e Y) := by
  intro Y Y' h
  dsimp only
  rw [hT _ _ (agreeThrough_mono (le_max_left _ _) h)]
  exact InputTree.slabCost_adapted l d (T Y') e Y Y'
    (agreeThrough_mono (le_max_right _ _) h)

lemma InputTree.familyCost_adapted (L n d s : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (max s (familyEnd L n)) (fun Y => InputTree.familyCost L n d T e Y) := by
  apply layerAdapted_sum
  intro j hj
  exact layerAdapted_mono (InputTree.random_slabCost_adapted (L*4^j) d s T hT e)
    (max_le_max_left s (familyEnd_ge L n j (Finset.mem_range.mp hj)))

/-- Only the first slab pays for the exceptional central maps. Later slabs
condition on them, using independent outward layers, exactly as FAC.2. -/
theorem InputTree.family_mgf_first (L n d s : ℕ) (hL : 0 < L) (hs : s ≤ L)
    (T : (SwitchIndex d → Bool) → InputTree d) (hT : LayerAdapted d s T)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) (p : ℝ) (hp : 0 ≤ p)
    (hfirst : finiteMean (fun Y => q^(InputTree.slabCost L d (T Y) e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*Real.exp (-(L:ℝ)/64)))) :
    finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*∑ j ∈ Finset.range n,
        Real.exp (-((L*4^j:ℕ):ℝ)/64))) := by
  induction n with
  | zero =>
    simp only [InputTree.familyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,add_zero]
    exact Real.one_le_exp hp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [InputTree.familyCost,Nat.zero_add,Finset.sum_range_one,pow_zero,mul_one] using hfirst
    · let l := L*4^n
      have hl : 0 < l := Nat.mul_pos hL (pow_pos (by decide) _)
      have hsl : 2*familyEnd L n ≤ l := familyEnd_two L n
      have hs' : s ≤ familyEnd L n := by
        have hh := familyEnd_ge L n 0 (Nat.pos_of_ne_zero hn)
        simp only [pow_zero,mul_one] at hh
        omega
      have hc : ∀ Y, InputTree.familyCost L (n+1) d T e Y =
          InputTree.familyCost L n d T e Y+InputTree.slabCost l d (T Y) e Y := by
        intro Y
        exact Finset.sum_range_succ _ _
      have hm : finiteMean (fun Y => q^(InputTree.familyCost L (n+1) d T e Y)) ≤
          finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) *
            Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
        by_cases hld : l ≤ d
        · simp_rw [hc,pow_add]
          apply InputTree.random_slab_adapted_mul_le d (familyEnd L n) l (by omega) hl hsl T
            (layerAdapted_mono hT hs') e _ (fun _ => pow_nonneg (by linarith) _)
          · apply layerAdapted_comp
            exact layerAdapted_mono (InputTree.familyCost_adapted L n d s T hT e) (max_le hs' le_rfl)
          · exact hq
          · exact hlog
        · simp_rw [hc,InputTree.slabCost_gt l d _ (by omega),Nat.add_zero]
          exact le_mul_of_one_le_right
            (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
            (Real.one_le_exp_iff.mpr (by positivity))
      refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
      rw [←Real.exp_add,Finset.sum_range_succ]
      congr 1
      dsimp only [l]
      ring

lemma InputTree.family_mgf_first_decay (L n d s : ℕ) (hL : 0 < L) (hs : s ≤ L)
    (T : (SwitchIndex d → Bool) → InputTree d) (hT : LayerAdapted d s T)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) (p : ℝ) (hp : 0 ≤ p)
    (hfirst : finiteMean (fun Y => q^(InputTree.slabCost L d (T Y) e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*Real.exp (-(L:ℝ)/64)))) :
    finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) ≤
      Real.exp (p+Fintype.card ι*heightDecay L) := by
  apply (InputTree.family_mgf_first L n d s hL hs T hT e q hq hlog p hp hfirst).trans
  apply Real.exp_le_exp.mpr
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using hh

end CubeShuffle
namespace CubeShuffle

noncomputable def modifiedInputTree (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X Y : SwitchIndex (L+r) → Bool) : InputTree (L+r) :=
  boundaryTree L r (modifiedBoundary L r E U Y) X

lemma modifiedInputTree_adapted (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool) :
    LayerAdapted (L+r) L (modifiedInputTree L r E U X) := by
  intro Y Y' h
  unfold modifiedInputTree
  rw [modifiedBoundary_adapted L r E U Y Y' h]

lemma modified_slab_mgf (l L r : ℕ) (hl : 0 < l) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (modifiedInputTree L r E U X Y) e Y)) ≤
      Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q+
        Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
  have hqp : 0 < q := by linarith
  have hpoint (Y : SwitchIndex (L+r) → Bool) :
      InputTree.slabCost l (L+r) (modifiedInputTree L r E U X Y) e Y ≤
        InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y+l*E.card*2^L := by
    apply (boundaryTree_slabCost_perturb l L r (modifiedBoundary L r E U Y) U X e Y).trans
    apply Nat.add_le_add_left
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left l (modifiedBoundary_distance_le L r E U Y)
  calc
    _ ≤ finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y+l*E.card*2^L)) :=
      finiteMean_mono (fun Y => pow_le_pow_right₀ hq (hpoint Y))
    _ = finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y)) *
        q^(l*E.card*2^L) := by simp_rw [pow_add]; exact finiteMean_mul_const _ _
    _ ≤ Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) * q^(l*E.card*2^L) :=
      mul_le_mul_of_nonneg_right (InputTree.slab_mgf l (L+r) hl _ e q hq hlog) (pow_nonneg (by linarith) _)
    _ = _ := by
      have he : Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q) = q^(l*E.card*2^L) := by
        rw [Real.exp_nat_mul,Real.exp_log hqp]
      rw [Real.exp_add,he,mul_comm]

lemma modified_family_mgf (l n L r : ℕ) (hl : 0 < l) (hLl : L ≤ l) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.familyCost l n (L+r) (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q+Fintype.card ι*heightDecay l) := by
  exact InputTree.family_mgf_first_decay l n (L+r) L hl hLl _
    (modifiedInputTree_adapted L r E U X) e q hq hlog _
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hq))
    (modified_slab_mgf l L r hl E U X e q hq hlog)

/-- The actual exceptional-block high-level moment: the exceptional loss is
paid in the first slab of each family only, not at every height. -/
theorem modified_high_mgf (L n r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(InputTree.familyCost L n (L+r) (modifiedInputTree L r E U X) e Y+
      InputTree.familyCost (2*L) n (L+r) (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log q) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/250 := by rw [Real.log_pow]; norm_num; linarith
  have h₀ := modified_family_mgf L n L r hL le_rfl E U X e (q^2) hq2 hlog2
  have h₁ := modified_family_mgf (2*L) n L r (by omega) (by omega) E U X e (q^2) hq2 hlog2
  have h₁' : finiteMean (fun Y => (q^2)^(InputTree.familyCost (2*L) n (L+r)
      (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp ((((2*L)*E.card*2^L:ℕ):ℝ)*Real.log (q^2)+Fintype.card ι*heightDecay L) := by
    apply h₁.trans
    apply Real.exp_le_exp.mpr
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (heightDecay_antitone (show L ≤ 2*L by omega)) (Nat.cast_nonneg _)) _
  have hh := finiteMean_mul_exp_le
    (fun Y => q^(InputTree.familyCost L n (L+r) (modifiedInputTree L r E U X) e Y))
    (fun Y => q^(InputTree.familyCost (2*L) n (L+r) (modifiedInputTree L r E U X) e Y))
    _ _ (by simpa only [pow_right_comm] using h₀) (by simpa only [pow_right_comm] using h₁')
  simp only [←pow_add] at hh
  refine hh.trans_eq ?_
  congr 1
  simp only [Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  ring

noncomputable def InputTree.lowCost (H d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ i ∈ Finset.range H, T.levelCost (i+1) e Y

lemma InputTree.lowCost_slab (L d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost L d T e Y+InputTree.slabCost L d T e Y = InputTree.lowCost (2*L) d T e Y := by
  rw [InputTree.lowCost,InputTree.lowCost,show 2*L=L+L by omega,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => T.levelCost (L+i+1) e Y) L

lemma InputTree.cost_family (L n d : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost L d (T Y) e Y + InputTree.familyCost L n d T e Y +
      InputTree.familyCost (2*L) n d T e Y = InputTree.lowCost (L*4^n) d (T Y) e Y := by
  induction n with
  | zero => simp only [InputTree.familyCost,Finset.range_zero,Finset.sum_empty,Nat.add_zero,
      pow_zero,mul_one]
  | succ n ih =>
    have he : (2*L)*4^n = 2*(L*4^n) := by ring
    have he' : L*4^(n+1) = 2*(2*(L*4^n)) := by rw [pow_succ]; ring
    simp only [InputTree.familyCost,Finset.sum_range_succ] at ih ⊢
    rw [he,he',←InputTree.lowCost_slab,←InputTree.lowCost_slab,←ih]
    omega

lemma InputTree.lowCost_ge (H d : ℕ) (hd : d ≤ H) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost H d T e Y = InputTree.lowCost d d T e Y := by
  symm
  apply Finset.sum_subset (Finset.range_mono hd)
  intro i _ hi
  have hi' : d ≤ i := by simpa only [Finset.mem_range,not_lt] using hi
  exact InputTree.levelCost_gt (i+1) d T (by omega) e Y

lemma boundaryTree_levelCost_low (t L r : ℕ) (ht : t ≤ L)
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    (boundaryTree L r U X).levelCost t e Y = 0 := by
  induction r generalizing ι with
  | zero => rfl
  | succ r ih =>
    rw [boundaryTree,InputTree.levelCost,ite_eq_right (by omega : t ≠ L+r+1),ih,ih]

lemma boundaryTree_lowCost_zero (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    InputTree.lowCost L (L+r) (boundaryTree L r U X) e Y = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact boundaryTree_levelCost_low (i+1) L r (by simpa only [Finset.mem_range,Nat.lt_iff_add_one_le] using hi) U X e Y

/-- Quantitative FAC.2 cycle moment, with fixed outer input layers and fixed
independent uniform central seeds. The latter may now be averaged freely. -/
theorem modified_cost_mgf (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E U X Y) e Y)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log q) := by
  have hbound : L+r ≤ L*4^(L+r) := by
    have h₀ := pow_four_ge (L+r)
    have h₁ := Nat.mul_le_mul_right (4^(L+r)) hL
    nlinarith
  have he (Y : SwitchIndex (L+r) → Bool) :=
    InputTree.cost_family L (L+r) (L+r) (modifiedInputTree L r E U X) e Y
  have hz (Y : SwitchIndex (L+r) → Bool) :
      InputTree.lowCost L (L+r) (modifiedInputTree L r E U X Y) e Y = 0 :=
    boundaryTree_lowCost_zero L r _ X e Y
  simp only [hz,Nat.zero_add,InputTree.lowCost_ge _ _ hbound] at he
  simp_rw [←he]
  exact modified_high_mgf L (L+r) r hL E U X e q hq hlog

end CubeShuffle

end OAI
