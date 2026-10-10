import Mathlib
import OAI.Probability.ThorpRouting.Tail.ParallelFollow

namespace OAI

namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators
open Filter
namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [Fintype α] in
lemma bipartitionFlip_injective (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x)) :
    Function.Injective (bipartitionFlip p S χ hχ) := by
  classical
  intro f g he
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ S
  · have hh := congrFun (congrArg Subtype.val he) x
    change (if x ∈ S then Bool.xor (f.val x) (χ x) else false) =
      (if x ∈ S then Bool.xor (g.val x) (χ x) else false) at hh
    simp only [ite_eq_left hx] at hh
    cases hfx : f.val x <;> cases hgx : g.val x <;> cases hcx : χ x <;> simp_all
  · exact (f.property.1 x hx).trans (g.property.1 x hx).symm

lemma card_opposite_le (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x)) :
    Fintype.card (OppositeColoring p S) ≤
      2 ^ ((boundary p S).card + Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  exact (Fintype.card_le_of_injective _ (bipartitionFlip_injective p S χ hχ)).trans
    (card_coloring_le p S)

def alternatingPerm (p : Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := if x.1 then (false,p x.2) else (true,x.2)
  invFun x := if x.1 then (false,x.2) else (true,p.symm x.2)
  left_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp
  right_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp

omit [Fintype α] [DecidableEq α] in
lemma alternatingPerm_flip (p : Equiv.Perm α) (x : Bool × α) :
    (alternatingPerm p x).1 = !x.1 := by
  rcases x with ⟨b,x⟩
  cases b <;> rfl

omit [Fintype α] [DecidableEq α] in
lemma alternating_step_sameCycle (p : Equiv.Perm α) (x : Bool × α) :
    p.SameCycle x.2 (alternatingPerm p x).2 := by
  rcases x with ⟨b,x⟩
  cases b
  · exact Equiv.Perm.SameCycle.refl p x
  · exact (Equiv.Perm.SameCycle.refl p x).apply_right

omit [DecidableEq α] in
lemma alternating_sameCycle_snd (p : Equiv.Perm α) {x y : Bool × α}
    (h : (alternatingPerm p).SameCycle x y) : p.SameCycle x.2 y.2 := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hp (k : ℕ) : p.SameCycle x.2 (((alternatingPerm p)^k) x).2 := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl p x.2
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ih.trans (alternating_step_sameCycle p _)
  exact hn ▸ hp n

omit [DecidableEq α] in
lemma alternating_zero_sameCycle (p : Equiv.Perm α) {x y : α}
    (h : p.SameCycle x y) : (alternatingPerm p).SameCycle (false,x) (false,y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hp (k : ℕ) : (alternatingPerm p).SameCycle (false,x) (false,(p^k) x) := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      have hs := ih.apply_right.apply_right
      simpa only [pow_succ',Equiv.Perm.mul_apply,alternatingPerm,Equiv.coe_fn_mk,
        Bool.false_eq_true,↓reduceIte] using hs
  simpa only [hn] using hp n

omit [Fintype α] [DecidableEq α] in
lemma alternating_sameCycle_zero (p : Equiv.Perm α) (x : Bool × α) :
    (alternatingPerm p).SameCycle x (false,x.2) := by
  rcases x with ⟨b,x⟩
  cases b
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact ((Equiv.Perm.SameCycle.refl (alternatingPerm p) (false,x)).apply_right).symm

omit [DecidableEq α] in
lemma alternating_sameCycle_iff (p : Equiv.Perm α) (x y : Bool × α) :
    (alternatingPerm p).SameCycle x y ↔ p.SameCycle x.2 y.2 := by
  constructor
  · exact alternating_sameCycle_snd p
  · intro h
    exact (alternating_sameCycle_zero p x).trans
      ((alternating_zero_sameCycle p h).trans (alternating_sameCycle_zero p y).symm)

lemma orbit_alternating (p : Equiv.Perm α) (x : Bool × α) :
    orbitSet (alternatingPerm p) x = childJoin (orbitSet p x.2) (orbitSet p x.2) := by
  ext ⟨b,y⟩
  simp only [mem_orbitSet,alternating_sameCycle_iff,mem_childJoin,ite_self]

omit [Fintype α] in
lemma boolFiber_childJoin (A B : Finset α) (b : Bool) :
    boolFiber (childJoin A B) b = if b then B else A := by
  ext x
  cases b <;> simp only [mem_boolFiber,mem_childJoin,Bool.false_eq_true,↓reduceIte]

noncomputable def projectCycle (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    RoutingNetwork.SelectedCycle p A := by
  refine ⟨boolFiber C.val false,?_,?_⟩
  · obtain ⟨x,hx⟩ := C.property.1
    refine ⟨x.2,?_⟩
    rw [hx,orbit_alternating,boolFiber_childJoin]
    rfl
  · intro x hx
    exact (mem_childJoin A B false x).mp (C.property.2 ((mem_boolFiber _ _ _).mp hx))

lemma selected_alternating_eq (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    C.val = childJoin (projectCycle p A B C).val (projectCycle p A B C).val := by
  change C.val = childJoin (boolFiber C.val false) (boolFiber C.val false)
  obtain ⟨x,hx⟩ := C.property.1
  rw [hx,orbit_alternating,boolFiber_childJoin]
  rfl

lemma projectCycle_injective (p : Equiv.Perm α) (A B : Finset α) :
    Function.Injective (projectCycle p A B) := by
  intro C D he
  apply Subtype.ext
  rw [selected_alternating_eq p A B C,selected_alternating_eq p A B D,he]

lemma card_alternating_cycles_le (p : Equiv.Perm α) (A B : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) ≤
      Fintype.card (RoutingNetwork.SelectedCycle p A) :=
  Fintype.card_le_of_injective _ (projectCycle_injective p A B)

end CycleColoring

section PairAssignmentCount
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma mem_image_perm_iff (p : Equiv.Perm α) (A : Finset α) (y : α) :
    y ∈ A.image p ↔ p.symm y ∈ A := by
  constructor
  · intro h
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp h
    simpa only [←hxy,Equiv.symm_apply_apply] using hx
  · intro h
    exact Finset.mem_image.mpr ⟨p.symm y,h,p.apply_symm_apply y⟩

omit [Fintype α] in
lemma card_childJoin (A B : Finset α) : (childJoin A B).card = A.card+B.card := by
  have hd : Disjoint (A.image (fun x => (false,x))) (B.image (fun x => (true,x))) := by
    apply Finset.disjoint_left.mpr
    rintro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp hy
    exact Bool.false_ne_true (congrArg Prod.fst hba).symm
  have hi (b : Bool) : Function.Injective (fun x : α => (b,x)) :=
    fun _ _ h => congrArg Prod.snd h
  rw [childJoin,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective A (hi false),Finset.card_image_of_injective B (hi true)]

omit [Fintype α] in
lemma alternating_internal (p : Equiv.Perm α) (A B : Finset α) :
    ((childJoin A B).filter (fun x => (CycleColoring.alternatingPerm p).symm x ∈ childJoin A B)) =
      childJoin (A ∩ B.image p) (B ∩ A) := by
  ext ⟨b,x⟩
  rw [Finset.mem_filter]
  cases b <;> simp only [mem_childJoin,CycleColoring.alternatingPerm,
    Equiv.symm_mk,Equiv.coe_fn_mk,Bool.false_eq_true,↓reduceIte,Finset.mem_inter,mem_image_perm_iff]

omit [Fintype α] in
lemma alternating_boundary_card (p : Equiv.Perm α) (A B : Finset α) :
    (CycleColoring.boundary (CycleColoring.alternatingPerm p) (childJoin A B)).card =
      (A ∪ B).card + (A ∪ B.image p).card - (A.card+B.card) := by
  rw [CycleColoring.boundary_card,alternating_internal,card_childJoin,card_childJoin]
  have h₀ := Finset.card_union_add_card_inter A B
  have h₁ := Finset.card_union_add_card_inter A (B.image p)
  rw [Finset.card_image_of_injective _ p.injective] at h₁
  have h₂ := Finset.inter_comm B A
  rw [h₂]
  omega

lemma compatible_assignment_bound (p : Equiv.Perm α) (A B : Finset α) :
    Fintype.card (CycleColoring.OppositeColoring (CycleColoring.alternatingPerm p) (childJoin A B)) ≤
      2 ^ ((A ∪ B).card + (A ∪ B.image p).card - (A.card+B.card) +
        Fintype.card (RoutingNetwork.SelectedCycle p A)) := by
  have h := CycleColoring.card_opposite_le (CycleColoring.alternatingPerm p) (childJoin A B)
    Prod.fst (CycleColoring.alternatingPerm_flip p)
  rw [alternating_boundary_card] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_left (CycleColoring.card_alternating_cycles_le p A B) _))

end PairAssignmentCount

lemma finiteMean_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => h ω)) (Nat.cast_nonneg _)

lemma boolFiber_headTail (d : ℕ) (S : Finset (Card (d+1))) (b : Bool) :
    boolFiber (S.image (headTailEquiv d)) b = childMarks S b := by
  classical
  ext x
  rw [mem_boolFiber,mem_childMarks]
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    have hh := congrArg (headTailEquiv d).symm he
    rw [Equiv.symm_apply_apply] at hh
    change y = Fin.cons b x at hh
    exact hh ▸ hy
  · intro h
    exact Finset.mem_image.mpr ⟨Fin.cons b x,h,by rfl⟩

lemma prod_childMarks (d : ℕ) (S : Finset (Card (d+1))) (f : Card (d+1) → ℝ) :
    (∏ x ∈ S, f x) =
      (∏ x ∈ childMarks S false, f (Fin.cons false x)) *
      ∏ x ∈ childMarks S true, f (Fin.cons true x) := by
  classical
  have h := prod_boolFibers (S.image (headTailEquiv d)) (fun x => f ((headTailEquiv d).symm x))
  rw [Finset.prod_image (headTailEquiv d).injective.injOn,
    boolFiber_headTail,boolFiber_headTail] at h
  simp only [Equiv.symm_apply_apply] at h
  exact h

noncomputable def headAverage {d : ℕ} (p : Card (d+1) → ℝ) (y : Card d) : ℝ :=
  (p (Fin.cons false y)+p (Fin.cons true y))/2

lemma finiteMean_headAverage (d : ℕ) (p : Card (d+1) → ℝ) :
    finiteMean (headAverage p) = finiteMean p := by
  rw [finiteMean_equiv (headTailEquiv d),finiteMean_prod,finiteMean_comm]
  apply finiteMean_congr
  intro y
  rw [finiteMean_bool]
  rfl

lemma pairSwitch_product_bound (d : ℕ) (S : Finset (Card (d+1)))
    (p : Card (d+1) → ℝ) (hp : ∀ x, 0 ≤ p x) :
    finiteMean (fun ξ : Card d → Bool => ∏ x ∈ S, p (pairSwitch ξ x)) ≤
      ∏ x ∈ S, headAverage p (Fin.tail x) := by
  classical
  have h : CylinderBound (fun T => ∏ x ∈ T, p ((headTailEquiv d).symm x))
      (fun x => p ((headTailEquiv d).symm x)) := fun _ => le_rfl
  have hh := h.fair_parallel (fun x => hp _) (S.image (headTailEquiv d))
  simp only [Finset.prod_image (pairLayer _).injective.injOn,
    Finset.prod_image (headTailEquiv d).injective.injOn] at hh
  convert hh using 1
  · apply finiteMean_congr
    intro ξ
    apply Finset.prod_congr rfl
    intro x _
    rfl
  · apply Finset.prod_congr rfl
    intro x _
    change (p (Fin.cons false (Fin.tail x))+p (Fin.cons true (Fin.tail x)))/2 =
      (p (Fin.cons (x 0) (Fin.tail x))+p (Fin.cons (!(x 0)) (Fin.tail x)))/2
    cases x 0
    · rfl
    · simp only [Bool.not_true]
      ring

lemma butterflyPerm_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) :
    butterflyPerm (d+1) (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ))) =
    pairSwitch ξ * childLift (fun b => butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))) := by
  change pairSwitch (fun y => (coinStepEquiv d).symm (c,ξ) (Sum.inl y)) *
    childLift (fun b => butterflyPerm d (decodeButterfly d
      (fun i => (coinStepEquiv d).symm (c,ξ) (Sum.inr (b,i))))) = _
  apply congrArg₂ (· * ·)
  · rfl
  · apply congrArg childLift
    funext b
    apply congrArg (fun ω => butterflyPerm d (decodeButterfly d ω))
    funext i
    cases b <;> rfl

lemma butterfly_product_bound (d : ℕ) (S : Finset (Card d))
    (p : Card d → ℝ) (hp : ∀ x, 0 ≤ p x) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      ∏ x ∈ S, p (butterflyPerm d (decodeButterfly d ω) x)) ≤ (finiteMean p)^S.card := by
  classical
  induction d with
  | zero =>
    have he : p = fun _ => p (fun i => Fin.elim0 i) := by
      funext x
      exact congrArg p (Subsingleton.elim _ _)
    rw [he]
    simp only [Finset.prod_const,finiteMean_const,le_refl]
  | succ d ih =>
    let g : Card d → ℝ := headAverage p
    have hg : ∀ x, 0 ≤ g x := fun x => div_nonneg (add_nonneg (hp _) (hp _)) (by norm_num)
    rw [finiteMean_equiv (coinStepEquiv d),finiteMean_prod]
    calc
      _ ≤ finiteMean (fun c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool) =>
        (∏ x ∈ childMarks S false, g (butterflyPerm d (decodeButterfly d c.1) x)) *
        ∏ x ∈ childMarks S true, g (butterflyPerm d (decodeButterfly d c.2) x)) := by
        apply finiteMean_mono
        intro c
        let f : Equiv.Perm (Card (d+1)) := childLift (fun b =>
          butterflyPerm d (decodeButterfly d (if b then c.2 else c.1)))
        have hh := pairSwitch_product_bound d (S.image f) p hp
        simp only [Finset.prod_image f.injective.injOn] at hh
        convert hh using 1
        · apply finiteMean_congr
          intro ξ
          apply Finset.prod_congr rfl
          intro x _
          rw [butterflyPerm_step]
          rfl
        · rw [prod_childMarks]
          simp only [f,childLift,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons,
            Bool.false_eq_true,↓reduceIte]
          rfl
      _ = (finiteMean (fun c : SwitchIndex d → Bool =>
        ∏ x ∈ childMarks S false, g (butterflyPerm d (decodeButterfly d c) x))) *
        finiteMean (fun c : SwitchIndex d → Bool =>
        ∏ x ∈ childMarks S true, g (butterflyPerm d (decodeButterfly d c) x)) :=
          finiteMean_prod_mul
            (fun c : SwitchIndex d → Bool => ∏ x ∈ childMarks S false,
              g (butterflyPerm d (decodeButterfly d c) x))
            (fun c : SwitchIndex d → Bool => ∏ x ∈ childMarks S true,
              g (butterflyPerm d (decodeButterfly d c) x))
      _ ≤ (finiteMean g)^(childMarks S false).card * (finiteMean g)^(childMarks S true).card :=
        mul_le_mul (ih (childMarks S false) g hg) (ih (childMarks S true) g hg)
          (finiteMean_nonneg fun c => Finset.prod_nonneg (fun x _ => hg _))
          (pow_nonneg (finiteMean_nonneg hg) _)
      _ = (finiteMean p)^S.card := by
        rw [←pow_add,card_childMarks_add,finiteMean_headAverage]

noncomputable def inverseButterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω)).symm

lemma inverseButterflyMarks_inclusion (d : ℕ) (A S : Finset (Card d)) :
    inclusionMoment (inverseButterflyMarks d A) S ≤
      ((A.card : ℝ)/(2:ℝ)^d)^S.card := by
  classical
  let p : Card d → ℝ := fun x => if x ∈ A then 1 else 0
  have hm : finiteMean p = (A.card : ℝ)/(2:ℝ)^d := by
    simp only [finiteMean,p,card_positions,Nat.cast_pow,Nat.cast_ofNat]
    congr 1
    simp
  have he : inclusionMoment (inverseButterflyMarks d A) S =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        ∏ x ∈ S, p (butterflyPerm d (decodeButterfly d ω) x)) := by
    rw [inclusionMoment_eq]
    apply finiteMean_congr
    intro ω
    simp only [inverseButterflyMarks,subset_image_equiv_iff,Equiv.symm_symm,indicator_subset_prod,
      Finset.prod_image (butterflyPerm d (decodeButterfly d ω)).injective.injOn,p]
  rw [he]
  simpa only [hm] using butterfly_product_bound d S p (fun x => by dsimp [p]; split_ifs <;> norm_num)

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def occupied (x : ι → Bool × α) : Finset α :=
  Finset.univ.image (fun i => (x i).2)

omit [Fintype α] in
lemma mem_occupied (x : ι → Bool × α) (y : α) : y ∈ occupied x ↔ ∃ i, (x i).2 = y := by
  simp [occupied]

def required (x : ι → Bool × α) (c : ι → Bool) (i : ι) : Bool := Bool.xor (x i).1 (c i)

def Compatible (x : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i j, (x i).2 = (x j).2 → required x c i = required x c j

def colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) : Bool :=
  Bool.xor (x i).1 (ξ (x i).2)

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma required_colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) :
    required x (colors x ξ) i = ξ (x i).2 := by
  simp only [required,colors]
  cases (x i).1 <;> cases ξ (x i).2 <;> rfl

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma colors_compatible (x : ι → Bool × α) (ξ : α → Bool) : Compatible x (colors x ξ) := by
  intro i j he
  simp only [required_colors,he]

noncomputable def chosenCoin (x : ι → Bool × α) (c : ι → Bool) (y : α) : Bool := by
  classical
  exact if h : ∃ i, (x i).2 = y then required x c (Classical.choose h) else false

omit [Fintype α] in
lemma chosenCoin_apply (x : ι → Bool × α) (c : ι → Bool) (hc : Compatible x c) (i : ι) :
    chosenCoin x c (x i).2 = required x c i := by
  classical
  simp only [chosenCoin,dite_eq_left (show ∃ j, (x j).2 = (x i).2 from ⟨i,rfl⟩)]
  exact hc _ i (Classical.choose_spec (show ∃ j, (x j).2 = (x i).2 from ⟨i,rfl⟩))

omit [Fintype α] in
lemma colors_eq_iff (x : ι → Bool × α) (c : ι → Bool) (hc : Compatible x c) (ξ : α → Bool) :
    colors x ξ = c ↔ ∀ y ∈ occupied x, ξ y = chosenCoin x c y := by
  constructor
  · intro he y hy
    obtain ⟨i,rfl⟩ := (mem_occupied x y).mp hy
    rw [chosenCoin_apply x c hc i]
    rw [←he,required_colors]
  · intro he
    funext i
    apply (xor_eq_iff _ _ _).mpr
    exact (he _ ((mem_occupied x _).mpr ⟨i,rfl⟩)).trans (chosenCoin_apply x c hc i)

noncomputable instance (x : ι → Bool × α) (c : ι → Bool) : Decidable (Compatible x c) :=
  Classical.propDecidable _

lemma colors_probability (x : ι → Bool × α) (c : ι → Bool) :
    finiteMean (fun ξ : α → Bool => if colors x ξ = c then (1 : ℝ) else 0) =
      if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0 := by
  classical
  by_cases hc : Compatible x c
  · rw [ite_eq_left hc]
    have he := fun ξ => colors_eq_iff x c hc ξ
    simp only [he]
    exact mean_coinCylinder (occupied x) (chosenCoin x c)
  · rw [ite_eq_right hc]
    have he : ∀ ξ, colors x ξ ≠ c := fun ξ hh => hc (hh ▸ colors_compatible x ξ)
    simp only [he,ite_false,finiteMean_const]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma Compatible.tail_injective {x : ι ↪ Bool × α} {c : ι → Bool} (hc : Compatible x c) (b : Bool) :
    Function.Injective (fun i : {i : ι // c i = b} => (x i.val).2) := by
  intro i j he
  apply Subtype.ext
  apply x.injective
  apply Prod.ext
  · have hh := hc i j he
    simp only [required,i.property,j.property] at hh
    cases h₀ : (x i.val).1 <;> cases h₁ : (x j.val).1 <;> cases b <;> simp_all
  · exact he

def childEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    {i : ι // c i = b} ↪ α := ⟨fun i => (x i.val).2,hc.tail_injective b⟩


def lift (p : Bool → Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := (x.1,p x.1 x.2)
  invFun x := (x.1,(p x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

def sandwich (ξ η : α → Bool) (p : Bool → Equiv.Perm α) : Equiv.Perm (Bool × α) :=
  pairLayer η * lift p * pairLayer ξ

def ChildMatches (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i, p (c i) (x i).2 = (y i).2

noncomputable instance (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) :
    Decidable (ChildMatches p x y c) := Classical.propDecidable _

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma sandwich_matches_iff (ξ η : α → Bool) (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) :
    (∀ i, sandwich ξ η p (x i) = y i) ↔
      colors x ξ = colors y η ∧ ChildMatches p x y (colors x ξ) := by
  have he (i : ι) : sandwich ξ η p (x i) = y i ↔
      colors x ξ i = colors y η i ∧ p (colors x ξ i) (x i).2 = (y i).2 := by
    change pairLayer η (lift p (pairLayer ξ (x i))) = y i ↔ _
    rw [←Equiv.eq_symm_apply]
    change (colors x ξ i,p (colors x ξ i) (x i).2) = (colors y η i,(y i).2) ↔ _
    exact ⟨Prod.mk.inj,fun h => Prod.ext h.1 h.2⟩
  simp only [he,forall_and,←funext_iff,ChildMatches]

lemma sandwich_probability [DecidableEq ι] (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) :
    finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then (1:ℝ) else 0) =
    ∑ c : ι → Bool,
      (if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0) *
      (if Compatible y c then 1/(2:ℝ)^(occupied y).card else 0) *
      (if ChildMatches p x y c then 1 else 0) := by
  classical
  have he (coins : (α → Bool) × (α → Bool)) :
      (if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then (1:ℝ) else 0) =
      ∑ c : ι → Bool, (if colors x coins.1 = c then (1:ℝ) else 0) *
        (if colors y coins.2 = c then 1 else 0) * (if ChildMatches p x y c then 1 else 0) := by
    rw [Finset.sum_eq_single (colors x coins.1)]
    · by_cases hc : colors x coins.1 = colors y coins.2
      · simp only [sandwich_matches_iff,hc,true_and,↓reduceIte,one_mul]
      · simp only [sandwich_matches_iff,hc,false_and,↓reduceIte,one_mul,Ne.symm hc,zero_mul]
    · intro c _ hc
      simp only [Ne.symm hc,ite_false,zero_mul]
    · simp
  simp_rw [he]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [finiteMean_mul_const]
  rw [finiteMean_prod_mul
    (fun ξ : α → Bool => if colors x ξ = c then (1:ℝ) else 0)
    (fun η : α → Bool => if colors y η = c then (1:ℝ) else 0),
    colors_probability,colors_probability]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma childMatches_split (p₀ p₁ : Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) :
    ChildMatches (fun b => if b then p₁ else p₀) x y c ↔
      (∀ i : {i // c i = false}, p₀ (x i.val).2 = (y i.val).2) ∧
      (∀ i : {i // c i = true}, p₁ (x i.val).2 = (y i.val).2) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [i.property,Bool.false_eq_true,↓reduceIte] using h i.val
    · intro i
      simpa only [i.property,↓reduceIte] using h i.val
  · rintro ⟨h₀,h₁⟩ i
    cases hi : c i
    · simpa only [hi,Bool.false_eq_true,↓reduceIte] using h₀ ⟨i,hi⟩
    · simpa only [hi,↓reduceIte] using h₁ ⟨i,hi⟩

omit [Fintype α] in
lemma childMatches_mean {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (P : Ω → Equiv.Perm α) (Q : Ω' → Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) :
    finiteMean (fun ω : Ω × Ω' =>
      if ChildMatches (fun b => if b then Q ω.2 else P ω.1) x y c then (1:ℝ) else 0) =
      tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2) *
      tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2) := by
  classical
  let f : Ω → ℝ := fun ω => if ∀ i : {i // c i = false}, P ω (x i.val).2 = (y i.val).2 then 1 else 0
  let g : Ω' → ℝ := fun ω => if ∀ i : {i // c i = true}, Q ω (x i.val).2 = (y i.val).2 then 1 else 0
  have he (ω : Ω × Ω') :
      (if ChildMatches (fun b => if b then Q ω.2 else P ω.1) x y c then (1:ℝ) else 0) = f ω.1*g ω.2 := by
    simp only [childMatches_split,f,g]
    split_ifs <;> simp_all
  simp_rw [he]
  exact finiteMean_prod_mul f g

lemma sandwich_mean [DecidableEq ι] {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (P : Ω → Equiv.Perm α) (Q : Ω' → Equiv.Perm α) (x y : ι → Bool × α) :
    finiteMean (fun ω : Ω × Ω' => finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 (fun b => if b then Q ω.2 else P ω.1) (x i) = y i
      then (1:ℝ) else 0)) =
    ∑ c : ι → Bool,
      (if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0) *
      (if Compatible y c then 1/(2:ℝ)^(occupied y).card else 0) *
      (tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2) *
      tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2)) := by
  classical
  simp_rw [sandwich_probability]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_comm ((if Compatible x c then _ else _) * _),finiteMean_mul_const,
    childMatches_mean]


abbrev BothAssignments (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :=
  {c : ι → Bool // Compatible e c ∧ Compatible (fun i => lift p (e i)) c}

noncomputable instance (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Fintype (BothAssignments e p) := Fintype.ofFinite _

noncomputable def labelSet (e : ι ↪ Bool × α) : Finset (Bool × α) := Finset.univ.image e

def alternatingProjection (p : Bool → Equiv.Perm α) : Equiv.Perm α := (p false).symm * p true

noncomputable def assignmentColoring (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α)
    (c : BothAssignments e p) : CycleColoring.OppositeColoring
      (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e) := by
  classical
  refine ⟨Function.extend e c.val (fun _ => false),?_,?_⟩
  · intro z hz
    apply Function.extend_apply'
    rintro ⟨i,rfl⟩
    exact hz (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · intro z hz hnext
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hnext
    have hfi := e.injective.extend_apply c.val (fun _ => false) i
    have hfj := e.injective.extend_apply c.val (fun _ => false) j
    rw [hi] at hfi
    rw [hj] at hfj
    rw [hfi,hfj]
    rcases z with ⟨b,a⟩
    cases b
    · have hj' : e j = (true,a) := hj
      have ht : (e i).2 = (e j).2 := by rw [hi,hj']
      have hh := c.property.1 i j ht
      simp only [required,hi,hj'] at hh
      revert hh
      generalize c.val i = bi
      generalize c.val j = bj
      cases bi <;> cases bj <;> decide
    · have hj' : e j = (false,alternatingProjection p a) := hj
      have ht : (lift p (e i)).2 = (lift p (e j)).2 := by
        simp only [hi,hj',lift,Equiv.coe_fn_mk,alternatingProjection,Equiv.Perm.coe_mul,
          Function.comp_apply,Equiv.apply_symm_apply]
      have hh := c.property.2 i j ht
      simp only [required,hi,hj',lift,Equiv.coe_fn_mk] at hh
      revert hh
      generalize c.val i = bi
      generalize c.val j = bj
      cases bi <;> cases bj <;> decide

omit [Fintype α] in
lemma assignmentColoring_injective (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Function.Injective (assignmentColoring e p) := by
  intro c c' he
  apply Subtype.ext
  funext i
  have hh := congrFun (congrArg Subtype.val he) (e i)
  change Function.extend e c.val (fun _ => false) (e i) =
    Function.extend e c'.val (fun _ => false) (e i) at hh
  simpa only [e.injective.extend_apply] using hh

lemma bothAssignments_card (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Fintype.card (BothAssignments e p) ≤
      2 ^ ((boolFiber (labelSet e) false ∪ boolFiber (labelSet e) true).card +
        (boolFiber (labelSet e) false ∪ (boolFiber (labelSet e) true).image
          (alternatingProjection p)).card -
        ((boolFiber (labelSet e) false).card+(boolFiber (labelSet e) true).card) +
        Fintype.card (RoutingNetwork.SelectedCycle (alternatingProjection p) (boolFiber (labelSet e) false))) := by
  have h := compatible_assignment_bound (alternatingProjection p)
    (boolFiber (labelSet e) false) (boolFiber (labelSet e) true)
  rw [childJoin_boolFiber] at h
  exact (Fintype.card_le_of_injective _ (assignmentColoring_injective e p)).trans h

omit [Fintype α] in
lemma occupied_labelSet (e : ι ↪ Bool × α) : occupied e = (labelSet e).image Prod.snd := by
  classical
  simp only [occupied,labelSet,Finset.image_image,Function.comp_def]

omit [Fintype ι] [Fintype α] in
lemma image_snd_childJoin (A B : Finset α) : (childJoin A B).image Prod.snd = A ∪ B := by
  classical
  simp only [childJoin,Finset.image_union,Finset.image_image,Function.comp_def,Finset.image_id']

omit [Fintype ι] [Fintype α] in
lemma image_lift_childJoin (p : Bool → Equiv.Perm α) (A B : Finset α) :
    (childJoin A B).image (fun x => (lift p x).2) = A.image (p false) ∪ B.image (p true) := by
  classical
  simp only [childJoin,Finset.image_union,Finset.image_image,Function.comp_def,lift,Equiv.coe_fn_mk]

omit [Fintype α] in
lemma occupied_lift_card (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    (occupied (fun i => lift p (e i))).card =
      (boolFiber (labelSet e) false ∪ (boolFiber (labelSet e) true).image (alternatingProjection p)).card := by
  classical
  have he : occupied (fun i => lift p (e i)) = (labelSet e).image (fun x => (lift p x).2) := by
    simp only [occupied,labelSet,Finset.image_image,Function.comp_def]
  rw [he,←childJoin_boolFiber (labelSet e),image_lift_childJoin]
  simp only [CycleColoring.boolFiber_childJoin,Bool.false_eq_true,↓reduceIte]
  let A := boolFiber (labelSet e) false
  let B := boolFiber (labelSet e) true
  change (A.image (p false) ∪ B.image (p true)).card = (A ∪ B.image (alternatingProjection p)).card
  have hh : A.image (p false) ∪ B.image (p true) =
      (A ∪ B.image (alternatingProjection p)).image (p false) := by
    simp only [Finset.image_union,Finset.image_image,Function.comp_def,
      alternatingProjection,Equiv.Perm.coe_mul,Equiv.apply_symm_apply]
  rw [hh,Finset.card_image_of_injective _ (p false).injective]

lemma bothAssignments_occupied_bound (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Fintype.card (BothAssignments e p) ≤
      2 ^ ((occupied e).card + (occupied (fun i => lift p (e i))).card - Fintype.card ι +
        Fintype.card (RoutingNetwork.SelectedCycle (alternatingProjection p) (boolFiber (labelSet e) false))) := by
  have he : (occupied e).card =
      (boolFiber (labelSet e) false ∪ boolFiber (labelSet e) true).card := by
    rw [occupied_labelSet,←childJoin_boolFiber (labelSet e),image_snd_childJoin]
    simp only [CycleColoring.boolFiber_childJoin,Bool.false_eq_true,↓reduceIte]
  have hc : (boolFiber (labelSet e) false).card+(boolFiber (labelSet e) true).card = Fintype.card ι := by
    rw [←card_childJoin,childJoin_boolFiber,labelSet,Finset.card_image_of_injective _ e.injective,
      Finset.card_univ]
  simpa only [he,occupied_lift_card,←hc] using bothAssignments_card e p

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma compatible_pairLayer_iff (x : ι → Bool × α) (c : ι → Bool) (ξ : α → Bool) :
    Compatible (fun i => pairLayer ξ (x i)) c ↔ Compatible x c := by
  have he (i j : ι) (ht : (x i).2 = (x j).2) :
      required (fun i => pairLayer ξ (x i)) c i = required (fun i => pairLayer ξ (x i)) c j ↔
      required x c i = required x c j := by
    simp only [required,pairLayer,Equiv.coe_fn_mk,ht]
    cases (x i).1 <;> cases (x j).1 <;> cases c i <;> cases c j <;> cases ξ (x j).2 <;> decide
  constructor
  · intro h i j ht
    exact (he i j ht).mp (h i j ht)
  · intro h i j ht
    exact (he i j ht).mpr (h i j ht)


noncomputable def alternatingCycles (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) : ℕ :=
  Fintype.card (RoutingNetwork.SelectedCycle
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e))

omit [Fintype α] in
lemma occupied_eq_fibers (e : ι ↪ Bool × α) :
    occupied e = boolFiber (labelSet e) false ∪ boolFiber (labelSet e) true := by
  rw [occupied_labelSet,←childJoin_boolFiber (labelSet e),image_snd_childJoin]
  simp only [CycleColoring.boolFiber_childJoin,Bool.false_eq_true,↓reduceIte]

omit [Fintype α] in
lemma card_labelSet (e : ι ↪ Bool × α) : (labelSet e).card = Fintype.card ι := by
  classical
  exact (Finset.card_image_of_injective _ e.injective).trans (Finset.card_univ)

omit [Fintype α] in
lemma occupied_card_double (e : ι ↪ Bool × α) : Fintype.card ι ≤ 2*(occupied e).card := by
  have h₀ : (boolFiber (labelSet e) false).card ≤ (occupied e).card := by
    rw [occupied_eq_fibers]
    exact Finset.card_le_card Finset.subset_union_left
  have h₁ : (boolFiber (labelSet e) true).card ≤ (occupied e).card := by
    rw [occupied_eq_fibers]
    exact Finset.card_le_card Finset.subset_union_right
  have he : (boolFiber (labelSet e) false).card+(boolFiber (labelSet e) true).card = Fintype.card ι := by
    rw [←card_childJoin,childJoin_boolFiber,card_labelSet]
  omega

lemma bothAssignments_exact_bound (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Fintype.card (BothAssignments e p) ≤
      2 ^ ((occupied e).card + (occupied (fun i => lift p (e i))).card - Fintype.card ι +
        alternatingCycles e p) := by
  have h := CycleColoring.card_opposite_le
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e)
    Prod.fst (CycleColoring.alternatingPerm_flip (alternatingProjection p))
  have hb : (CycleColoring.boundary (CycleColoring.alternatingPerm (alternatingProjection p))
      (labelSet e)).card =
      (occupied e).card + (occupied (fun i => lift p (e i))).card - Fintype.card ι := by
    have hh := alternating_boundary_card (alternatingProjection p)
      (boolFiber (labelSet e) false) (boolFiber (labelSet e) true)
    rw [childJoin_boolFiber] at hh
    rw [occupied_eq_fibers,occupied_lift_card]
    have he := card_childJoin (boolFiber (labelSet e) false) (boolFiber (labelSet e) true)
    rw [childJoin_boolFiber,card_labelSet] at he
    simpa only [he] using hh
  rw [hb] at h
  exact (Fintype.card_le_of_injective _ (assignmentColoring_injective e p)).trans h

abbrev Assignments (x y : ι → Bool × α) :=
  {c : ι → Bool // Compatible x c ∧ Compatible y c}

noncomputable instance (x y : ι → Bool × α) : Fintype (Assignments x y) := Fintype.ofFinite _

def switchedEmbedding (e : ι ↪ Bool × α) (ξ : α → Bool) : ι ↪ Bool × α :=
  e.trans (pairLayer ξ).toEmbedding

def routedEmbedding (e : ι ↪ Bool × α) (ξ η : α → Bool) (p : Bool → Equiv.Perm α) :
    ι ↪ Bool × α := e.trans (sandwich ξ η p).toEmbedding

omit [Fintype α] in
lemma occupied_pairLayer (x : ι → Bool × α) (ξ : α → Bool) :
    occupied (fun i => pairLayer ξ (x i)) = occupied x := rfl

noncomputable def assignmentsEquiv (e : ι ↪ Bool × α) (ξ η : α → Bool)
    (p : Bool → Equiv.Perm α) :
    Assignments e (routedEmbedding e ξ η p) ≃ BothAssignments (switchedEmbedding e ξ) p := by
  apply Equiv.subtypeEquivRight
  intro c
  change Compatible e c ∧ Compatible (fun i => pairLayer η (lift p (pairLayer ξ (e i)))) c ↔ _
  rw [compatible_pairLayer_iff]
  exact and_congr (compatible_pairLayer_iff e c ξ).symm Iff.rfl

lemma assignments_actual_bound (e : ι ↪ Bool × α) (ξ η : α → Bool) (p : Bool → Equiv.Perm α) :
    Fintype.card (Assignments e (routedEmbedding e ξ η p)) ≤
      2 ^ ((occupied e).card + (occupied (routedEmbedding e ξ η p)).card - Fintype.card ι +
        alternatingCycles (switchedEmbedding e ξ) p) := by
  rw [Fintype.card_congr (assignmentsEquiv e ξ η p)]
  exact bothAssignments_exact_bound (switchedEmbedding e ξ) p

omit [Fintype α] in
lemma assignments_actual_exponent_nonneg (e : ι ↪ Bool × α) (ξ η : α → Bool)
    (p : Bool → Equiv.Perm α) :
    Fintype.card ι ≤ (occupied e).card + (occupied (routedEmbedding e ξ η p)).card := by
  have h₀ := occupied_card_double e
  have h₁ := occupied_card_double (routedEmbedding e ξ η p)
  omega

end
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

noncomputable def compatibleSet (x y : ι → Bool × α) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter (fun c => Compatible x c ∧ Compatible y c)

omit [Fintype α] [DecidableEq α] in
lemma mem_compatibleSet (x y : ι → Bool × α) (c : ι → Bool) :
    c ∈ compatibleSet x y ↔ Compatible x c ∧ Compatible y c := by
  classical
  simp only [compatibleSet,Finset.mem_filter,Finset.mem_univ,true_and]

omit [Fintype α] [DecidableEq α] in
lemma card_compatibleSet (x y : ι → Bool × α) :
    (compatibleSet x y).card = Fintype.card (Assignments x y) := by
  classical
  exact (Fintype.card_subtype _).symm

noncomputable def outerWeight (x y : ι → Bool × α) : ℝ :=
  1/(2:ℝ)^((occupied x).card+(occupied y).card)

omit [Fintype α] [DecidableEq ι] in
lemma outerWeight_pos (x y : ι → Bool × α) : 0 < outerWeight x y := by
  unfold outerWeight
  positivity

omit [Fintype α] in
lemma sum_colors_factor (x y : ι → Bool × α) (f : (ι → Bool) → ℝ) :
    (∑ c : ι → Bool,
      (if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0) *
      (if Compatible y c then 1/(2:ℝ)^(occupied y).card else 0) * f c) =
      outerWeight x y * ∑ c ∈ compatibleSet x y, f c := by
  classical
  rw [compatibleSet,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hx : Compatible x c <;> by_cases hy : Compatible y c
  · simp only [hx,hy,true_and,↓reduceIte,outerWeight,pow_add,one_div_mul_one_div]
  · simp only [hx,hy,and_false,↓reduceIte,mul_zero,zero_mul]
  · simp only [hx,hy,false_and,↓reduceIte,mul_zero,zero_mul]
  · simp only [hx,hy,false_and,↓reduceIte,mul_zero,zero_mul]

lemma sandwich_weighted_probability (p : Bool → Equiv.Perm α) (x y : ι → Bool × α)
    (W : (ι → Bool) → ℝ) :
    finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then W (colors x coins.1) else 0) =
    outerWeight x y * ∑ c ∈ compatibleSet x y, if ChildMatches p x y c then W c else 0 := by
  classical
  have he (coins : (α → Bool) × (α → Bool)) :
      (if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then W (colors x coins.1) else 0) =
      ∑ c : ι → Bool, (if colors x coins.1 = c then (1:ℝ) else 0) *
        (if colors y coins.2 = c then 1 else 0) * (if ChildMatches p x y c then W c else 0) := by
    rw [Finset.sum_eq_single (colors x coins.1)]
    · by_cases hc : colors x coins.1 = colors y coins.2
      · simp only [sandwich_matches_iff,hc,true_and,↓reduceIte,one_mul]
      · simp only [sandwich_matches_iff,hc,false_and,↓reduceIte,one_mul,Ne.symm hc,zero_mul]
    · intro c _ hc
      simp only [Ne.symm hc,ite_false,zero_mul]
    · simp
  simp_rw [he]
  rw [finiteMean_sum,←sum_colors_factor]
  apply Finset.sum_congr rfl
  intro c _
  rw [finiteMean_mul_const,finiteMean_prod_mul
    (fun ξ : α → Bool => if colors x ξ = c then (1:ℝ) else 0)
    (fun η : α → Bool => if colors y η = c then (1:ℝ) else 0),
    colors_probability,colors_probability]

omit [Fintype α] [DecidableEq ι] in
lemma tupleProbability_nonneg {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : 0 ≤ tupleProbability P x y := by
  classical
  exact finiteMean_nonneg (fun ω => by split_ifs <;> norm_num)

lemma sandwich_power_bound {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (P : Ω → Equiv.Perm α) (Q : Ω' → Equiv.Perm α) (x y : ι → Bool × α)
    (a : ℝ) (ha : 0 ≤ a) :
    (finiteMean (fun ω : Ω × Ω' => finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 (fun b => if b then Q ω.2 else P ω.1) (x i) = y i
      then (1:ℝ) else 0)))^(1+a) ≤
    (outerWeight x y)^(1+a) * ((compatibleSet x y).card:ℝ)^a *
      ∑ c ∈ compatibleSet x y,
      (tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2))^(1+a) *
      (tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2))^(1+a) := by
  classical
  rw [sandwich_mean,sum_colors_factor]
  let f (c : ι → Bool) : ℝ :=
      tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2) *
      tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2)
  have hf (c : ι → Bool) : 0 ≤ f c := mul_nonneg (tupleProbability_nonneg _ _ _)
    (tupleProbability_nonneg _ _ _)
  rw [Real.mul_rpow (le_of_lt (outerWeight_pos _ _)) (Finset.sum_nonneg (fun c _ => hf c))]
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (compatibleSet x y)
    (show 1 ≤ 1+a by linarith) (fun c _ => hf c)
  have he : 1+a-1=a := by ring
  rw [he] at hh
  calc
    _ ≤ (outerWeight x y)^(1+a) *
        (((compatibleSet x y).card:ℝ)^a * ∑ c ∈ compatibleSet x y, (f c)^(1+a)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (le_of_lt (outerWeight_pos _ _)) _)
    _ = _ := by
      rw [←mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      exact Real.mul_rpow (tupleProbability_nonneg _ _ _) (tupleProbability_nonneg _ _ _)

end PairRouting

end Thorp

end ThorpNine.Tail

end OAI
