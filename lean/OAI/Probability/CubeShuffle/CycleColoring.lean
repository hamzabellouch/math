import OAI.Probability.CubeShuffle.ParallelLayers

namespace OAI

namespace CubeShuffle

open scoped BigOperators
open Filter

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A coloring of the selected vertices constant along every retained edge of
an oriented permutation graph. Off the selected set its value is fixed. -/
abbrev Coloring (p : Equiv.Perm α) (S : Finset α) :=
  {f : α → Bool // (∀ x, x ∉ S → f x = false) ∧
    ∀ x ∈ S, p x ∈ S → f (p x) = f x}

noncomputable instance (p : Equiv.Perm α) (S : Finset α) : Fintype (Coloring p S) :=
  Fintype.ofFinite _

noncomputable def boundary (p : Equiv.Perm α) (S : Finset α) : Finset α :=
  S.filter (fun x => p.symm x ∉ S)

noncomputable def root {p : Equiv.Perm α} {S : Finset α}
    (C : RoutingNetwork.SelectedCycle p S) : α := C.nonempty.choose

lemma root_mem {p : Equiv.Perm α} {S : Finset α} (C : RoutingNetwork.SelectedCycle p S) :
    root C ∈ C.val := C.nonempty.choose_spec

abbrev Seed (p : Equiv.Perm α) (S : Finset α) :=
  {x // x ∈ boundary p S} ⊕ RoutingNetwork.SelectedCycle p S

noncomputable def record {p : Equiv.Perm α} {S : Finset α}
    (f : Coloring p S) : Seed p S → Bool :=
  Sum.elim (fun x => f.val x.val) (fun C => f.val (root C))

lemma orbit_subset_of_predecessor_closed (p : Equiv.Perm α) (D : Finset α)
    (hD : ∀ x ∈ D, p.symm x ∈ D) {x : α} (hx : x ∈ D) : orbitSet p x ⊆ D := by
  intro y hy
  have hh := ((mem_orbitSet p x y).mp hy).inv
  obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
  have hp (k : ℕ) : (p⁻¹ ^ k) x ∈ D := by
    induction k with
    | zero => simpa using hx
    | succ k ih => simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.coe_inv] using hD _ ih
  exact hn ▸ hp n

lemma record_injective (p : Equiv.Perm α) (S : Finset α) :
    Function.Injective (record (p := p) (S := S)) := by
  classical
  intro f g hfg
  apply Subtype.ext
  funext x
  by_contra hne
  have hx : x ∈ S := by
    by_contra h
    exact hne ((f.property.1 x h).trans (g.property.1 x h).symm)
  let D := S.filter (fun y => f.val y ≠ g.val y)
  have hxD : x ∈ D := Finset.mem_filter.mpr ⟨hx,hne⟩
  have hprev (y : α) (hy : y ∈ D) : p.symm y ∈ D := by
    obtain ⟨hyS,hyne⟩ := Finset.mem_filter.mp hy
    have hpS : p.symm y ∈ S := by
      by_contra hn
      have hseed : y ∈ boundary p S := Finset.mem_filter.mpr ⟨hyS,hn⟩
      exact hyne (congrFun hfg (Sum.inl ⟨y,hseed⟩))
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    have hf := f.property.2 (p.symm y) hpS (by simpa only [Equiv.apply_symm_apply] using hyS)
    have hg := g.property.2 (p.symm y) hpS (by simpa only [Equiv.apply_symm_apply] using hyS)
    simp only [Equiv.apply_symm_apply] at hf hg
    intro he
    exact hyne (hf.trans (he.trans hg.symm))
  have horb := orbit_subset_of_predecessor_closed p D hprev hxD
  let C : RoutingNetwork.SelectedCycle p S :=
    ⟨orbitSet p x,⟨x,rfl⟩,fun y hy => (Finset.mem_filter.mp (horb hy)).1⟩
  have hrD : root C ∈ D := horb (root_mem C)
  have hrne := (Finset.mem_filter.mp hrD).2
  exact hrne (congrFun hfg (Sum.inr C))

/-- Every open chain has a boundary seed and every complete cycle has one free
bit. In particular a parallel pair of matching edges is treated as a cycle. -/
lemma card_coloring_le (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (Coloring p S) ≤
      2 ^ ((boundary p S).card + Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  have h := Fintype.card_le_of_injective (record (p := p) (S := S)) (record_injective p S)
  simpa only [Fintype.card_fun,Fintype.card_sum,Fintype.card_coe,Fintype.card_bool] using h

omit [Fintype α] in
lemma boundary_card (p : Equiv.Perm α) (S : Finset α) :
    (boundary p S).card = S.card - (S.filter (fun x => p.symm x ∈ S)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := S) (fun x => p.symm x ∈ S)
  unfold boundary
  omega

lemma card_coloring_le_edges (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (Coloring p S) ≤
      2 ^ (S.card - (S.filter (fun x => p.symm x ∈ S)).card +
        Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  simpa only [boundary_card] using card_coloring_le p S

end CycleColoring

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A binary assignment with opposite values on each marked matching edge. -/
abbrev OppositeColoring (p : Equiv.Perm α) (S : Finset α) :=
  {f : α → Bool // (∀ x, x ∉ S → f x = false) ∧
    ∀ x ∈ S, p x ∈ S → f (p x) = !(f x)}

noncomputable instance (p : Equiv.Perm α) (S : Finset α) : Fintype (OppositeColoring p S) :=
  Fintype.ofFinite _

/-- Flipping one bipartition converts opposite matching assignments into
constant colorings. The construction includes the unmarked-value convention. -/
noncomputable def bipartitionFlip (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x))
    (f : OppositeColoring p S) : Coloring p S := by
  classical
  refine ⟨(fun x => if x ∈ S then Bool.xor (f.val x) (χ x) else false),?_,?_⟩
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hpx
    simp only [ite_eq_left hx,ite_eq_left hpx,f.property.2 x hx hpx,hχ x]
    cases f.val x <;> cases χ x <;> rfl

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

/-- Alternating traversal of the identity matching and the p-matching on two
halves. A fixed point of p is precisely a parallel-edge alternating cycle. -/
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

/-- Literal component-count exponent in FAC.1, after identifying the two
perfect matchings with the identity and p matchings on their two halves.
The complete alternating cycles are bounded by the projection-side cycles. -/
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

/-- A weighted form of the inverse-image cylinder bound. Its orientation is
specified by the actual butterfly action on each selected input. -/
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

/-- The central-mark inclusion estimate in the orientation required by the
recursive Beneš network, derived rather than assumed from reversibility. -/
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

end CubeShuffle

end OAI
