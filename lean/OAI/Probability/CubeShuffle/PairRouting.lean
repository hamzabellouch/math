import OAI.Probability.CubeShuffle.CycleColoring

namespace OAI

namespace CubeShuffle

open scoped BigOperators
open Filter

namespace PairRouting
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

/-- Exact fair-coin probability at an outer pair layer, including impossible
assignments. No cardinality or independence of marked paths is assumed. -/
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

end PairRouting

namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

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

/-- Exact expansion by the binary child assignments at one actual outer pair
layer on each side. The factors 2^-b count occupied switches, not paths. -/
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

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

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

/-- The exact recursive transition identity before taking any moment bound. -/
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

end PairRouting

namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

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

end PairRouting


namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

/-- Full alternating cycles, not their projection-side overcount. This is the
cycle count needed for sparse low-level blocks. -/
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

end PairRouting

namespace PairRouting
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

/-- Arbitrary weights can be kept as functions of the actual child assignment;
no change from the physical switch measure to uniformly sampled assignments. -/
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

/-- One precise Hölder step in the source recursive density expansion. -/
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

/-- Two genuine independent butterfly coin fields; the first routes outward
on the output side, the second outward on the input side. -/
abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

/-- Exact rearrangement, not a resampling assumption. -/
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

/-- The complete actual recursive Beneš construction in product coordinates. -/
lemma palindromePerm_coordinates (d : ℕ) (c : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) (x : Card (d+1)) :
    headTailEquiv d (palindromePerm (d+1) ((benesStepEquiv d).symm (c,coins)) x) =
      PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then c.2 else c.1))
        (headTailEquiv d x) := by
  rw [palindromePerm_step]
  simp only [Equiv.Perm.mul_apply,headTail_switch,headTail_child]
  rfl

/-- Full alternating-cycle count along the ACTUAL sampled routing, recursively.
At each child the labels are exactly those sent into it by the actual input coins. -/
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
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

lemma alternatingCycles_double (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    2 * alternatingCycles e p ≤ Fintype.card ι := by
  have hh := CycleColoring.alternating_cycle_count_double (alternatingProjection p) (labelSet e)
  simpa only [alternatingCycles, card_labelSet] using hh

lemma alternatingCycles_zero (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α)
    (hι : Fintype.card ι ≤ 1) : alternatingCycles e p = 0 := by
  have hh := alternatingCycles_double e p
  omega

end PairRouting

namespace PairRouting
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

/-- The exact cancellation giving the source factor 2^(-h+z), before taking
its a-th power. Natural subtraction is justified by occupied-pair cardinalities. -/
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

end PairRouting

namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

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

end CubeShuffle

end OAI
