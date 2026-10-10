import OAI.Combinatorics.EditApproximation.Specification.ConcreteFootprints
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation

universe u_1 u_2

private theorem footprint_cases {ι β : Type*} {program : BitQuery ι β}
    {p : Prop} (d : Decidable p) (no : ¬p → BitQuery.Heap program)
    (yes : p → BitQuery.Heap program) :
    (Decidable.casesOn (motive := fun _ => BitQuery.Heap program) d no yes).footprint =
      Decidable.casesOn (motive := fun _ => BitQuery.Footprint program) d
        (fun h => (no h).footprint) (fun h => (yes h).footprint) := by
  cases d <;> rfl

private theorem cases_congr {p : Prop} (d : Decidable p) {α : Sort*}
    {no otherNo : ¬p → α} {yes otherYes : p → α}
    (hn : ∀ h, no h = otherNo h) (hy : ∀ h, yes h = otherYes h) :
    Decidable.casesOn (motive := fun _ => α) d no yes =
      Decidable.casesOn (motive := fun _ => α) d otherNo otherYes := by
  cases d with
  | isFalse h => exact hn h
  | isTrue h => exact hy h

private theorem footprint_congr_seven {α₁ : Sort*} {α₂ : Sort*} {α₃ : Sort*} {α₄ : Sort*}
    {α₅ : Sort*} {α₆ : Sort*} {α₇ : Sort*} {β : Sort*}
    {f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → β}
    {a₁ b₁ : α₁} {a₂ b₂ : α₂} {a₃ b₃ : α₃} {a₄ b₄ : α₄}
    {a₅ b₅ : α₅} {a₆ b₆ : α₆} {a₇ b₇ : α₇}
    (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃) (h₄ : a₄ = b₄)
    (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
    f a₁ a₂ a₃ a₄ a₅ a₆ a₇ = f b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  cases h₁; cases h₂; cases h₃; cases h₄; cases h₅; cases h₆; cases h₇
  rfl

private theorem footprint_mpr_congr {ι β : Type*} {p q : BitQuery ι β}
    (eqn : p = q) (a : BitQuery.Heap q) (b : BitQuery.Footprint q)
    (hab : a.footprint = b) :
    ((congrArg BitQuery.Heap eqn).mpr a).footprint =
      (congrArg BitQuery.Footprint eqn).mpr b := by
  cases eqn
  exact hab

private def groupHeapTransportBridge (M J N n exponent F Q R B b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, BitQuery.Heap (actual s j)) :
    ∀ s j, BitQuery.Heap
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
  cases h
  exact heap

private def groupFootprintTransportBridge (M J N n exponent F Q R B b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, BitQuery.Footprint (actual s j)) :
    ∀ s j, BitQuery.Footprint
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
  cases h
  exact heap

private theorem footprint_groupTransport (M J N n exponent F Q R B b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, BitQuery.Heap (actual s j))
    (footprint : ∀ s j, BitQuery.Footprint (actual s j))
    (hfp : ∀ s j, (heap s j).footprint = footprint s j) :
    ∀ s j, (groupHeapTransportBridge M J N n exponent F Q R B b c h actual heap s j).footprint =
      groupFootprintTransportBridge M J N n exponent F Q R B b c h actual footprint s j := by
  cases h
  intro s j
  exact hfp s j

-- Supply case arguments directly so inference does not normalize indexed branch values.
universe u

private theorem heq_decidable_cases_from {p : Prop} (left right : Decidable p → Sort u)
    {α β : Sort u} (outerLeft : α) (outerRight : β)
    (leftNo : ∀ h : ¬p, left (.isFalse h)) (leftYes : ∀ h : p, left (.isTrue h))
    (rightNo : ∀ h : ¬p, right (.isFalse h)) (rightYes : ∀ h : p, right (.isTrue h))
    (decision : Decidable p)
    (hleft : HEq outerLeft (Decidable.casesOn (motive := left) decision leftNo leftYes))
    (hright : HEq (Decidable.casesOn (motive := right) decision rightNo rightYes) outerRight)
    (hn : ∀ h, HEq (leftNo h) (rightNo h)) (hy : ∀ h, HEq (leftYes h) (rightYes h)) :
    HEq outerLeft outerRight := by
  refine hleft.trans ?_
  refine HEq.trans ?_ hright
  cases decision with
  | isFalse h => exact hn h
  | isTrue h => exact hy h

open Lean Meta Elab Tactic in
local elab "direct_decidable_heq" : tactic => withMainContext do
  let initialTarget ← instantiateMVars (← (← getMainGoal).getType)
  if initialTarget.isAppOfArity ``Eq 3 then
    evalTactic (← `(tactic| apply eq_of_heq))
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``HEq 4 do
      throwError "expected heterogeneous equality"
    let sides := target.getAppArgs
    let recArgs (value : Expr) : MetaM (Array Expr) := do
      let value := value.consumeMData
      let value := if value.getAppFn.isConstOf ``id && value.getAppArgs.size == 2 then
        value.getAppArgs[1]!.consumeMData else value
      let args := value.getAppArgs
      unless args.size == 5 do
        throwError "unexpected Decidable recursor arity {args.size} at {value.getAppFn}"
      if value.getAppFn.isConstOf ``Decidable.rec then
        pure args
      else if value.getAppFn.isConstOf ``Decidable.casesOn then
        pure #[args[0]!, args[1]!, args[3]!, args[4]!, args[2]!]
      else
        throwError "expected a Decidable recursor, got {value.getAppFn}"
    let left ← recArgs sides[1]!
    let right ← recArgs sides[3]!
    unless left[0]! == right[0]! && left[4]! == right[4]! do
      throwError "the case expressions use different propositions or decisions"
    let proof ← withTransparency .default <| mkAppM ``heq_decidable_cases_from
      #[left[1]!, right[1]!, sides[1]!, sides[3]!, left[2]!, left[3]!, right[2]!, right[3]!, left[4]!]
    let goals ← withTransparency .default <| goal.apply proof
    replaceMainGoal goals

private theorem heq_mpr_both {α β γ δ : Sort u} (leftEq : α = β) (rightEq : γ = δ)
    (left : β) (right : δ) (h : HEq left right) : HEq (leftEq.mpr left) (rightEq.mpr right) := by
  cases leftEq
  cases rightEq
  exact h

open Lean Meta Elab Tactic in
local elab "direct_mpr_heq" : tactic => withMainContext do
  let initialTarget ← instantiateMVars (← (← getMainGoal).getType)
  if initialTarget.isAppOfArity ``Eq 3 then
    evalTactic (← `(tactic| apply eq_of_heq))
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``HEq 4 do
      throwError "expected heterogeneous equality"
    let sides := target.getAppArgs
    let castArgs (value : Expr) : MetaM (Array Expr) := do
      let value := value.consumeMData
      unless value.getAppFn.isConstOf ``Eq.mpr && value.getAppArgs.size == 4 do
        throwError "expected Eq.mpr, got {value.getAppFn}"
      pure value.getAppArgs
    let left ← castArgs sides[1]!
    let right ← castArgs sides[3]!
    let proof ← withTransparency .default <| mkAppM ``heq_mpr_both
      #[left[2]!, right[2]!, left[3]!, right[3]!]
    let goals ← withTransparency .default <| goal.apply proof
    replaceMainGoal goals

@[simp] theorem queryInitialGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {n : Nat} (N P F exponent : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (a : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n)
  (reader :
    OAI.EditApproximation.TargetInterval n →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (key : OAI.EditApproximation.TargetInterval n) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key))
  (next :
    List.{0} (OAI.EditApproximation.TargetInterval n) →
      List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (OAI.EditApproximation.TargetInterval n)) →
      (words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryInitialGather.{u_1, u_2} ι β n N P F exponent hP a q reader next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryInitialGather.{u_1, u_2} ι β n N P F exponent hP a q reader next)
      (@OAI.EditApproximation.queryInitialGatherHeap.{u_1, u_2} ι β n N P F exponent hP a q reader hr next hn))
    (@OAI.EditApproximation.queryInitialGatherFootprint.{u_1, u_2} ι β n N P F exponent hP a q reader
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key)
          (hr key))
      next fun keys words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys words) (hn keys words)) := by
  intros
  simp [queryInitialGatherHeap, queryInitialGatherFootprint, queryInitialGather]

@[simp] theorem queryBandGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {nx ny : Nat} (M : Nat) (parent : OAI.EditApproximation.TargetInterval nx)
  (N P F exponent : Nat) (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (a : OAI.EditApproximation.BinaryFraction)
  (initial : OAI.EditApproximation.TargetInterval ny → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.TargetInterval ny → Nat)
  (ha :
    ∀ (r : OAI.EditApproximation.TargetInterval ny),
      @LE.le.{0} Nat instLENat (allocation r) (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial r)))
  (q : OAI.EditApproximation.TargetInterval ny)
  (massReader initialReader :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hm :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (massReader key))
  (hi :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (initialReader key))
  (next :
    List.{0} (Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      List.{0} OAI.EditApproximation.BinaryFraction →
        List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny))) →
      (mass words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys mass words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryBandGather.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial q massReader
        initialReader next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryBandGather.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial q massReader
        initialReader next)
      (@OAI.EditApproximation.queryBandGatherHeap.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial allocation
        ha q massReader initialReader hm hi next hn))
    (@OAI.EditApproximation.queryBandGatherFootprint.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial
      allocation q massReader initialReader
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (massReader key)
          (hm key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (initialReader key) (hi key))
      next fun keys mass words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys mass words) (hn keys mass words)) := by
  intros
  simp [queryBandGatherHeap, queryBandGatherFootprint, queryBandGather]

@[simp] theorem queryGroupSourceGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {n : Nat} (M N F Q exponent eM eF : Nat)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (a : OAI.EditApproximation.BinaryFraction)
  (initial : OAI.EditApproximation.TargetInterval n → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.TargetInterval n → Nat)
  (ha :
    ∀ (r : OAI.EditApproximation.TargetInterval n),
      @LE.le.{0} Nat instLENat (allocation r) (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial r)))
  (q : OAI.EditApproximation.TargetInterval n)
  (reader :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key))
  (next :
    List.{0} (OAI.EditApproximation.GroupScalarKey M F Q) →
      List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (OAI.EditApproximation.GroupScalarKey M F Q)) →
      (words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryGroupSourceGather.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial q reader
        next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryGroupSourceGather.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial q reader
        next)
      (@OAI.EditApproximation.queryGroupSourceGatherHeap.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial
        allocation ha q reader hr next hn))
    (@OAI.EditApproximation.queryGroupSourceGatherFootprint.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial
      allocation q reader
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key)
          (hr key))
      next fun keys words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys words) (hn keys words)) := by
  intros
  simp [queryGroupSourceGatherHeap, queryGroupSourceGatherFootprint, queryGroupSourceGather]

@[simp] theorem queryOnlineSourceGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {nx ny M : Nat} (parent : OAI.EditApproximation.TargetInterval nx)
  (N P F exponent H : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (tau a : OAI.EditApproximation.BinaryFraction)
  (initial : OAI.EditApproximation.TargetInterval ny → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (initialAllocation : OAI.EditApproximation.TargetInterval ny → Nat)
  (child : Fin M → OAI.EditApproximation.TargetInterval ny → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (childAllocation : Fin M → OAI.EditApproximation.TargetInterval ny → Nat)
  (hi :
    ∀ (r : OAI.EditApproximation.TargetInterval ny),
      @LE.le.{0} Nat instLENat (initialAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial r)))
  (hc :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval ny),
      @LE.le.{0} Nat instLENat (childAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)))
  (q : OAI.EditApproximation.TargetInterval ny)
  (reader :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny)) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key range))
  (next :
    List.{0} (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny)) →
      List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny))) →
      (words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryOnlineSourceGather.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a initial
        child q reader next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryOnlineSourceGather.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a initial
        child q reader next)
      (@OAI.EditApproximation.queryOnlineSourceGatherHeap.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a
        initial initialAllocation child childAllocation hi hc q reader hr next hn))
    (@OAI.EditApproximation.queryOnlineSourceGatherFootprint.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a
      initial initialAllocation child childAllocation q reader
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (reader key range) (hr key range))
      next fun keys words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys words) (hn keys words)) := by
  intros
  simp [queryOnlineSourceGatherHeap, queryOnlineSourceGatherFootprint, queryOnlineSourceGather]

@[simp] theorem queryLocalRefinementHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (parentInitial :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (child initial :
    Fin M →
      OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
        Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (R : Nat)
  (hc :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)) R)
  (hi :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)) R)
  (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q)
  (integer : Nat → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Prod.{0, 0} Nat Nat)
  (parentAllocation : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (drawAllocation : OAI.EditApproximation.CountedCellGroupAllocations M F Q)
  (integerAllocation : Nat → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (hp :
    ∀ (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (parentAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (parentInitial r)))
  (hca :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (childAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)))
  (hia :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (initialAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)))
  (hd :
    ∀ (b : Nat) (cell : Prod.{0, 0} Nat Nat)
      (s :
        Fin (@List.length.{0} Rat (OAI.EditApproximation.groupDyadicScales M b (@Nat.cast.{0} Rat Rat.instNatCast F))))
      (j :
        Fin
          (OAI.EditApproximation.groupSampleCount M Q b
            (OAI.EditApproximation.groupDyadicScaleAt M b (@Nat.cast.{0} Rat Rat.instNatCast F) s))),
      @LE.le.{0} Nat instLENat (drawAllocation b cell s j) (@Prod.snd.{0, 0} (Fin M) Nat (draw b cell s j)))
  (hz :
    ∀ (b : Nat) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (integerAllocation b r) (@Prod.snd.{0, 0} Nat Nat (integer b r)))
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRefinement.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRefinement.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent)
      (@OAI.EditApproximation.queryLocalRefinementHeap.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer parentAllocation childAllocation
        initialAllocation drawAllocation integerAllocation hp hca hia hd hz q readEarlier readCurrent he hr))
    (@OAI.EditApproximation.queryLocalRefinementFootprint.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer parentAllocation childAllocation
      initialAllocation drawAllocation integerAllocation q readEarlier readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalRefinementHeap, queryLocalRefinementFootprint, queryLocalRefinement, queryRefinementGather]

@[simp] theorem queryLocalRandomSourcesHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (parentInitial :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (child initial :
    Fin M →
      OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
        Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (R : Nat)
  (hc :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)) R)
  (hi :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)) R)
  (parentAllocation : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (hp :
    ∀ (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (parentAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (parentInitial r)))
  (hca :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (childAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)))
  (hia :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (initialAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)))
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInteger key range))
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRandomSources.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier
        readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRandomSources.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier
        readCurrent)
      (@OAI.EditApproximation.queryLocalRandomSourcesHeap.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q
        eM eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi parentAllocation childAllocation
        initialAllocation hp hca hia q readGroup readInteger readEarlier readCurrent hg hz he hr))
    (@OAI.EditApproximation.queryLocalRandomSourcesFootprint.{u_1, u_2} ι α source target M _inst parent N P F exponent H
      Q eM eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi parentAllocation childAllocation
      initialAllocation q readGroup readInteger readEarlier readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (readInteger key range) (hz key range))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalRandomSourcesHeap, queryLocalRandomSourcesFootprint, queryLocalRandomSources]

@[simp] theorem queryLocalBandHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (parentInitial :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (parentAllocation : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (hp :
    ∀ (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (parentAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (parentInitial r)))
  (readMass readInitial :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hm :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key))
  (hi :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key))
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInteger key range))
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalBand.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalBand.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent)
      (@OAI.EditApproximation.queryLocalBandHeap.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t parentInitial parentAllocation hp readMass readInitial readGroup readInteger q
        readEarlier readCurrent hm hi hg hz he hr))
    (@OAI.EditApproximation.queryLocalBandFootprint.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta t parentInitial parentAllocation readMass readInitial readGroup readInteger q
      readEarlier readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key)
          (hm key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key)
          (hi key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (readInteger key range) (hz key range))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalBandHeap, queryLocalBandFootprint, queryLocalBand]

@[simp] theorem queryLocalProgramHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (readParent :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readMass readInitial :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hp :
    (key : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readParent key))
  (hm :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key))
  (hi :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key))
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInteger key range))
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalProgram.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalProgram.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent)
      (@OAI.EditApproximation.queryLocalProgramHeap.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF
        hP hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent
        hp hm hi hg hz he hr))
    (@OAI.EditApproximation.queryLocalProgramFootprint.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM
      eF hP hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier
      readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readParent key)
          (hp key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key)
          (hm key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key)
          (hi key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (readInteger key range) (hz key range))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalProgramHeap, queryLocalProgramFootprint, queryLocalProgram]

@[simp] theorem queryPhysicalTableReadHeap_footprint :
    ∀ {M J n : Nat} (copies T S : Nat) (parent : OAI.EditApproximation.PhysicalTableRequest M J n)
  (child :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S r)
        (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S parent)),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S r)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S parent))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalTableRead M J n copies T S parent child))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S r)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S parent))
      OAI.EditApproximation.BinaryFraction (@OAI.EditApproximation.queryPhysicalTableRead M J n copies T S parent child)
      (@OAI.EditApproximation.queryPhysicalTableReadHeap M J n copies T S parent child))
    (@OAI.EditApproximation.queryPhysicalTableReadFootprint M J n copies T S parent child) := by
  intros
  simp [queryPhysicalTableReadHeap, queryPhysicalTableReadFootprint, queryPhysicalTableRead]

@[simp] theorem queryMeanReadHeap_footprint :
    ∀ {ι : Type u_1} (count : Nat)
  (reader : Fin count → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (i : Fin count) → @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader i)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryMeanRead.{u_1} ι count reader))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryMeanRead.{u_1} ι count reader)
      (@OAI.EditApproximation.queryMeanReadHeap.{u_1} ι count reader hr))
    (@OAI.EditApproximation.queryMeanReadFootprint.{u_1} ι count reader fun i =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader i) (hr i)) := by
  intros
  simp [queryMeanReadHeap, queryMeanReadFootprint, queryMeanRead]

@[simp] theorem queryPhysicalEarlierReadHeap_footprint :
    ∀ {M J n : Nat} (copies pass copy T S t : Nat) (node : OAI.EditApproximation.PhysicalNode M J)
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          node))
      J)
  (q : OAI.EditApproximation.TargetInterval n)
  (input : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval n))),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S child)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
            (@OAI.EditApproximation.PhysicalTableRequest.refinement M J n pass copy node T t q)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalEarlierRead M J n copies pass copy T S t node hbelow q input))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S child)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
            (@OAI.EditApproximation.PhysicalTableRequest.refinement M J n pass copy node T t q)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalEarlierRead M J n copies pass copy T S t node hbelow q input)
      (@OAI.EditApproximation.queryPhysicalEarlierReadHeap M J n copies pass copy T S t node hbelow q input))
    (@OAI.EditApproximation.queryPhysicalEarlierReadFootprint M J n copies pass copy T S t node hbelow q input) := by
  intros
  unfold queryPhysicalEarlierReadHeap queryPhysicalEarlierReadFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  with_unfolding_all apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    rfl
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    apply queryPhysicalTableReadHeap_footprint

@[simp] theorem queryPhysicalRandomDataRequestHeap_footprint :
    ∀ {σ : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M J : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (copies pass copy T S t : Nat)
  (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
  (node : OAI.EditApproximation.PhysicalNode M J)
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          node))
      J)
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} σ OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} σ OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} σ OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} σ OAI.EditApproximation.BinaryFraction (readInteger key range)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_2} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_2} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalRandomDataRequest.{u_1, u_2} σ α source target M J _inst N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_2} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_2} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalRandomDataRequest.{u_1, u_2} σ α source target M J _inst N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q)
      (@OAI.EditApproximation.queryPhysicalRandomDataRequestHeap.{u_1, u_2} σ α source target M J _inst N P F exponent H
        Q eM eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q hg hz))
    (@OAI.EditApproximation.queryPhysicalRandomDataRequestFootprint.{u_1, u_2} σ α source target M J _inst N P F exponent
      H Q eM eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} σ OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      fun key range =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} σ OAI.EditApproximation.BinaryFraction
        (readInteger key range) (hz key range)) := by
  intros
  unfold queryPhysicalRandomDataRequestHeap queryPhysicalRandomDataRequestFootprint queryPhysicalRandomDataRequest
  refine (queryLocalProgramHeap_footprint ..).trans ?_
  apply footprint_congr_seven
  all_goals funext input
  all_goals try funext range
  all_goals refine (BitQuery.Heap.footprint_mapKeysWithWork _ _ _ _).trans ?_
  all_goals apply congrArg (BitQuery.Footprint.mapKeysWithWork _ _)
  all_goals first
    | rfl
    | apply queryPhysicalTableReadHeap_footprint
    | apply queryPhysicalEarlierReadHeap_footprint
    | (refine (queryMeanReadHeap_footprint ..).trans ?_; congr 1)

@[simp] theorem queryPhysicalScalarReadHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction (OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B key)
      (OAI.EditApproximation.queryPhysicalScalarReadHeap M J N n exponent F Q R B key))
    (OAI.EditApproximation.queryPhysicalScalarReadFootprint M J N n exponent F Q R B key) := by
  intros
  simp [queryPhysicalScalarReadHeap, queryPhysicalScalarReadFootprint, queryPhysicalScalarRead]

private def scalarGroupFootprintBridge (M J N n exponent F Q R B : ℕ)
    (node : PhysicalInternalNode M J) (time : Fin R) (b : ℕ) (cell : ℕ × ℕ) :
    ∀ s j, BitQuery.Footprint (queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j) := by
  intro s j
  refine (congrArg BitQuery.Footprint (congrArg
    (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
    (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell))).mpr ?_
  split
  · rename_i hb
    split
    · rename_i hc
      let key : PhysicalLocalGroupKey M J N n exponent :=
        (node, physicalScaleIndex N b ((queryScalePresentWithWork_value N b).mp hb),
          ⟨cell.1, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).1⟩,
          ⟨cell.2, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).2⟩)
      exact groupFootprintTransportBridge M J N n exponent F Q R B _ _
        (physicalScaleIndex_get N b ((queryScalePresentWithWork_value N b).mp hb))
        (queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
        (fun s j => (congrArg BitQuery.Footprint
          (queryPhysicalScalarGroupQueriesAt.eq_1 M J N n exponent F Q R B key time s j)).mpr
            (queryPhysicalScalarReadFootprint M J N n exponent F Q R B
              ⟨Sum.inr key, ⟨time, ⟨s, j⟩⟩⟩)) s j
    · exact .done _
  · exact .done _

@[simp] theorem queryPhysicalScalarGroupQueriesHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R) (b : Nat)
  (cell : Prod.{0, 0} Nat Nat)
  (s : Fin (@List.length.{0} Rat (OAI.EditApproximation.groupDyadicScales M b (@Nat.cast.{0} Rat Rat.instNatCast F))))
  (j :
    Fin
      (OAI.EditApproximation.groupSampleCount M Q b
        (OAI.EditApproximation.groupDyadicScaleAt M b (@Nat.cast.{0} Rat Rat.instNatCast F) s))),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j)
      (OAI.EditApproximation.queryPhysicalScalarGroupQueriesHeap M J N n exponent F Q R B node time b cell s j))
    (OAI.EditApproximation.queryPhysicalScalarGroupQueriesFootprint M J N n exponent F Q R B node time b cell s j) := by
  intro M J N n exponent F Q R B node time b cell s j
  have hbridge : (queryPhysicalScalarGroupQueriesHeap M J N n exponent F Q R B node time b cell s j).footprint =
      scalarGroupFootprintBridge M J N n exponent F Q R B node time b cell s j := by
    unfold queryPhysicalScalarGroupQueriesHeap scalarGroupFootprintBridge
    apply footprint_mpr_congr (congrArg
      (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
      (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell))
    dsimp only [id]
    rw [footprint_cases (instDecidableEqBool (queryScalePresentWithWork N b).1 true)]
    refine congrFun ?_ (instDecidableEqBool (queryScalePresentWithWork N b).1 true)
    funext decision
    cases decision with
    | isFalse h =>
        apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_right h))
        rfl
    | isTrue h =>
        apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_left h))
        rw [footprint_cases (instDecidableEqBool (queryCellValidWithWork n exponent cell).1 true)]
        refine congrFun ?_ (instDecidableEqBool (queryCellValidWithWork n exponent cell).1 true)
        funext decision
        cases decision with
        | isFalse h' =>
            apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_right h'))
            rfl
        | isTrue h' =>
            apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_left h'))
            let key : PhysicalLocalGroupKey M J N n exponent :=
              (node, physicalScaleIndex N b ((queryScalePresentWithWork_value N b).mp h),
                ⟨cell.1, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp h').1⟩,
                ⟨cell.2, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp h').2⟩)
            with_unfolding_all
              apply footprint_groupTransport M J N n exponent F Q R B _ b
                (physicalScaleIndex_get N b ((queryScalePresentWithWork_value N b).mp h))
                (queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
            intro scale sample
            apply footprint_mpr_congr
              (queryPhysicalScalarGroupQueriesAt.eq_1 M J N n exponent F Q R B key time scale sample)
            apply queryPhysicalScalarReadHeap_footprint
  have hsame : queryPhysicalScalarGroupQueriesFootprint M J N n exponent F Q R B node time b cell s j =
      scalarGroupFootprintBridge M J N n exponent F Q R B node time b cell s j := by
    have heq_mpr_right {α β γ : Sort _} (eqn : α = β) (a : γ) (b : β) (hab : HEq a b) :
        HEq a (eqn.mpr b) := by
      cases eqn
      exact hab
    apply eq_of_heq
    unfold scalarGroupFootprintBridge
    apply heq_mpr_right (congrArg BitQuery.Footprint (congrArg
      (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
      (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell)))
    unfold queryPhysicalScalarGroupQueriesFootprint
    direct_decidable_heq
    · exact heq_of_eq (id_eq _)
    · rfl
    · intro h
      direct_mpr_heq
      rfl
    · intro h
      direct_mpr_heq
      direct_decidable_heq
      · rfl
      · rfl
      · intro h'
        direct_mpr_heq
        rfl
      · intro h'
        direct_mpr_heq
        rfl
  exact hbridge.trans hsame.symm


@[simp] theorem queryPhysicalScalarGroupReadHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : OAI.EditApproximation.GroupScalarKey M F Q),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key)
      (OAI.EditApproximation.queryPhysicalScalarGroupReadHeap M J N n exponent F Q R B node time key))
    (OAI.EditApproximation.queryPhysicalScalarGroupReadFootprint M J N n exponent F Q R B node time key) := by
  intros
  simp [queryPhysicalScalarGroupReadHeap, queryPhysicalScalarGroupReadFootprint, queryPhysicalScalarGroupRead]

private def scalarOnlineFootprintBridge (M J N n exponent F Q R B : ℕ)
    (node : PhysicalInternalNode M J) (time : Fin R) (key : ℕ × TargetInterval n) (range : ℕ) :
    BitQuery.Footprint (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range) := by
  refine (congrArg BitQuery.Footprint
    (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range)).mpr ?_
  refine BitQuery.Footprint.chargeOf
    (queryScalePresentAllocation N key.1 + queryRangeValidAllocation B range) ?_
  split
  · rename_i hb
    split
    · rename_i hr
      exact queryPhysicalScalarReadFootprint M J N n exponent F Q R B
        ⟨.inl ((node, physicalScaleIndex N key.1 ((queryScalePresentWithWork_value N key.1).mp hb), key.2),
          positiveDrawRangeOfLE B range ((queryRangeValidWithWork_value B range).mp hr).1
            ((queryRangeValidWithWork_value B range).mp hr).2), time⟩
    · exact .done _
  · exact .done _

@[simp] theorem queryPhysicalScalarOnlineReadHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval n)) (range : Nat),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range)
      (OAI.EditApproximation.queryPhysicalScalarOnlineReadHeap M J N n exponent F Q R B node time key range))
    (OAI.EditApproximation.queryPhysicalScalarOnlineReadFootprint M J N n exponent F Q R B node time key range) := by
  intro M J N n exponent F Q R B node time key range
  have hbridge : (queryPhysicalScalarOnlineReadHeap M J N n exponent F Q R B node time key range).footprint =
      scalarOnlineFootprintBridge M J N n exponent F Q R B node time key range := by
    unfold queryPhysicalScalarOnlineReadHeap scalarOnlineFootprintBridge
    apply footprint_mpr_congr
      (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range)
    apply congrArg (BitQuery.Footprint.charge _)
    rw [footprint_cases (instDecidableEqBool (queryScalePresentWithWork N key.1).1 true)]
    congr! (config := {closePre := false, closePost := false, sameFun := true}) 1
    · funext h
      apply footprint_mpr_congr (dite_eq_right h)
      rfl
    · funext h
      apply footprint_mpr_congr (dite_eq_left h)
      rw [footprint_cases (instDecidableEqBool (queryRangeValidWithWork B range).1 true)]
      congr! (config := {closePre := false, closePost := false, sameFun := true}) 1
      · funext h'
        apply footprint_mpr_congr (dite_eq_right h')
        rfl
      · funext h'
        apply footprint_mpr_congr (dite_eq_left h')
        apply queryPhysicalScalarReadHeap_footprint
  have hsame : queryPhysicalScalarOnlineReadFootprint M J N n exponent F Q R B node time key range =
      scalarOnlineFootprintBridge M J N n exponent F Q R B node time key range := by
    have heq_mpr_right {α β γ : Sort _} (eqn : α = β) (a : γ) (b : β) (hab : HEq a b) :
        HEq a (eqn.mpr b) := by
      cases eqn
      exact hab
    apply eq_of_heq
    unfold scalarOnlineFootprintBridge
    apply heq_mpr_right (congrArg BitQuery.Footprint
      (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range))
    unfold queryPhysicalScalarOnlineReadFootprint
    dsimp (config := {beta := false, iota := false, proj := false}) only
    apply heq_of_eq
    apply congrArg (BitQuery.Footprint.chargeOf
      (queryScalePresentAllocation N key.1 + queryRangeValidAllocation B range))
    direct_decidable_heq
    · rfl
    · rfl
    · intro h
      direct_mpr_heq
      rfl
    · intro h
      direct_mpr_heq
      direct_decidable_heq
      · rfl
      · rfl
      · intro h'
        direct_mpr_heq
        rfl
      · intro h'
        direct_mpr_heq
        rfl
  exact hbridge.trans hsame.symm

@[simp] theorem queryFamilyGroupReadHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} (target : List.{u_1} α) (N P F exponent H Q passes copies pass copy : Nat)
  (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : OAI.EditApproximation.GroupScalarKey M F Q),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyGroupRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyGroupRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key)
      (@OAI.EditApproximation.queryFamilyGroupReadHeap.{u_1} α M J R target N P F exponent H Q passes copies pass copy
        node time key))
    (@OAI.EditApproximation.queryFamilyGroupReadFootprint.{u_1} α M J R target N P F exponent H Q passes copies pass
      copy node time key) := by
  intros
  simp [queryFamilyGroupReadHeap, queryFamilyGroupReadFootprint, queryFamilyGroupRead]

@[simp] theorem queryFamilyOnlineReadHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} (target : List.{u_1} α) (N P F exponent H Q passes copies pass copy : Nat)
  (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_1} α target))) (range : Nat),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyOnlineRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key range))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyOnlineRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key range)
      (@OAI.EditApproximation.queryFamilyOnlineReadHeap.{u_1} α M J R target N P F exponent H Q passes copies pass copy
        node time key range))
    (@OAI.EditApproximation.queryFamilyOnlineReadFootprint.{u_1} α M J R target N P F exponent H Q passes copies pass
      copy node time key range) := by
  intros
  simp [queryFamilyOnlineReadHeap, queryFamilyOnlineReadFootprint, queryFamilyOnlineRead]

@[simp] theorem queryRestrictPhysicalBodyHeap_footprint :
    ∀ {σ : Type u_1} {M J n : Nat} (passes copies T S : Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
  (program :
    OAI.EditApproximation.BitQuery.{u_1, 0}
      (@OAI.EditApproximation.QueryPhysicalChild.{u_1} σ M J n passes copies T S parent)
      OAI.EditApproximation.BinaryFraction)
  (heap :
    @OAI.EditApproximation.BitQuery.Heap.{u_1, 0}
      (@OAI.EditApproximation.QueryPhysicalChild.{u_1} σ M J n passes copies T S parent)
      OAI.EditApproximation.BinaryFraction program),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryRestrictPhysicalBody.{u_1} σ M J n passes copies T S parent program))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryRestrictPhysicalBody.{u_1} σ M J n passes copies T S parent program)
      (@OAI.EditApproximation.queryRestrictPhysicalBodyHeap.{u_1} σ M J n passes copies T S parent program heap))
    (@OAI.EditApproximation.queryRestrictPhysicalBodyFootprint.{u_1} σ M J n passes copies T S parent program
      (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0}
        (@OAI.EditApproximation.QueryPhysicalChild.{u_1} σ M J n passes copies T S parent)
        OAI.EditApproximation.BinaryFraction program heap)) := by
  intros
  simp [queryRestrictPhysicalBodyHeap, queryRestrictPhysicalBodyFootprint, queryRestrictPhysicalBody]

@[simp] theorem queryFamilyRefinementHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (source target : List.{u_1} α) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (passes copies pass copy T S t : Nat)
  (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
  (node : OAI.EditApproximation.PhysicalNode M J)
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          node))
      J)
  (time : Fin R) (q : OAI.EditApproximation.TargetInterval (@List.length.{u_1} α target)),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_1} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyRefinement.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_1} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyRefinement.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q)
      (@OAI.EditApproximation.queryFamilyRefinementHeap.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q))
    (@OAI.EditApproximation.queryFamilyRefinementFootprint.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP
      hM hF tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q) := by
  intros
  simp [queryFamilyRefinementHeap, queryFamilyRefinementFootprint, queryFamilyRefinement]

@[simp] theorem queryFamilyActiveHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{u_1} α)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (T S passes copies : Nat)
  (request : OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
  (hindex :
    @LT.lt.{0} Nat instLTNat T
      (@OAI.EditApproximation.PhysicalTableRequest.index M J (@List.length.{u_1} α target) request))
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          (@OAI.EditApproximation.PhysicalTableRequest.node M J (@List.length.{u_1} α target) request)))
      J),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S request)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta T S passes copies request hindex hbelow))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S request)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta T S passes copies request hindex hbelow)
      (@OAI.EditApproximation.queryFamilyActiveHeap.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta T S passes copies request hindex hbelow))
    (@OAI.EditApproximation.queryFamilyActiveFootprint.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta T S passes copies request hindex hbelow) := by
  intros
  simp [queryFamilyActiveHeap, queryFamilyActiveFootprint, queryFamilyActive]

@[simp] theorem queryFamilyBoundedActiveHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{u_1} α)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (T S passes copies : Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        copies T S r)
  (hindex :
    @LT.lt.{0} Nat instLTNat T
      (@OAI.EditApproximation.PhysicalTableRequest.index M J (@List.length.{u_1} α target)
        (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
          (fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S r)
          parent)))
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          (@OAI.EditApproximation.PhysicalTableRequest.node M J (@List.length.{u_1} α target)
            (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
              (fun r =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  copies T S r)
              parent))))
      J),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyBoundedActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF
        hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyBoundedActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF
        hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow)
      (@OAI.EditApproximation.queryFamilyBoundedActiveHeap.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow))
    (@OAI.EditApproximation.queryFamilyBoundedActiveFootprint.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q
      eM eF hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow) := by
  intros
  simp [queryFamilyBoundedActiveHeap, queryFamilyBoundedActiveFootprint, queryFamilyBoundedActive]

@[simp] theorem queryInitialConeProgramAtHeap_footprint :
    ∀ {ι : Type u_1} {n : Nat} (sourceLength N P F : Nat) (A a : OAI.EditApproximation.BinaryFraction)
  (reader :
    OAI.EditApproximation.TargetInterval n →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval n)
  (hr :
    (r : OAI.EditApproximation.TargetInterval n) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader r)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryInitialConeProgramAt.{u_1} ι n sourceLength N P F A a reader q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryInitialConeProgramAt.{u_1} ι n sourceLength N P F A a reader q)
      (@OAI.EditApproximation.queryInitialConeProgramAtHeap.{u_1} ι n sourceLength N P F A a reader q hr))
    (@OAI.EditApproximation.queryInitialConeProgramAtFootprint.{u_1} ι n sourceLength N P F A a reader q fun r =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader r) (hr r)) := by
  intros
  simp [queryInitialConeProgramAtHeap, queryInitialConeProgramAtFootprint, queryInitialConeProgramAt]

@[simp] theorem queryChargedReadHeap_footprint :
    ∀ {M J n passes copies T S : Nat}
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
  (key :
    @Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
      @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
        (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
          (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
            (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
              @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
            parent))),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction (@OAI.EditApproximation.queryChargedRead M J n passes copies T S parent key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction (@OAI.EditApproximation.queryChargedRead M J n passes copies T S parent key)
      (@OAI.EditApproximation.queryChargedReadHeap M J n passes copies T S parent key))
    (@OAI.EditApproximation.queryChargedReadFootprint M J n passes copies T S parent key) := by
  intros
  simp [queryChargedReadHeap, queryChargedReadFootprint, queryChargedRead]

@[simp] theorem queryChargedSeedAtHeap_footprint :
    ∀ {M J n passes copies T S : Nat}
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
  (N : Nat) (multiplier : Nat → Nat) (q : OAI.EditApproximation.TargetInterval n),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedSeedAt M J n passes copies T S parent N multiplier q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedSeedAt M J n passes copies T S parent N multiplier q)
      (@OAI.EditApproximation.queryChargedSeedAtHeap M J n passes copies T S parent N multiplier q))
    (@OAI.EditApproximation.queryChargedSeedAtFootprint M J n passes copies T S parent N multiplier q) := by
  intros
  unfold queryChargedSeedAtHeap queryChargedSeedAtFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    refine (BitQuery.Heap.footprint_chargeOf _ _ _).trans ?_
    apply congrArg (BitQuery.Footprint.chargeOf _)
    refine (BitQuery.Heap.footprint_collect _ _ _ _ _).trans ?_
    congr 1
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    apply queryChargedReadHeap_footprint

@[simp] theorem queryWarmupProgramHeap_footprint :
    ∀ {ι : Type u_1} {nx ny M : Nat} (parent : OAI.EditApproximation.TargetInterval nx) (N P F : Nat)
  (a : OAI.EditApproximation.BinaryFraction)
  (initialRead :
    OAI.EditApproximation.TargetInterval ny →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (childRead :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval ny)
  (hi :
    (r : OAI.EditApproximation.TargetInterval ny) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (initialRead r))
  (hc :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (childRead key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryWarmupProgram.{u_1} ι nx ny M parent N P F a initialRead childRead q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryWarmupProgram.{u_1} ι nx ny M parent N P F a initialRead childRead q)
      (@OAI.EditApproximation.queryWarmupProgramHeap.{u_1} ι nx ny M parent N P F a initialRead childRead q hi hc))
    (@OAI.EditApproximation.queryWarmupProgramFootprint.{u_1} ι nx ny M parent N P F a initialRead childRead q
      (fun r =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (initialRead r)
          (hi r))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (childRead key)
        (hc key)) := by
  intros
  simp [queryWarmupProgramHeap, queryWarmupProgramFootprint, queryWarmupProgram]

@[simp] theorem queryPhysicalInitialHeap_footprint :
    ∀ (source target : List.{0} Nat) {M J passes copies T S : Nat} (N P F : Nat)
  (A a : OAI.EditApproximation.BinaryFraction) (multiplier : Nat → Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S r)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat) (q : OAI.EditApproximation.TargetInterval (@List.length.{0} Nat target)),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalInitial source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalInitial source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits q)
      (@OAI.EditApproximation.queryPhysicalInitialHeap source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits q))
    (@OAI.EditApproximation.queryPhysicalInitialFootprint source target M J passes copies T S N P F A a multiplier
      parent occurrence symbolBits positionBits q) := by
  intros
  unfold queryPhysicalInitialHeap queryPhysicalInitialFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (ite_eq_right h)
    simp
  · intro h
    apply footprint_mpr_congr (ite_eq_left h)
    rfl

@[simp] theorem queryChargedWarmupHeap_footprint :
    ∀ (source target : List.{0} Nat) {M J passes copies T S : Nat} (N P F : Nat)
  (A a : OAI.EditApproximation.BinaryFraction) (multiplier : Nat → Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S r)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedWarmup source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedWarmup source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits)
      (@OAI.EditApproximation.queryChargedWarmupHeap source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits))
    (@OAI.EditApproximation.queryChargedWarmupFootprint source target M J passes copies T S N P F A a multiplier parent
      occurrence symbolBits positionBits) := by
  intros
  unfold queryChargedWarmupHeap queryChargedWarmupFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    apply congrArg (BitQuery.Footprint.charge _)
    rw [footprint_cases]
    apply cases_congr
    · intro h'
      apply footprint_mpr_congr (dite_eq_right h')
      simp
    · intro h'
      apply footprint_mpr_congr (dite_eq_left h')
      apply congrArg (BitQuery.Footprint.charge _)
      rw [footprint_cases]
      apply cases_congr
      · intro h''
        apply footprint_mpr_congr (ite_eq_right h'')
        refine (queryWarmupProgramHeap_footprint _ _ _ _ _ _ _ _ _ _).trans ?_
        congr 1
        funext r
        apply queryPhysicalInitialHeap_footprint
      · intro h''
        apply footprint_mpr_congr (ite_eq_left h'')
        simp
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    simp

@[simp] theorem queryChargedFamilyTableHeap_footprint :
    ∀ {M J R passes copies T S : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{0} Nat)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (A a : Nat → OAI.EditApproximation.BinaryFraction) (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
  (multiplier : Nat → Nat) (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        copies T S r),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q
        (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun request =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S request)
          parent))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyTable M J R passes copies T S _inst _inst_1 source target N P F exponent H
        Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q
        (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun request =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S request)
          parent))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyTable M J R passes copies T S _inst _inst_1 source target N P F exponent H
        Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent)
      (@OAI.EditApproximation.queryChargedFamilyTableHeap M J R passes copies T S _inst _inst_1 source target N P F
        exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent))
    (@OAI.EditApproximation.queryChargedFamilyTableFootprint M J R passes copies T S _inst _inst_1 source target N P F
      exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent) := by
  intros
  unfold queryChargedFamilyTableHeap queryChargedFamilyTableFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    apply congrArg (BitQuery.Footprint.charge _)
    rw [footprint_cases]
    apply cases_congr
    · intro h'
      apply footprint_mpr_congr (dite_eq_right h')
      simp
    · intro h'
      apply footprint_mpr_congr (dite_eq_left h')
      apply congrArg (BitQuery.Footprint.charge _)
      rw [footprint_cases]
      apply cases_congr
      · intro h''
        apply footprint_mpr_congr (ite_eq_right h'')
        simp
      · intro h''
        apply footprint_mpr_congr (ite_eq_left h'')
        simp
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    simp

@[simp] theorem queryChargedFamilyGlobalHeap_footprint :
    ∀ {M J R passes copies T S : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{0} Nat)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (A a : Nat → OAI.EditApproximation.BinaryFraction) (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
  (multiplier : Nat → Nat) (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat)
  (coarse :
    OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) → Nat)
  (hc :
    ∀ (entry : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target)),
      @LE.le.{0} Nat instLENat (allocation entry)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (coarse entry))))
  (request :
    OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      copies T S),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q request)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyGlobal M J R passes copies T S _inst _inst_1 source target N P F exponent
        H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q request)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyGlobal M J R passes copies T S _inst _inst_1 source target N P F exponent
        H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request)
      (@OAI.EditApproximation.queryChargedFamilyGlobalHeap M J R passes copies T S _inst _inst_1 source target N P F
        exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse
        allocation hc request))
    (@OAI.EditApproximation.queryChargedFamilyGlobalFootprint M J R passes copies T S _inst _inst_1 source target N P F
      exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse
      allocation request) := by
  intros
  rename_i request
  cases request <;> simp [queryChargedFamilyGlobalHeap, queryChargedFamilyGlobalFootprint, queryChargedFamilyGlobal]

@[simp] theorem queryFamilyMemoRawHeap_footprint :
    ∀ {M J R passes copies T S : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{0} Nat)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (A a : Nat → OAI.EditApproximation.BinaryFraction) (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
  (multiplier : Nat → Nat) (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat)
  (coarse :
    OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) → Nat)
  (hc :
    ∀ (entry : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target)),
      @LE.le.{0} Nat instLENat (allocation entry)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (coarse entry))))
  (draw : @OAI.EditApproximation.PhysicalFamilyScalarDraw.{0} Nat M J R target N P F exponent H Q passes copies)
  (key : @OAI.EditApproximation.QueryFamilyMemoKey M J R passes copies T S target N P F exponent H Q),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
          (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            copies T S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            key))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyMemoRaw M J R passes copies T S _inst _inst_1 source target N P F exponent H Q eM
        eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
          (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            copies T S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            key))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyMemoRaw M J R passes copies T S _inst _inst_1 source target N P F exponent H Q eM
        eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key)
      (@OAI.EditApproximation.queryFamilyMemoRawHeap M J R passes copies T S _inst _inst_1 source target N P F exponent H
        Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation hc draw
        key))
    (@OAI.EditApproximation.queryFamilyMemoRawFootprint M J R passes copies T S _inst _inst_1 source target N P F exponent
      H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation draw
      key) := by
  intros
  rename_i key
  cases key <;> simp [queryFamilyMemoRawHeap, queryFamilyMemoRawFootprint, queryFamilyMemoRaw]
  · apply BitQuery.Heap.footprint_computeOf
  · refine (BitQuery.Heap.footprint_mapKeysWithWork _ _ _ _).trans ?_
    apply congrArg (BitQuery.Footprint.mapKeysWithWork _ _)
    apply queryChargedFamilyGlobalHeap_footprint

@[simp] theorem computedQueryMemoRawHeap_footprint :
    ∀ (source target : List.{0} Nat) (N : Nat)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat) (input : OAI.EditApproximation.ComputedFamilyInput source target N)
  (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
              (OAI.EditApproximation.smallLogExponent N))
            (OAI.EditApproximation.inputHeight N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (OAI.EditApproximation.computedSeedPassCount N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (OAI.EditApproximation.ChargedPhysicalRequest
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (OAI.EditApproximation.computedSeedPassCount N)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoRaw source target N occurrence symbolBits positionBits input key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
              (OAI.EditApproximation.smallLogExponent N))
            (OAI.EditApproximation.inputHeight N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (OAI.EditApproximation.computedSeedPassCount N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (OAI.EditApproximation.ChargedPhysicalRequest
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (OAI.EditApproximation.computedSeedPassCount N)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoRaw source target N occurrence symbolBits positionBits input key)
      (OAI.EditApproximation.computedQueryMemoRawHeap source target N occurrence symbolBits positionBits input key))
    (OAI.EditApproximation.computedQueryMemoRawFootprint source target N occurrence symbolBits positionBits input key) := by
  intros
  simp [computedQueryMemoRawHeap, computedQueryMemoRawFootprint, computedQueryMemoRaw]
  with_unfolding_all apply queryFamilyMemoRawHeap_footprint

@[simp] theorem computedQueryMemoHeap_footprint :
    ∀ (source target : List.{0} Nat) (N : Nat)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat) (input : OAI.EditApproximation.ComputedFamilyInput source target N)
  (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ComputedFamilyMemoKey source target N) fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            child)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ComputedFamilyMemoKey source target N) fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            child)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key)
      (OAI.EditApproximation.computedQueryMemoHeap source target N occurrence symbolBits positionBits input key))
    (OAI.EditApproximation.computedQueryMemoFootprint source target N occurrence symbolBits positionBits input key) := by
  intro source target N occurrence symbolBits positionBits input key
  unfold computedQueryMemoHeap computedQueryMemoFootprint
  refine (BitQuery.Heap.footprint_normalize _ _ _ _).trans ?_
  exact congrArg
      (fun footprint : BitQuery.Footprint
          (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key) =>
        footprint.normalize (computedQueryBase N) (computedQueryBase_pos N)
          (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
            (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key))
      (computedQueryMemoRawHeap_footprint source target N occurrence symbolBits positionBits input key)

end OAI.EditApproximation
