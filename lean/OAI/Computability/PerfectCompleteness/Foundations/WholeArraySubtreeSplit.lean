import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.WholeArraySubtreeSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev subtreeSlots (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Slots branch m → Fin t → MixedSupport.Slot :=
  fun s => slots (p.slotEmbedding s)

def Complement (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, _, .refl _, _, _ => Unit
  | _, _, _, .step i p, q, slots =>
      RootTape rows repeats (.step i (p.append q)) slots ×
        (((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows) ×
          Complement rows repeats p q (childSlots slots i))

@[instance_reducible] def complementFintypeAux (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Complement rows repeats p q slots)
  | _, _, _, .refl _, _, _ => inferInstanceAs (Fintype Unit)
  | _, _, _, .step i p, q, slots =>
      letI := complementFintypeAux rows repeats p q (childSlots slots i)
      inferInstanceAs (Fintype
        (RootTape rows repeats (.step i (p.append q)) slots ×
          (((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows) ×
            Complement rows repeats p q (childSlots slots i))))

instance complementFintype (rows repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Complement rows repeats p q slots) :=
  complementFintypeAux rows repeats p q slots

theorem complementNonemptyAux (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Nonempty (Complement rows repeats p q slots)
  | _, _, _, .refl _, _, _ => inferInstanceAs (Nonempty Unit)
  | _, _, _, .step i p, q, slots =>
      let := complementNonemptyAux rows repeats p q (childSlots slots i)
      inferInstanceAs (Nonempty
        (RootTape rows repeats (.step i (p.append q)) slots ×
          (((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows) ×
            Complement rows repeats p q (childSlots slots i))))

instance complementNonempty (rows repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Complement rows repeats p q slots) :=
  complementNonemptyAux rows repeats p q slots

def splitEquiv (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats (p.append q) slots ≃
          Complement rows repeats p q slots × Tape rows repeats q (subtreeSlots p slots)
  | _, _, _, .refl _, _, _ =>
      { toFun := fun ω => ((), ω)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨u, ω⟩; cases u; rfl }
  | _, _, _, .step i p, q, slots =>
      let e := splitEquiv rows repeats p q (childSlots slots i)
      { toFun := fun ω =>
          ((ω (.inl ()), (fun j => ω (.inr (.inr j)),
              (e (ω (.inr (.inl ())))).1)),
            (e (ω (.inr (.inl ())))).2)
        invFun := fun x field => match field with
          | .inl _ => x.1.1
          | .inr (.inl _) => e.symm (x.1.2.2, x.2)
          | .inr (.inr j) => x.1.2.1 j
        left_inv := by
          intro ω
          funext field
          rcases field with u | (u | j)
          · cases u
            rfl
          · cases u
            exact e.symm_apply_apply (ω (.inr (.inl ())))
          · rfl
        right_inv := by
          rintro ⟨⟨root, ordinary, lower⟩, selected⟩
          change ((root, (ordinary, (e (e.symm (lower, selected))).1)),
            (e (e.symm (lower, selected))).2) = ((root, (ordinary, lower)), selected)
          rw [e.apply_symm_apply]
          rfl }

def extract (rows repeats : Nat → Nat) (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (p.append q) slots) :
    Tape rows repeats q (subtreeSlots p slots) :=
  (splitEquiv rows repeats p q slots ω).2

@[simp] theorem extract_refl (rows repeats : Nat → Nat) (q : Path branch n k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats q slots) :
    extract rows repeats (.refl n) q slots ω = ω := rfl

@[simp] theorem extract_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats ((Path.step i p).append q) slots) :
    extract rows repeats (.step i p) q slots ω =
      extract rows repeats p q (childSlots slots i) (ω (.inr (.inl ()))) := rfl

def restrictArrays (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Arrays slots rows → Arrays (subtreeSlots p slots) rows
  | _, _, .refl _, _, arrays => arrays
  | _, _, .step i p, slots, arrays =>
      restrictArrays rows p (childSlots slots i) (fun node => arrays (.inr (i, node)))

theorem restrictArrays_evaluate (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ {k : Nat} (q : Path branch m k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (ω : Tape rows repeats (p.append q) slots),
      restrictArrays rows p slots (evaluate rows repeats (p.append q) slots ω) =
        evaluate rows repeats q (subtreeSlots p slots) (extract rows repeats p q slots ω) := by
  induction p with
  | refl n => intro k q slots ω; rfl
  | @step n m i p ih =>
      intro k q slots ω
      have hselected := funext (WholeArraySampler.evaluate_selected
        rows repeats i (p.append q) slots ω)
      exact (congrArg (restrictArrays rows p (childSlots slots i)) hselected).trans
        (ih q (childSlots slots i) (ω (.inr (.inl ()))))

def complementLaw (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        FiniteDistribution (Complement rows repeats p q slots)
  | _, _, _, .refl _, _, _ => FiniteDistribution.uniform Unit
  | n + 1, _, _, .step i p, q, slots =>
      (BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i (p.append q))
        (LeafDomain slots)).product
        ((FiniteProduct.law (fun j : RecursiveSampler.OffPath i =>
          FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))).product
          (complementLaw rows repeats p q (childSlots slots i)))

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

private theorem uniform_pushforward_equiv {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform B := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card A : ℝ) = 1 / (Fintype.card B : ℝ)
  rw [Fintype.card_congr e]

theorem rootTapeLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    BucketSampler.recursiveTapeLaw (rows n) repeats p (LeafDomain slots) =
      FiniteDistribution.uniform (RootTape rows repeats p slots) := by
  change FiniteProduct.law (fun _ : BucketSampler.Direction (rows n) =>
    RecursiveSampler.tapeLaw F2 repeats p (LeafDomain slots)) = _
  simp only [RecursiveSampler.tapeLaw_eq_uniform]
  exact UniformLinearImage.law_uniform

local instance stepFactorNonempty {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Nonempty Root] [Nonempty Selected] [∀ j, Nonempty (Ordinary j)]
    (field : StepIndex i) : Nonempty (StepFactor Root Selected Ordinary field) := by
  rcases field with _ | (_ | j) <;> dsimp only [StepFactor] <;> infer_instance

theorem tapeLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ slots : Slots branch n → Fin t → MixedSupport.Slot,
      WholeArraySampler.tapeLaw rows repeats p slots =
        FiniteDistribution.uniform (Tape rows repeats p slots) := by
  induction p with
  | refl n => intro slots; rfl
  | @step n m i p ih =>
      intro slots
      let : (field : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) field) :=
        fun field => stepFactorFintype _ _ _ field
      have hcomponent : componentLaw rows repeats i p slots =
          (fun field : StepIndex i => FiniteDistribution.uniform
            (StepFactor (RootTape rows repeats (.step i p) slots)
              (Tape rows repeats p (childSlots slots i))
              (fun j => Arrays (childSlots slots j.val) rows) field)) := by
        funext field
        rcases field with u | (u | j)
        · cases u
          exact rootTapeLaw_eq_uniform rows repeats (.step i p) slots
        · cases u
          exact ih (childSlots slots i)
        · rfl
      change FiniteProduct.law (componentLaw rows repeats i p slots) = _
      rw [hcomponent]
      exact UniformLinearImage.law_uniform

theorem complementLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ {k : Nat} (q : Path branch m k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot),
      complementLaw rows repeats p q slots =
        FiniteDistribution.uniform (Complement rows repeats p q slots) := by
  induction p with
  | refl n => intro k q slots; rfl
  | @step n m i p ih =>
      intro k q slots
      change (BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i (p.append q))
        (LeafDomain slots)).product
        ((FiniteProduct.law (fun j : RecursiveSampler.OffPath i =>
          FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))).product
          (complementLaw rows repeats p q (childSlots slots i))) =
        FiniteDistribution.uniform
          (RootTape rows repeats (.step i (p.append q)) slots ×
            (((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows) ×
              Complement rows repeats p q (childSlots slots i)))
      rw [rootTapeLaw_eq_uniform rows repeats (.step i (p.append q)) slots,
        UniformLinearImage.law_uniform, ih q (childSlots slots i)]
      rw [uniform_product
        (A := (j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows)
        (B := Complement rows repeats p q (childSlots slots i)), uniform_product]

theorem splitEquiv_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append q) slots).pushforward
        (splitEquiv rows repeats p q slots) =
      (complementLaw rows repeats p q slots).product
        (WholeArraySampler.tapeLaw rows repeats q (subtreeSlots p slots)) := by
  rw [tapeLaw_eq_uniform, uniform_pushforward_equiv, complementLaw_eq_uniform,
    tapeLaw_eq_uniform]
  exact uniform_product.symm

theorem extract_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append q) slots).pushforward
        (extract rows repeats p q slots) =
      WholeArraySampler.tapeLaw rows repeats q (subtreeSlots p slots) := by
  change (WholeArraySampler.tapeLaw rows repeats (p.append q) slots).pushforward
    (fun ω => (splitEquiv rows repeats p q slots ω).2) = _
  rw [← FiniteDistribution.pushforward_comp, splitEquiv_tapeLaw,
    FiniteDistribution.product_pushforward_snd]

theorem restrictArrays_law (rows repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.law rows repeats (p.append q) slots).pushforward
        (restrictArrays rows p slots) =
      WholeArraySampler.law rows repeats q (subtreeSlots p slots) := by
  unfold WholeArraySampler.law
  rw [FiniteDistribution.pushforward_comp]
  have hfun :
      (fun ω : Tape rows repeats (p.append q) slots =>
        restrictArrays rows p slots (evaluate rows repeats (p.append q) slots ω)) =
      (fun ω => evaluate rows repeats q (subtreeSlots p slots)
        (extract rows repeats p q slots ω)) := by
    funext ω
    exact restrictArrays_evaluate rows repeats p q slots ω
  rw [hfun, ← FiniteDistribution.pushforward_comp, extract_tapeLaw]

end
end PerfectCompleteness.WholeArraySubtreeSplit

end

end OAI
