import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BucketUniformLemmas

namespace OAI

section

namespace PerfectCompleteness.SamplerComposition

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

def ExpansionSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → DrawIndex repeats p → Type (max u w)
  | _, _, _, .refl _, q, A, _ => RecursiveSampler.Tape 𝕜 repeats q A
  | n + 1, _, _, .step i p, q, A, j =>
      match j with
      | Sum.inl j => squareSpace (space 𝕜 branch n (childFamily A j.val))
      | Sum.inr j => ExpansionSpace 𝕜 repeats p q (childFamily A i) j.2

abbrev ExpandedTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :=
  (j : DrawIndex repeats p) → ExpansionSpace 𝕜 repeats p q A j

def zeroFactor (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → (j : DrawIndex repeats p) →
        ExpansionSpace 𝕜 repeats p q A j
  | _, _, _, .refl _, q, A, _ => zeroTape 𝕜 repeats q A
  | n + 1, _, _, .step i p, q, A, j =>
      match j with
      | Sum.inl j => (0 : squareSpace (space 𝕜 branch n (childFamily A j.val)))
      | Sum.inr j => zeroFactor 𝕜 repeats p q (childFamily A i) j.2

def zeroExpandedTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :
    ExpandedTape 𝕜 repeats p q A := zeroFactor 𝕜 repeats p q A

def expandedSubTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m) (q : Path branch m k)
    (A : Slots branch (n + 1) → Type u)
    (t : ExpandedTape 𝕜 repeats (.step i p) q A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    ExpandedTape 𝕜 repeats p q (childFamily A i) := fun j => t (.inr ((h, b), j))

def expand (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → RecursiveSampler.Tape 𝕜 repeats (p.append q) A →
        ExpandedTape 𝕜 repeats p q A
  | _, _, _, .refl _, _, _, t => fun _ => t
  | _n + 1, _, _, .step i p, q, A, t => fun j =>
      match j with
      | Sum.inl j => t (.inl j)
      | Sum.inr j => expand 𝕜 repeats p q (childFamily A i)
          (subTape 𝕜 repeats i (p.append q) A t j.1.1 j.1.2) j.2

def flatten (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → ExpandedTape 𝕜 repeats p q A →
        RecursiveSampler.Tape 𝕜 repeats (p.append q) A
  | _, _, _, .refl _, _, _, t => t ()
  | _n + 1, _, _, .step i p, q, A, t => fun j =>
      match j with
      | Sum.inl j => t (.inl j)
      | Sum.inr j => flatten 𝕜 repeats p q (childFamily A i)
          (expandedSubTape 𝕜 repeats i p q A t j.1.1 j.1.2) j.2

theorem flatten_expand (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (t : RecursiveSampler.Tape 𝕜 repeats (p.append q) A),
      flatten 𝕜 repeats p q A (expand 𝕜 repeats p q A t) = t := by
  induction p with
  | refl n => intro q A t; rfl
  | @step n m i p ih =>
      intro q A t
      funext j
      cases j with
      | inl j => rfl
      | inr j =>
          exact congrFun
            (ih q (childFamily A i) (subTape 𝕜 repeats i (p.append q) A t j.1.1 j.1.2)) j.2

theorem expand_flatten (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (t : ExpandedTape 𝕜 repeats p q A),
      expand 𝕜 repeats p q A (flatten 𝕜 repeats p q A t) = t := by
  induction p with
  | refl n =>
      intro q A t
      funext j
      cases j
      rfl
  | @step n m i p ih =>
      intro q A t
      funext j
      cases j with
      | inl j => rfl
      | inr j =>
          exact congrFun
            (ih q (childFamily A i) (expandedSubTape 𝕜 repeats i p q A t j.1.1 j.1.2)) j.2

def expandEquiv (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :
    RecursiveSampler.Tape 𝕜 repeats (p.append q) A ≃ ExpandedTape 𝕜 repeats p q A where
  toFun := expand 𝕜 repeats p q A
  invFun := flatten 𝕜 repeats p q A
  left_inv := flatten_expand 𝕜 repeats p q A
  right_inv := expand_flatten 𝕜 repeats p q A

def collapseFactor (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → (j : DrawIndex repeats p) →
        ExpansionSpace 𝕜 repeats p q A j → DrawSpace 𝕜 repeats p A j
  | _, _, _, .refl _, q, A, _ => RecursiveSampler.evaluate 𝕜 repeats q A
  | _, _, _, .step i p, q, A, j =>
      match j with
      | Sum.inl _ => fun t => t
      | Sum.inr j => collapseFactor 𝕜 repeats p q (childFamily A i) j.2

def collapseExpanded (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :
    ExpandedTape 𝕜 repeats p q A → RecursiveSampler.Tape 𝕜 repeats p A :=
  fun t j => collapseFactor 𝕜 repeats p q A j (t j)

def collapseSuffix (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :
    RecursiveSampler.Tape 𝕜 repeats (p.append q) A → RecursiveSampler.Tape 𝕜 repeats p A :=
  collapseExpanded 𝕜 repeats p q A ∘ expandEquiv 𝕜 repeats p q A

theorem evaluate_collapseExpanded (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (t : ExpandedTape 𝕜 repeats p q A),
      RecursiveSampler.evaluate 𝕜 repeats p A (collapseExpanded 𝕜 repeats p q A t) =
        RecursiveSampler.evaluate 𝕜 repeats (p.append q) A (flatten 𝕜 repeats p q A t) := by
  induction p with
  | refl n => intro q A t; rfl
  | @step n m i p ih =>
      intro q A t
      have hl := funext fun h : Fin (repeats (n + 1)) =>
        ih q (childFamily A i) (expandedSubTape 𝕜 repeats i p q A t h false)
      have hr := funext fun h : Fin (repeats (n + 1)) =>
        ih q (childFamily A i) (expandedSubTape 𝕜 repeats i p q A t h true)
      exact congrArg₂
        (fun (left right : Fin (repeats (n + 1)) → space 𝕜 branch n (childFamily A i)) =>
          combine 𝕜 A i (repeats (n + 1)) (fun j => t (.inl j)) left right) hl hr

theorem evaluate_collapseSuffix (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u)
    (t : RecursiveSampler.Tape 𝕜 repeats (p.append q) A) :
    RecursiveSampler.evaluate 𝕜 repeats p A (collapseSuffix 𝕜 repeats p q A t) =
      RecursiveSampler.evaluate 𝕜 repeats (p.append q) A t :=
  (evaluate_collapseExpanded 𝕜 repeats p q A (expand 𝕜 repeats p q A t)).trans
    (congrArg (RecursiveSampler.evaluate 𝕜 repeats (p.append q) A)
      (flatten_expand 𝕜 repeats p q A t))

end
end PerfectCompleteness.SamplerComposition

end

end OAI
