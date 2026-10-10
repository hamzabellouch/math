import OAI.Computability.PerfectCompleteness.Construction.FactoredFunctionsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.PartitionsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaces

namespace OAI


namespace PerfectCompleteness.DescendantSpaces

open PointwiseSpaces RecursiveSpaces

universe u w

inductive Path (branch : Nat → Nat) : Nat → Nat → Type
  | refl (n : Nat) : Path branch n n
  | step {n m : Nat} (i : Fin (branch n)) (tail : Path branch n m) :
      Path branch (n + 1) m

namespace Path

variable {branch : Nat → Nat} {n m : Nat}

def slotEmbedding : {n m : Nat} → Path branch n m → Slots branch m → Slots branch n
  | _, _, .refl _, s => s
  | _, _, .step i p, s => (i, slotEmbedding p s)

@[simp] theorem slotEmbedding_refl (s : Slots branch n) :
    slotEmbedding (.refl n) s = s := rfl

@[simp] theorem slotEmbedding_step (i : Fin (branch n)) (p : Path branch n m)
    (s : Slots branch m) :
    slotEmbedding (.step i p) s = (i, slotEmbedding p s) := rfl

theorem slotEmbedding_injective (p : Path branch n m) :
    Function.Injective p.slotEmbedding := by
  induction p with
  | refl n => exact fun _ _ h => h
  | step i p ih =>
      intro s t h
      exact ih (congrArg Prod.snd h)

theorem height_le (p : Path branch n m) : m ≤ n := by
  induction p with
  | refl n => exact Nat.le_refl n
  | step i p ih => exact Nat.le_trans ih (Nat.le_succ _)

abbrev family (p : Path branch n m) (A : Slots branch n → Type u) :
    Slots branch m → Type u := fun s => A (p.slotEmbedding s)

def restriction (p : Path branch n m) (A : Slots branch n → Type u) :
    Assignment A → Assignment (p.family A) := fun x s => x (p.slotEmbedding s)

@[simp] theorem restriction_apply (p : Path branch n m)
    (A : Slots branch n → Type u) (x : Assignment A) (s : Slots branch m) :
    p.restriction A x s = x (p.slotEmbedding s) := rfl

@[simp] theorem restriction_refl (A : Slots branch n → Type u) :
    restriction (.refl n) A = id := rfl

theorem restriction_step (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (p : Path branch n m) :
    restriction (.step i p) A =
      p.restriction (childFamily A i) ∘ childRestriction A i := rfl

theorem restriction_surjective (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ s, Nonempty (A s)) →
      Function.Surjective (p.restriction A) := by
  induction p with
  | refl n =>
      intro A _ y
      exact ⟨y, rfl⟩
  | step i p ih =>
      intro A hnonempty
      exact (ih (childFamily A i) (fun s => hnonempty (i, s))).comp
        (childRestriction_surjective A hnonempty i)

end Path

variable {𝕜 : Type w} [Field 𝕜] {branch : Nat → Nat} {n m : Nat}

theorem space_descendant_le (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ k < n, 0 < branch k) →
      (space 𝕜 branch m (p.family A)).map (pullback 𝕜 (p.restriction A)) ≤
        space 𝕜 branch n A := by
  induction p with
  | refl n =>
      intro A _ f hf
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
      exact hg
  | @step n m i p ih =>
      intro A hbranch f hf
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
      have hb : ∀ k < n, 0 < branch k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hchild : pullback 𝕜 (p.restriction (childFamily A i)) g ∈
          space 𝕜 branch n (childFamily A i) :=
        ih (childFamily A i) hb (Submodule.mem_map_of_mem hg)
      exact child_le_space A i hb (Submodule.mem_map_of_mem hchild)

theorem squareSpace_descendant_le (p : Path branch n m)
    (A : Slots branch n → Type u) (hbranch : ∀ k < n, 0 < branch k) :
    (squareSpace (space 𝕜 branch m (p.family A))).map
        (pullback 𝕜 (p.restriction A)) ≤ squareSpace (space 𝕜 branch n A) :=
  squareSpace_pullback_le _ _ _ (space_descendant_le p A hbranch)

theorem step_square_le_space (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (p : Path branch n m)
    (hbranch : ∀ k < n, 0 < branch k) :
    (squareSpace (space 𝕜 branch m ((Path.step i p).family A))).map
        (pullback 𝕜 ((Path.step i p).restriction A)) ≤ space 𝕜 branch (n + 1) A := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  have hchild : pullback 𝕜 (p.restriction (childFamily A i)) g ∈
      squareSpace (space 𝕜 branch n (childFamily A i)) :=
    squareSpace_descendant_le p (childFamily A i) hbranch
      (Submodule.mem_map_of_mem hg)
  exact child_square_le_space A i (Submodule.mem_map_of_mem hchild)

theorem descendant_square_le_space (p : Path branch n m)
    (A : Slots branch n → Type u) (hbranch : ∀ k < n, 0 < branch k)
    (hproper : m < n) :
    (squareSpace (space 𝕜 branch m (p.family A))).map
        (pullback 𝕜 (p.restriction A)) ≤ space 𝕜 branch n A := by
  cases p with
  | refl n => exact False.elim (Nat.lt_irrefl n hproper)
  | @step n m i p =>
      exact step_square_le_space A i p
        (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))

theorem descendant_pullback_injective (p : Path branch n m)
    (A : Slots branch n → Type u) (hnonempty : ∀ s, Nonempty (A s)) :
    Function.Injective (pullback 𝕜 (p.restriction A)) :=
  pullback_injective _ (p.restriction_surjective A hnonempty)

end PerfectCompleteness.DescendantSpaces



namespace PerfectCompleteness.DescendantProducts

open RecursiveSpaces DescendantSpaces PointwiseSpaces FactoredFunctionsDependent

variable {𝕜 I : Type*} [Field 𝕜] {branch : Nat → Nat} {n : Nat}
  {height : I → Nat} {Row : I → Type*}

def lower (domains : Slots branch n → Type*)
    (paths : ∀ i, Path branch n (height i))
    (rows : ∀ i, Row i → space 𝕜 branch (height i) ((paths i).family domains)) :
    Assignment domains → (i : I) → Row i → 𝕜 :=
  fun x i row => (rows i row).val ((paths i).restriction domains x)

theorem quadraticSpan_le_ancestor (domains : Slots branch n → Type*)
    (hbranch : ∀ k < n, 0 < branch k)
    (paths : ∀ i, Path branch n (height i)) (hproper : ∀ i, height i < n)
    (rows : ∀ i, Row i → space 𝕜 branch (height i) ((paths i).family domains)) :
    dependentQuadraticSpan (lower domains paths rows) ≤ space 𝕜 branch n domains := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨i, t, u, rfl⟩
  · exact one_mem_space branch n domains hbranch
  · have hp : (rows i t).val * (rows i u).val ∈
        squareSpace (space 𝕜 branch (height i) ((paths i).family domains)) :=
      mul_mem_squareSpace _ (rows i t).property (rows i u).property
    exact descendant_square_le_space (paths i) domains hbranch (hproper i)
      (Submodule.mem_map_of_mem hp)

theorem quadraticSpan_le_displayed (domains : Slots branch n → Type*)
    (paths : ∀ i, Path branch n (height i))
    (rows : ∀ i, Row i → space 𝕜 branch (height i) ((paths i).family domains)) :
    dependentQuadraticSpan (lower domains paths rows) ≤
      FactoredFunctions.factoringSpace (lower domains paths rows) :=
  dependentQuadraticSpan_le_factoringSpace _

def ancestorRow (domains : Slots branch n → Type*)
    (hbranch : ∀ k < n, 0 < branch k)
    (paths : ∀ i, Path branch n (height i)) (hproper : ∀ i, height i < n)
    (rows : ∀ i, Row i → space 𝕜 branch (height i) ((paths i).family domains))
    (shift : dependentQuadraticSpan (lower domains paths rows)) :
    space 𝕜 branch n domains :=
  ⟨shift.val, quadraticSpan_le_ancestor domains hbranch paths hproper rows shift.property⟩

end PerfectCompleteness.DescendantProducts

end OAI
