import Mathlib.Algebra.BigOperators.Module
import OAI.Computability.PerfectCompleteness.Construction.DescendantSpacesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.LinearEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas

namespace OAI

section

namespace PerfectCompleteness.TriangularFolding

open MixedSupport CanonicalKeys PointwiseSpaces

variable {A B X : Type*} [AddCommGroup A]

def translate (q : B → A) : A × B ≃ A × B where
  toFun y := (y.1 + q y.2, y.2)
  invFun y := (y.1 - q y.2, y.2)
  left_inv y := by ext <;> simp
  right_inv y := by ext <;> simp

@[simp] theorem translate_first (q : B → A) (y : A × B) :
    (translate q y).1 = y.1 + q y.2 := rfl

@[simp] theorem translate_second (q : B → A) (y : A × B) :
    (translate q y).2 = y.2 := rfl

def shifted (f : X → A × B) (q : B → A) : X → A × B := translate q ∘ f

theorem shifted_kernel (f : X → A × B) (q : B → A) (x x' : X) :
    f x = f x' ↔ shifted f q x = shifted f q x' :=
  ⟨fun h => congrArg (translate q) h, fun h => (translate q).injective h⟩

theorem key_shifted {n : Nat} (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → A × B) (q : B → A) :
    key side slots (shifted f q) = key side slots f :=
  key_postcomp_equiv side slots f (translate q)

noncomputable def shiftLabel {n : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → A × B) (q : B → A) (P : Label slots f) :
    Label slots (shifted f q) :=
  transportKernel slots f (shifted f q) (shifted_kernel f q) P

theorem restore_shiftLabel {n : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → A × B) (q : B → A) (P : Label slots f) :
    restore slots (shifted f q) (shiftLabel slots f q P) =
      ((restore slots f P).1 + q (restore slots f P).2, (restore slots f P).2) :=
  restore_transportKernel slots f (shifted f q) (shifted_kernel f q)
    (translate q) (fun _ => rfl) P

def displayedTranslate {I : Type*} [DecidableEq I] (V : I → Type*)
    [∀ i, AddCommGroup (V i)] (B : Type*) (selected : I)
    (q : BlockQuotient.OtherBlocks V selected × B → V selected) :
    BlockQuotient.JointOutput V B ≃
      V selected × (BlockQuotient.OtherBlocks V selected × B) :=
  (BlockQuotient.splitOutput V B selected).trans (translate q)

theorem key_displayedTranslate {n : Nat} {I : Type*} [DecidableEq I]
    (V : I → Type*) [∀ i, AddCommGroup (V i)] (B : Type*)
    (side : Side) (slots : Fin n → Slot) (f : Assignment slots → BlockQuotient.JointOutput V B)
    (selected : I) (q : BlockQuotient.OtherBlocks V selected × B → V selected) :
    key side slots (displayedTranslate V B selected q ∘ f) = key side slots f :=
  key_postcomp_equiv side slots f (displayedTranslate V B selected q)

section Quadratics

variable {𝕜 J : Type*} [Field 𝕜] [Fintype J]

open scoped BigOperators

def quadraticValue (c : 𝕜) (coeff : J → J → 𝕜) (values : J → 𝕜) : 𝕜 :=
  c + ∑ i, ∑ j, coeff i j * (values i * values j)

def quadraticFunction (c : 𝕜) (coeff : J → J → 𝕜) (rows : J → X → 𝕜) : X → 𝕜 :=
  c • 1 + ∑ i, ∑ j, coeff i j • (rows i * rows j)

@[simp] theorem quadraticFunction_apply (c : 𝕜) (coeff : J → J → 𝕜)
    (rows : J → X → 𝕜) (x : X) :
    quadraticFunction c coeff rows x = quadraticValue c coeff (fun i => rows i x) := by
  simp [quadraticFunction, quadraticValue, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem quadraticFunction_mem_squareSpace (H : Submodule 𝕜 (X → 𝕜))
    (hone : (1 : X → 𝕜) ∈ H) (c : 𝕜) (coeff : J → J → 𝕜)
    (rows : J → H) : quadraticFunction c coeff (fun i => (rows i).val) ∈ squareSpace H := by
  apply (squareSpace H).add_mem
  · exact (squareSpace H).smul_mem c (one_mem_squareSpace H hone)
  · apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    exact (squareSpace H).smul_mem (coeff i j)
      (mul_mem_squareSpace H (rows i).property (rows j).property)

theorem quadratic_descendant_mem {branch : Nat → Nat} {n m : Nat}
    (p : DescendantSpaces.Path branch n m)
    (domains : RecursiveSpaces.Slots branch n → Type*)
    (hbranch : ∀ k < n, 0 < branch k) (hproper : m < n)
    (c : 𝕜) (coeff : J → J → 𝕜)
    (rows : J → RecursiveSpaces.space 𝕜 branch m (p.family domains)) :
    pullback 𝕜 (p.restriction domains)
      (quadraticFunction c coeff (fun i => (rows i).val)) ∈
        RecursiveSpaces.space 𝕜 branch n domains := by
  apply DescendantSpaces.descendant_square_le_space p domains hbranch hproper
  apply Submodule.mem_map_of_mem
  apply quadraticFunction_mem_squareSpace
  exact RecursiveSpaces.one_mem_space branch m (p.family domains)
    (fun k hk => hbranch k (Nat.lt_trans hk hproper))

end Quadratics

end PerfectCompleteness.TriangularFolding

end

end OAI
