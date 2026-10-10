import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import OAI.Computability.UniqueGames.Gadgets.ActualGadgetLemmas
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualSource

open UniqueGamesTheorem.Integration.BinaryLinear

structure Source where
  «variables» : Nat
  occurrences : Nat
  nonempty : 0 < occurrences
  equation : Fin occurrences → CloneGap.Equation (Fin «variables»)

def Source.sourceList (S : Source) : List (CloneGap.Equation (Fin S.variables)) :=
  List.ofFn S.equation

/-- Retain every list position as its own occurrence identifier. -/
def Source.ofList {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) : Source where
  «variables» := n
  occurrences := es.length
  nonempty := List.length_pos_iff.mpr hne
  equation := es.get

@[simp] theorem Source.sourceList_ofList {n : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (Source.ofList es hne).sourceList = es := by
  exact List.ofFn_getElem

@[simp] theorem Source.sourceList_length (S : Source) :
    S.sourceList.length = S.occurrences := by simp [Source.sourceList]

theorem Source.sourceList_nonempty (S : Source) : S.sourceList ≠ [] := by
  intro h
  have hp := S.nonempty
  have hn := S.sourceList_length
  rw [h] at hn
  simp only [List.length_nil] at hn
  omega

instance sourceIndexNonempty (S : Source) : Nonempty (Fin S.occurrences) :=
  ⟨⟨0, S.nonempty⟩⟩

def Source.satisfied (S : Source) (A : Fin S.variables → Bool)
    (i : Fin S.occurrences) : Bool := CloneGap.satisfied (S.equation i) A

def Source.failure (S : Source) (A : Fin S.variables → Bool) : ℚ :=
  Finset.univ.expect (fun i => if S.satisfied A i then (0 : ℚ) else 1)

def Source.DistinctNames (S : Source) : Prop :=
  ∀ i, (S.equation i).first ≠ (S.equation i).second ∧
    (S.equation i).first ≠ (S.equation i).third ∧
    (S.equation i).second ≠ (S.equation i).third

abbrev Alphabet (s : Nat) := UniqueGamesTheorem.Integration.BinaryLinear.Vector s
abbrev Ambient (s d : Nat) := Alphabet s × UniqueGamesTheorem.Integration.BinaryLinear.Vector d

def alphabetEmbedding (s d : Nat) : Alphabet s →ₗ[F2] Ambient s d :=
  LinearMap.inl F2 (Alphabet s) (UniqueGamesTheorem.Integration.BinaryLinear.Vector d)

@[simp] theorem alphabetEmbedding_apply (s d : Nat) (c : Alphabet s) :
    alphabetEmbedding s d c = (c, 0) := rfl

/-- Noise indices retain multiplicity even if several indices have equal vectors. -/
structure SplitGadget (s d : Nat) where
  f : Ambient s d → Alphabet s
  equivariant : ∀ (x : Ambient s d) (c : Alphabet s), f (x + (c, 0)) = f x + c
  NoiseIndex : Type
  noiseFintype : Fintype NoiseIndex
  noiseNonempty : Nonempty NoiseIndex
  noise : NoiseIndex → Ambient s d

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

def SplitGadget.stabilityError {s d : Nat} (g : SplitGadget s d) : ℚ :=
  Finset.univ.expect (fun xv : Ambient s d × g.NoiseIndex =>
    if g.f (xv.1 + g.noise xv.2) = g.f xv.1 then (0 : ℚ) else 1)

def SplitGadget.kernelError {s d p : Nat} (g : SplitGadget s d)
    (S : Ambient s d →ₗ[F2] UniqueGamesTheorem.Integration.BinaryLinear.Vector p) : ℚ :=
  Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

theorem SplitGadget.stabilityError_nonneg {s d : Nat} (g : SplitGadget s d) :
    0 ≤ g.stabilityError := by
  apply Finset.expect_nonneg
  intro x _
  split <;> norm_num

theorem SplitGadget.stabilityError_le_one {s d : Nat} (g : SplitGadget s d) :
    g.stabilityError ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  split <;> norm_num

end UniqueGamesTheorem.Reduction.ActualSource

end

section

/-! Transport of actual gadgets to the split coordinate model used by the reduction. -/

namespace UniqueGamesTheorem.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

/-- Any injective symbol embedding admits finite coordinates in which it is the
first summand. This is a theorem about the actual ambient vector space. -/
theorem exists_split_equiv {s : Nat} (e : Vector s →ₗ[F2] R)
    (he : Function.Injective e) :
    ∃ d : Nat, ∃ φ : R ≃ₗ[F2] (Vector s × Vector d),
      ∀ c, φ (e c) = (c, 0) := by
  obtain ⟨U, hU⟩ := e.range.exists_isCompl
  let er := LinearEquiv.ofInjective e he
  let eu := (Module.finBasis F2 U).equivFun
  let split := e.range.prodEquivOfIsCompl U hU
  refine ⟨Module.finrank F2 U, split.symm.trans (er.symm.prodCongr eu), ?_⟩
  intro c
  change (er.symm.prodCongr eu) (split.symm (e c)) = (c, 0)
  have hc : split.symm (e c) = (er c, 0) :=
    e.range.prodEquivOfIsCompl_symm_apply_left U hU (er c)
  rw [hc]
  simp

open UniqueGamesTheorem.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open UniqueGamesTheorem.Reduction.ActualSource

noncomputable def kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) : ℚ := by
  classical
  exact Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

theorem kernelProbability_eq_kernelError {s d p : Nat} (g : SplitGadget s d)
    (S : Ambient s d →ₗ[F2] Vector p) :
    kernelProbability g S = g.kernelError S := by
  unfold kernelProbability SplitGadget.kernelError
  congr 1
  funext i
  by_cases h : S (g.noise i) = 0 <;> simp_all

/-- Move all ambient vectors through a linear equivalence, retaining the same
noise indices and their multiplicities. -/
noncomputable def transport {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) : SplitGadget s d where
  f x := g.f (φ.symm x)
  equivariant x c := by
    have hc : φ.symm (c, 0) = g.embed c := by rw [← he c]; simp
    rw [map_add, hc]
    exact g.equivariant (φ.symm x) c
  NoiseIndex := g.NoiseIndex
  noiseFintype := g.noiseFintype
  noiseNonempty := g.noiseNonempty
  noise i := φ (g.noise i)

/-- Uniform stability is invariant under the coordinate change. -/
theorem transport_stabilityError {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) :
    (transport g φ he).stabilityError = stabilityError g := by
  classical
  apply Fintype.expect_equiv (φ.symm.toEquiv.prodCongr (Equiv.refl g.NoiseIndex))
  intro x
  simp [transport, failureIndicator, map_add]

/-- Every zero-image probability is invariant under the same coordinate change. -/
theorem transport_kernelError {s d p : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    (S : Ambient s d →ₗ[F2] Vector p) :
    (transport g φ he).kernelError S = kernelError g (S.comp φ.toLinearMap) := by
  unfold SplitGadget.kernelError kernelError Gadget.ActualGadget.kernelIndicator
  congr 1
  funext i
  by_cases h : S (φ (g.noise i)) = 0 <;> simp_all [transport]

/-- The restriction to the symbol space is exactly the same linear map. -/
theorem transport_symbol_map {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    (S.comp φ.toLinearMap).comp g.embed = S.comp (alphabetEmbedding s d) := by
  apply LinearMap.ext
  intro c
  change S (φ (g.embed c)) = S (c, 0)
  rw [he]

theorem transport_kernelProbability {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    kernelProbability (transport g φ he) S =
      kernelError g (S.comp φ.toLinearMap) := by
  rfl

/-- Both numerical gadget guarantees survive the coordinate change. -/
theorem transport_satisfies {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    (transport g φ he).stabilityError ≤ ζ ∧
      ∀ p (S : Ambient s d →ₗ[F2] Vector p),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        (transport g φ he).kernelError S ≤ ν := by
  constructor
  · rw [transport_stabilityError]
    exact hg.1
  · intro p S hS
    rw [transport_kernelError g φ he S]
    apply hg.2 (Vector p) (S.comp φ.toLinearMap)
    rwa [transport_symbol_map g φ he S]

/-- Every actual gadget satisfying the quantitative guarantees has a split
coordinate representative with exactly those guarantees. -/
theorem exists_split_gadget {s : Nat} (g : Data (Vector s))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    ∃ d : Nat, ∃ h : SplitGadget s d,
      h.stabilityError ≤ ζ ∧
      ∀ p (S : Ambient s d →ₗ[F2] Vector p),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        h.kernelError S ≤ ν := by
  obtain ⟨d, φ, he⟩ := exists_split_equiv g.embed g.embed_injective
  exact ⟨d, transport g φ he, transport_satisfies g φ he hg⟩

/-- The coordinate representative preserves dispersion for every target,
including the question spaces used directly by the soundness analysis. -/
theorem exists_split_gadget_general {s : Nat} (g : Data (Vector s))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    ∃ d : Nat, ∃ h : SplitGadget s d,
      h.stabilityError ≤ ζ ∧
      ∀ (P : Type) [AddCommGroup P] [Module F2 P]
        (S : Ambient s d →ₗ[F2] P),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        kernelProbability h S ≤ ν := by
  obtain ⟨d, φ, he⟩ := exists_split_equiv g.embed g.embed_injective
  refine ⟨d, transport g φ he, ?_, ?_⟩
  · rw [transport_stabilityError]
    exact hg.1
  · intro P _ _ S hS
    rw [transport_kernelProbability g φ he S]
    apply hg.2 P (S.comp φ.toLinearMap)
    rwa [transport_symbol_map g φ he S]

end UniqueGamesTheorem.Integration.SplitGadget

end

end OAI
