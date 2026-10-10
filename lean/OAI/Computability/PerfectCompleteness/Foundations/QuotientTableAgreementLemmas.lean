import OAI.Computability.PerfectCompleteness.Algebra.MatrixRowQuotientLaw
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys
import OAI.Computability.PerfectCompleteness.Foundations.ClauseSupportLemmas
import OAI.Computability.PerfectCompleteness.Foundations.FiniteRangeInverse
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas

namespace OAI

section

namespace PerfectCompleteness.QuotientTableAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open PartialTableInverse

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {H K Y : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]

def projectedAgreement (W : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Option Y) : ℝ :=
  𝔼 a : {a : K // a ≠ 0}, 𝔼 X : Module.Dual F2 H →ₗ[F2] K, 𝔼 h : H,
    definedEquality f (MatrixRowQuotient.projectMatrix W X)
      (MatrixRowQuotient.projectMatrix W (FiniteRangeInverse.matrixStep X a.val h))

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem projectedAgreement_eq (W : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Option Y) :
    projectedAgreement W f = FiniteRangeInverse.agreement f := by
  unfold projectedAgreement FiniteRangeInverse.agreement
  apply Finset.expect_congr rfl
  intro a _
  exact MatrixRowQuotientLaw.expect_project_rankOne_pair W a.val
    (fun X X' => definedEquality f X X')

omit [FiniteDimensional F2 K] [Fintype Y] in
theorem projectedAgreement_eq_nonzeroAgreement (W : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Option Y) :
    projectedAgreement W f = nonzeroAgreement f := by
  rw [projectedAgreement_eq, FiniteRangeInverse.agreement_eq_nonzeroAgreement]

end
end PerfectCompleteness.QuotientTableAgreement

end

section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {I C Y Z : Type*}

theorem localKey_kernel_invariant (s : Slot)
    (f : C → s.Domain → Y) (g : C → s.Domain → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    localKey s f = localKey s g := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
    change clauseKey occurrence variableIDs f = clauseKey occurrence variableIDs g
    simp only [clauseKey, clauseMode_kernel_invariant f g hkernel]
  | bit variableID =>
    change C → Bool → Y at f
    change C → Bool → Z at g
    change bitKey variableID f = bitKey variableID g
    simp only [bitKey, unused_kernel_invariant f g hkernel]

theorem localReduction_kernel_invariant (s : Slot)
    (f : C → s.Domain → Y) (g : C → s.Domain → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    localReduction s f = localReduction s g := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
    change clauseReduction f = clauseReduction g
    simp only [clauseReduction, clauseMode_kernel_invariant f g hkernel]
  | bit variableID =>
    change C → Bool → Y at f
    change C → Bool → Z at g
    funext b
    change bitReduction f b = bitReduction g b
    simp only [bitReduction, unused_kernel_invariant f g hkernel]

variable [DecidableEq I]

theorem sectionFunction_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (i : I) :
    ∀ context u v,
      sectionFunction slots f i context u = sectionFunction slots f i context v ↔
      sectionFunction slots g i context u = sectionFunction slots g i context v := by
  intro context u v
  exact hkernel (Function.update context i u) (Function.update context i v)

theorem keyFields_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    keyFields slots f = keyFields slots g := by
  funext i
  exact localKey_kernel_invariant (slots i)
    (sectionFunction slots f i) (sectionFunction slots g i)
    (sectionFunction_kernel_invariant slots f g hkernel i)

theorem coordinateReduction_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    coordinateReduction slots f = coordinateReduction slots g := by
  funext i
  exact localReduction_kernel_invariant (slots i)
    (sectionFunction slots f i) (sectionFunction slots g i)
    (sectionFunction_kernel_invariant slots f g hkernel i)

theorem reduction_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    reduction slots f = reduction slots g := by
  unfold reduction
  rw [coordinateReduction_kernel_invariant slots f g hkernel]

theorem retainedKeys_kernel_invariant {n : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    retainedKeys slots f = retainedKeys slots g := by
  simp only [retainedKeys, keyFields_kernel_invariant slots f g hkernel]

end PerfectCompleteness.MixedSupport

namespace PerfectCompleteness.ReducedPartition

variable {X R Y Z : Type*}

theorem fiber_kernel_invariant (r : X → R) (f : X → Y) (g : X → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (x : X) :
    fiber r f x = fiber r g x := by
  ext v
  constructor
  · rintro ⟨z, hz, hfz⟩
    exact ⟨z, hz, (hkernel z x).1 hfz⟩
  · rintro ⟨z, hz, hgz⟩
    exact ⟨z, hz, (hkernel z x).2 hgz⟩

theorem parts_kernel_invariant (r : X → R) (f : X → Y) (g : X → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    parts r f = parts r g := by
  have hfiber : fiber r f = fiber r g :=
    funext (fiber_kernel_invariant r f g hkernel)
  unfold parts
  rw [hfiber]

end PerfectCompleteness.ReducedPartition

namespace PerfectCompleteness.MixedSupport

variable {I Y Z : Type*} [DecidableEq I]

theorem reducedParts_kernel_invariant (slots : I → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    ReducedPartition.parts (reduction slots f) f =
      ReducedPartition.parts (reduction slots g) g := by
  rw [reduction_kernel_invariant slots f g hkernel]
  exact ReducedPartition.parts_kernel_invariant (reduction slots g) f g hkernel

end PerfectCompleteness.MixedSupport

end

section

namespace PerfectCompleteness.CanonicalKeys

open MixedSupport

variable {n : Nat} {Y Z : Type*}

theorem partition_kernel_invariant (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    partition slots f = partition slots g :=
  reducedParts_kernel_invariant slots f g hkernel

theorem key_kernel_invariant (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    key side slots f = key side slots g := by
  simp only [key, retainedKeys_kernel_invariant slots f g hkernel,
    partition_kernel_invariant slots f g hkernel]

theorem key_postcomp_injective (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (e : Y → Z) (he : Function.Injective e) :
    key side slots (e ∘ f) = key side slots f := by
  apply key_kernel_invariant
  intro x x'
  exact ⟨fun h => he h, fun h => congrArg e h⟩

theorem key_postcomp_equiv (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (e : Y ≃ Z) :
    key side slots (e ∘ f) = key side slots f :=
  key_postcomp_injective side slots f e e.injective

noncomputable def transportKernel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (P : Label slots f) :
    Label slots g :=
  ⟨P.val, by
    change P.val ∈ partition slots g
    rw [← partition_kernel_invariant slots f g hkernel]
    exact P.property⟩

theorem transportKernel_bijective (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    Function.Bijective (transportKernel slots f g hkernel) := by
  constructor
  · intro P Q h
    exact Subtype.ext (congrArg (fun R : Label slots g => R.val) h)
  · intro Q
    have hQ : Q.val ∈ partition slots f := by
      rw [partition_kernel_invariant slots f g hkernel]
      exact Q.property
    exact ⟨⟨Q.val, hQ⟩, Subtype.ext rfl⟩

theorem transportKernel_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (x : Assignment slots) :
    transportKernel slots f g hkernel (evaluateLabel slots f x) =
      evaluateLabel slots g x := by
  apply Subtype.ext
  change ReducedPartition.fiber (reduction slots f) f x =
    ReducedPartition.fiber (reduction slots g) g x
  rw [reduction_kernel_invariant slots f g hkernel]
  exact ReducedPartition.fiber_kernel_invariant (reduction slots g) f g hkernel x

theorem restore_transportKernel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (g : Assignment slots → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x')
    (e : Y → Z) (he : ∀ x, g x = e (f x)) (P : Label slots f) :
    restore slots g (transportKernel slots f g hkernel P) = e (restore slots f P) := by
  obtain ⟨x, hx⟩ := ReducedPartition.label_surjective (reduction slots f) f P
  change evaluateLabel slots f x = P at hx
  rw [← hx, transportKernel_evaluateLabel, restore_evaluateLabel, restore_evaluateLabel]
  exact he x

end PerfectCompleteness.CanonicalKeys

end

section

namespace PerfectCompleteness.KeyStrategy

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys

abbrev NonemptyKey (n : Nat) := {k : Key n // k.partition.Nonempty}

abbrev Strategy (n : Nat) :=
  (k : NonemptyKey n) → {P : Set (Fin n → ReducedValue) // P ∈ k.val.partition}

variable {n : Nat} {Y Z : Type*}

def queryKey (side : Side) (slots : Fin n → Slot) (f : Assignment slots → Y) :
    NonemptyKey n :=
  ⟨key side slots f, by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Assignment slots))
    exact ⟨(evaluateLabel slots f x).val, (evaluateLabel slots f x).property⟩⟩

def label (σ : Strategy n) (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Label slots f :=
  σ (queryKey side slots f)

def response (σ : Strategy n) (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Y :=
  restore slots f (label σ side slots f)

theorem response_mem_range (σ : Strategy n) (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : response σ side slots f ∈ Set.range f :=
  ReducedPartition.output_mem_range (reduction slots f) f (label σ side slots f)

theorem label_val_eq_of_key_eq (σ : Strategy n) (side side' : Side)
    (slots projected : Fin n → Slot) (f : Assignment slots → Y)
    (g : Assignment projected → Z) (hkey : key side slots f = key side' projected g) :
    (label σ side slots f).val = (label σ side' projected g).val := by
  have hk : queryKey side slots f = queryKey side' projected g := Subtype.ext hkey
  exact congrArg (fun k : NonemptyKey n => (σ k).val) hk

theorem response_postcomp_injective (σ : Strategy n) (side : Side)
    (slots : Fin n → Slot) (f : Assignment slots → Y) (e : Y → Z)
    (he : Function.Injective e) :
    response σ side slots (e ∘ f) = e (response σ side slots f) := by
  let hkernel : ∀ x x', f x = f x' ↔ (e ∘ f) x = (e ∘ f) x' :=
    fun _ _ => ⟨fun h => congrArg e h, fun h => he h⟩
  have hlabel : label σ side slots (e ∘ f) =
      transportKernel slots f (e ∘ f) hkernel (label σ side slots f) := by
    apply Subtype.ext
    exact label_val_eq_of_key_eq σ side side slots slots (e ∘ f) f
      (key_postcomp_injective side slots f e he)
  unfold response
  rw [hlabel]
  exact restore_transportKernel slots f (e ∘ f) hkernel e (fun _ => rfl)
    (label σ side slots f)

theorem response_projection (σ : Strategy n) (side : Side)
    {slots projected : Fin n → Slot} (p : ∀ i, Projection (slots i) (projected i))
    (f : Assignment projected → Y) :
    response σ side slots (f ∘ projectionMap p) = response σ side projected f := by
  have hlabel : transportLabel p f (label σ side slots (f ∘ projectionMap p)) =
      label σ side projected f := by
    apply Subtype.ext
    exact label_val_eq_of_key_eq σ side side slots projected (f ∘ projectionMap p) f
      (key_projection side p f)
  unfold response
  rw [restore_projection, hlabel]

def extend (vertices : Set (Key n))
    (σ : (k : ↥vertices) → {P : Set (Fin n → ReducedValue) // P ∈ k.val.partition}) :
    Strategy n := fun k =>
  if h : k.val ∈ vertices then σ ⟨k.val, h⟩
  else ⟨Classical.choose k.property, Classical.choose_spec k.property⟩

theorem extend_val (vertices : Set (Key n))
    (σ : (k : ↥vertices) → {P : Set (Fin n → ReducedValue) // P ∈ k.val.partition})
    (k : NonemptyKey n) (hk : k.val ∈ vertices) :
    (extend vertices σ k).val = (σ ⟨k.val, hk⟩).val := by
  simp [extend, hk]

end
end PerfectCompleteness.KeyStrategy

end

end OAI
