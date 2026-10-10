import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas
import OAI.Computability.PerfectCompleteness.Machines.CanonicalLabelEncoding

namespace OAI

section

namespace PerfectCompleteness.CanonicalCoarseningEncoding

open MixedSupport CanonicalKeys CanonicalEdges

noncomputable section

universe uY uY' uZ uZ'

variable {n : Nat} {Y : Type uY} {Y' : Type uY'} {Z : Type uZ} {Z' : Type uZ'}

theorem fineKernel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) :
    ∀ x x', f x = f x' ↔ (eL ∘ f) x = (eL ∘ f) x' := by
  intro x x'
  exact ⟨fun h => congrArg eL h, fun h => heL h⟩

theorem coarseKernel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y)) :
    ∀ x x', (p ∘ f) x = (p ∘ f) x' ↔
      (p' ∘ (eL ∘ f)) x = (p' ∘ (eL ∘ f)) x' := by
  intro x x'
  change p (f x) = p (f x') ↔ p' (eL (f x)) = p' (eL (f x'))
  rw [commutes (f x), commutes (f x')]
  exact ⟨fun h => congrArg eR h, fun h => heR h⟩

theorem key_fine (side : Side) (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) :
    key side slots (eL ∘ f) = key side slots f :=
  key_postcomp_injective side slots f eL heL

theorem key_coarse (side : Side) (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y)) :
    key side slots (p' ∘ (eL ∘ f)) = key side slots (p ∘ f) :=
  (key_kernel_invariant side slots (p ∘ f) (p' ∘ (eL ∘ f))
    (coarseKernel slots f p eL eR p' heR commutes)).symm

def transportFine (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    Label slots (eL ∘ f) :=
  transportKernel slots f (eL ∘ f) (fineKernel slots f eL heL) P

def transportCoarse (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y))
    (Q : Label slots (p ∘ f)) : Label slots (p' ∘ (eL ∘ f)) :=
  transportKernel slots (p ∘ f) (p' ∘ (eL ∘ f))
    (coarseKernel slots f p eL eR p' heR commutes) Q

@[simp] theorem transportFine_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    (transportFine slots f eL heL P).val = P.val := rfl

@[simp] theorem transportCoarse_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y))
    (Q : Label slots (p ∘ f)) :
    (transportCoarse slots f p eL eR p' heR commutes Q).val = Q.val := rfl

theorem transportFine_bijective (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) :
    Function.Bijective (transportFine slots f eL heL) :=
  transportKernel_bijective slots f (eL ∘ f) (fineKernel slots f eL heL)

theorem restore_transportFine (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    restore slots (eL ∘ f) (transportFine slots f eL heL P) = eL (restore slots f P) :=
  restore_transportKernel slots f (eL ∘ f) (fineKernel slots f eL heL)
    eL (fun _ => rfl) P

theorem restore_transportCoarse (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heR : Function.Injective eR) (commutes : ∀ y, p' (eL y) = eR (p y))
    (Q : Label slots (p ∘ f)) :
    restore slots (p' ∘ (eL ∘ f)) (transportCoarse slots f p eL eR p' heR commutes Q) =
      eR (restore slots (p ∘ f) Q) :=
  restore_transportKernel slots (p ∘ f) (p' ∘ (eL ∘ f))
    (coarseKernel slots f p eL eR p' heR commutes) eR (fun x => commutes (f x)) Q

theorem coarsen_transport (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    transportCoarse slots f p eL eR p' heR commutes (coarsen slots f p P) =
      coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P) := by
  apply restore_injective slots (p' ∘ (eL ∘ f))
  calc
    restore slots (p' ∘ (eL ∘ f))
        (transportCoarse slots f p eL eR p' heR commutes (coarsen slots f p P)) =
        eR (restore slots (p ∘ f) (coarsen slots f p P)) :=
      restore_transportCoarse slots f p eL eR p' heR commutes (coarsen slots f p P)
    _ = eR (p (restore slots f P)) := congrArg eR (restore_coarsen slots f p P)
    _ = p' (eL (restore slots f P)) := (commutes (restore slots f P)).symm
    _ = p' (restore slots (eL ∘ f) (transportFine slots f eL heL P)) :=
      congrArg p' (restore_transportFine slots f eL heL P).symm
    _ = restore slots (p' ∘ (eL ∘ f))
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)) :=
      (restore_coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).symm

theorem coarsen_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    (coarsen slots f p P).val =
      (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).val :=
  congrArg Subtype.val (coarsen_transport slots f p eL eR p' heL heR commutes P)

@[simp] theorem partIndex_transportFine (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (transportFine slots f eL heL P).val =
      CanonicalKeyEncoding.partEnum n P.val := rfl

theorem partIndex_coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (coarsen slots f p P).val =
      CanonicalKeyEncoding.partEnum n
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).val :=
  congrArg (CanonicalKeyEncoding.partEnum n)
    (coarsen_val slots f p eL eR p' heL heR commutes P)

theorem labelIndex_coarsen (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    CanonicalLabelEncoding.labelIndex (key side slots (p ∘ f)) (coarsen slots f p P) =
      CanonicalLabelEncoding.labelIndex (key side slots (p' ∘ (eL ∘ f)))
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)) :=
  partIndex_coarsen slots f p eL eR p' heL heR commutes P

@[simp] theorem labelEmbedding_transportFine {q : Nat} (side : Side)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (slots : Fin n → Slot) (f : Assignment slots → Y)
    (eL : Y → Y') (heL : Function.Injective eL) (P : Label slots f) :
    CanonicalLabelEncoding.labelEmbedding (key side slots (eL ∘ f)) large
        (transportFine slots f eL heL P) =
      CanonicalLabelEncoding.labelEmbedding (key side slots f) large P := rfl

theorem labelEmbedding_coarsen {q : Nat} (side : Side)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (eL : Y → Y') (eR : Z → Z') (p' : Y' → Z')
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    (commutes : ∀ y, p' (eL y) = eR (p y)) (P : Label slots f) :
    CanonicalLabelEncoding.labelEmbedding (key side slots (p ∘ f)) large
        (coarsen slots f p P) =
      CanonicalLabelEncoding.labelEmbedding (key side slots (p' ∘ (eL ∘ f))) large
        (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)) := by
  apply Fin.ext
  change (CanonicalKeyEncoding.partEnum n (coarsen slots f p P).val).val =
    (CanonicalKeyEncoding.partEnum n
      (coarsen slots (eL ∘ f) p' (transportFine slots f eL heL P)).val).val
  exact congrArg (fun i : Fin (CanonicalKeyEncoding.partitionWidth n) => i.val)
    (partIndex_coarsen slots f p eL eR p' heL heR commutes P)

end
end PerfectCompleteness.CanonicalCoarseningEncoding

end

end OAI
