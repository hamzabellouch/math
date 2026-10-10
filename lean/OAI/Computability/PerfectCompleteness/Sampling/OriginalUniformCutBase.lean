import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCut
import OAI.Computability.PerfectCompleteness.Sampling.BucketUniformLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalUniformCutBase

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

@[instance_reducible] def valuesChildrenFintype (C : Type*)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat)
    [hValues : Fintype (C → H slots)] [hChildren : Fintype (ChildArrays rows slots)] :
    Fintype ((C → H slots) × ChildArrays rows slots) :=
  @instFintypeProd (C → H slots) (ChildArrays rows slots) hValues hChildren

attribute [local instance 2000] instFintypeProd

def assembleEquiv
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    ((Fin (rows (n + 1)) → H slots) × ChildArrays rows slots) ≃ Arrays slots rows where
  toFun z := WholeArraySampler.assemble slots rows z.1 z.2
  invFun arrays := (arrays (.inl ()), fun child node => arrays (.inr (child, node)))
  left_inv z := by
    rcases z with ⟨root, children⟩
    rfl
  right_inv arrays := by
    funext node
    rcases node with u | ⟨child, node⟩
    · cases u
      rfl
    · rfl

theorem uniform_assemble_law
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    ((FiniteDistribution.uniform (Fin (rows (n + 1)) → H slots)).product
        (FiniteDistribution.uniform (ChildArrays rows slots))).pushforward
        (fun z => WholeArraySampler.assemble slots rows z.1 z.2) =
      FiniteDistribution.uniform (Arrays slots rows) := by
  rw [WholeCutSampler.uniform_product]
  change (FiniteDistribution.uniform
      ((Fin (rows (n + 1)) → H slots) × ChildArrays rows slots)).pushforward
      (assembleEquiv slots rows) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (assembleEquiv slots rows)

theorem uniform_bucket_assemble_law
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    ((BucketSampler.tapeLaw (rows (n + 1)) (FiniteDistribution.uniform (H slots))).product
        (FiniteDistribution.uniform (ChildArrays rows slots))).pushforward
        (fun z => WholeArraySampler.assemble slots rows
          (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots) z.1) z.2) =
      FiniteDistribution.uniform (Arrays slots rows) := by
  calc
    _ = (((BucketSampler.tapeLaw (rows (n + 1))
        (FiniteDistribution.uniform (H slots))).product
          (FiniteDistribution.uniform (ChildArrays rows slots))).pushforward
          (fun z =>
            (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots) z.1,
              z.2))).pushforward
                (fun z => WholeArraySampler.assemble slots rows z.1 z.2) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((FiniteDistribution.uniform (Fin (rows (n + 1)) → H slots)).product
        (FiniteDistribution.uniform (ChildArrays rows slots))).pushforward
          (fun z => WholeArraySampler.assemble slots rows z.1 z.2) := by
      apply congrArg (fun μ : FiniteDistribution
          ((Fin (rows (n + 1)) → H slots) × ChildArrays rows slots) =>
        μ.pushforward (fun z => WholeArraySampler.assemble slots rows z.1 z.2))
      have h := FiniteDistribution.product_pushforward
        (BucketSampler.tapeLaw (rows (n + 1)) (FiniteDistribution.uniform (H slots)))
        (FiniteDistribution.uniform (ChildArrays rows slots))
        (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots))
        (id : ChildArrays rows slots → ChildArrays rows slots)
      simpa only [id_eq, FiniteDistribution.pushforward_id,
        BucketUniform.uniform_evaluate_law] using h
    _ = _ := uniform_assemble_law slots rows

private theorem uniform_pushforward_reindex {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : A → C) (g : B → C) (h : ∀ x, g (e x) = f x) :
    (FiniteDistribution.uniform A).pushforward f =
      (FiniteDistribution.uniform B).pushforward g := by
  calc
    _ = (FiniteDistribution.uniform A).pushforward (fun x => g (e x)) :=
      congrArg (fun map : A → C => (FiniteDistribution.uniform A).pushforward map)
        (funext (fun x => (h x).symm))
    _ = ((FiniteDistribution.uniform A).pushforward e).pushforward g :=
      (FiniteDistribution.pushforward_comp (FiniteDistribution.uniform A) e g).symm
    _ = (FiniteDistribution.uniform B).pushforward g :=
      congrArg (fun μ : FiniteDistribution B => μ.pushforward g)
        ((FiniteDistribution.transport_eq_pushforward
          (FiniteDistribution.uniform A) e).symm.trans
            (UniformConditioning.uniform_transport e))

private abbrev ReflRecord (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  Unit × ((BucketSampler.Direction (rows (n + 1)) → H slots) × ChildArrays rows slots)

private def reflRecordEquiv (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    OriginalWholeCut.Record rows repeats (.refl (n + 1)) slots ≃ ReflRecord rows slots :=
  Equiv.refl _

private def renderRecord (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (record : ReflRecord rows slots) : Arrays slots rows :=
  WholeArraySampler.assemble slots rows
    (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots) record.2.1) record.2.2

private theorem renderRecord_equiv (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (.refl (n + 1)) slots) :
    renderRecord rows slots (reflRecordEquiv rows repeats slots record) =
      OriginalWholeCut.reconstructRecord rows repeats (.refl (n + 1)) slots record := rfl

private theorem uniform_renderRecord (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (ReflRecord rows slots)).pushforward (renderRecord rows slots) =
      FiniteDistribution.uniform (Arrays slots rows) := by
  have hdrop : (FiniteDistribution.uniform (ReflRecord rows slots)).pushforward Prod.snd =
      (BucketSampler.tapeLaw (rows (n + 1)) (FiniteDistribution.uniform (H slots))).product
        (FiniteDistribution.uniform (ChildArrays rows slots)) := by
    rw [← WholeCutSampler.uniform_product, FiniteDistribution.product_pushforward_snd]
    rw [BucketSampler.tapeLaw, UniformLinearImage.law_uniform, WholeCutSampler.uniform_product]
  calc
    _ = ((FiniteDistribution.uniform (ReflRecord rows slots)).pushforward Prod.snd).pushforward
        (fun z => WholeArraySampler.assemble slots rows
          (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots) z.1) z.2) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [hdrop]; exact uniform_bucket_assemble_law slots rows

theorem uniform_reconstructRecord_refl (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform
        (OriginalWholeCut.Record rows repeats (.refl (n + 1)) slots)).pushforward
        (OriginalWholeCut.reconstructRecord rows repeats (.refl (n + 1)) slots) =
      FiniteDistribution.uniform (Arrays slots rows) :=
  (uniform_pushforward_reindex
    (A := OriginalWholeCut.Record rows repeats (.refl (n + 1)) slots)
    (B := ReflRecord rows slots) (C := Arrays slots rows)
    (reflRecordEquiv rows repeats slots)
    (OriginalWholeCut.reconstructRecord rows repeats (.refl (n + 1)) slots)
    (renderRecord rows slots) (renderRecord_equiv rows repeats slots)).trans
      (uniform_renderRecord rows slots)

end
end PerfectCompleteness.OriginalUniformCutBase

end

end OAI
