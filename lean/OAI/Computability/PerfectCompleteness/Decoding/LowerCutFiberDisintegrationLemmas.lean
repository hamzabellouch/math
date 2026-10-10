import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairBackground
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutFiberDisintegration

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (a : BucketSampler.Direction (rows (m + 1)))

abbrev Scalar := H (cutSlots path slots)
abbrev Quotient := LowerDirectionFiber.Complement a (Scalar path slots)
abbrev Background := LowerCutPairBackground.Complement rows repeats path slots ×
  Quotient rows path slots a
abbrev Coordinates := Background rows repeats path slots a ×
  (Scalar path slots × Scalar path slots)

def coordinateEquiv : LowerCutPairBackground.Observation rows repeats path slots ≃
    Coordinates rows repeats path slots a where
  toFun z := ((z.1, LowerDirectionFiber.complement a z.2.1),
    (z.2.1 (LowerDirectionFiber.pivot a), z.2.2))
  invFun z := (z.1.1, (LowerDirectionFiber.restore a z.1.2 z.2.1, z.2.2))
  left_inv z := by
    change (z.1, (LowerDirectionFiber.restore a
      (LowerDirectionFiber.complement a z.2.1) (z.2.1 (LowerDirectionFiber.pivot a)),
      z.2.2)) = z
    exact Prod.ext rfl (Prod.ext (LowerDirectionFiber.restore_complement a z.2.1) rfl)
  right_inv z := by
    apply Prod.ext
    · exact Prod.ext rfl (LowerDirectionFiber.complement_restore a z.1.2 z.2.1)
    · exact Prod.ext (LowerDirectionFiber.restore_pivot a z.1.2 z.2.1) rfl

@[simp] theorem coordinateEquiv_apply (z : LowerCutPairBackground.Observation rows repeats path slots) :
    coordinateEquiv rows repeats path slots a z =
      ((z.1, LowerDirectionFiber.complement a z.2.1),
        (z.2.1 (LowerDirectionFiber.pivot a), z.2.2)) := rfl

def coordinates (raw : LowerCutPair.Raw rows repeats path slots) :
    Coordinates rows repeats path slots a :=
  coordinateEquiv rows repeats path slots a
    (LowerCutPairBackground.observe rows repeats path slots raw)

def law : FiniteDistribution (Coordinates rows repeats path slots a) :=
  ((FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats path slots)).product
    (FiniteDistribution.uniform (Quotient rows path slots a))).product
      ((FiniteDistribution.uniform (Scalar path slots)).product
        (FiniteDistribution.uniform (Scalar path slots)))

theorem coordinates_law :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats path))
      (cutSlots path slots) rows).pushforward (coordinates rows repeats path slots a) =
      law rows repeats path slots a := by
  change (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats path))
    (cutSlots path slots) rows).pushforward
      (fun raw => coordinateEquiv rows repeats path slots a
        (LowerCutPairBackground.observe rows repeats path slots raw)) = _
  rw [← FiniteDistribution.pushforward_comp,
    LowerCutPairBackground.observe_law]
  have h := UniformConditioning.uniform_transport
    (coordinateEquiv rows repeats path slots a)
  rw [FiniteDistribution.transport_eq_pushforward] at h
  simpa only [law, WholeCutSampler.uniform_product] using h

def arraysAt (exterior : Exterior rows repeats path slots)
    (background : Background rows repeats path slots a) (fresh : Scalar path slots) :
    Arrays slots rows :=
  LowerCutPairBackground.installRows rows repeats path slots exterior background.1
    (LowerDirectionFiber.restore a background.2 fresh)

theorem first_eq_arraysAt (exterior : Exterior rows repeats path slots)
    (raw : LowerCutPair.Raw rows repeats path slots) :
    LowerCutPair.first rows repeats path slots exterior raw =
      arraysAt rows repeats path slots a exterior
        (coordinates rows repeats path slots a raw).1
        (coordinates rows repeats path slots a raw).2.1 := by
  simp only [arraysAt, coordinates, coordinateEquiv_apply, LowerDirectionFiber.restore_complement]
  rw [LowerCutPairBackground.observe_rows rows repeats path slots exterior]
  exact LowerCutPairBackground.first_eq_installRows rows repeats path slots exterior raw

theorem second_eq_arraysAt (exterior : Exterior rows repeats path slots)
    (raw : LowerCutPair.Raw rows repeats path slots) :
    LowerCutPair.second rows repeats path slots exterior a raw =
      arraysAt rows repeats path slots a exterior
        (coordinates rows repeats path slots a raw).1
        (coordinates rows repeats path slots a raw).2.2 := by
  rw [LowerCutPairBackground.second_eq_installRows,
    LowerCutPair.selected_second]
  simp only [arraysAt, coordinates, coordinateEquiv_apply,
    LowerDirectionFiber.replace, LowerCutPairBackground.observe_rows rows repeats path slots exterior,
    LowerCutPairBackground.observe_fresh]

def pair (exterior : Exterior rows repeats path slots)
    (z : Coordinates rows repeats path slots a) : Arrays slots rows × Arrays slots rows :=
  (arraysAt rows repeats path slots a exterior z.1 z.2.1,
    arraysAt rows repeats path slots a exterior z.1 z.2.2)

theorem pair_coordinates (exterior : Exterior rows repeats path slots)
    (raw : LowerCutPair.Raw rows repeats path slots) :
    pair rows repeats path slots a exterior (coordinates rows repeats path slots a raw) =
      LowerCutPair.arraysPair rows repeats path slots exterior a raw :=
  Prod.ext (first_eq_arraysAt rows repeats path slots a exterior raw).symm
    (second_eq_arraysAt rows repeats path slots a exterior raw).symm

theorem arraysPair_law (exterior : Exterior rows repeats path slots) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats path))
      (cutSlots path slots) rows).pushforward
        (LowerCutPair.arraysPair rows repeats path slots exterior a) =
      (law rows repeats path slots a).pushforward (pair rows repeats path slots a exterior) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Coordinates rows repeats path slots a) =>
      μ.pushforward (pair rows repeats path slots a exterior))
    (coordinates_law rows repeats path slots a)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [pair_coordinates] using h

theorem probability_pair (exterior : Exterior rows repeats path slots)
    (event : Arrays slots rows × Arrays slots rows → Bool) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats path))
      (cutSlots path slots) rows).probability
        (fun raw => event (LowerCutPair.arraysPair rows repeats path slots exterior a raw)) =
      (law rows repeats path slots a).probability
        (fun z => event (pair rows repeats path slots a exterior z)) := by
  rw [← FiniteDistribution.probability_pushforward,
    arraysPair_law, FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.LowerCutFiberDisintegration

end

section

namespace PerfectCompleteness.LowerCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

section Linear

variable {H K : Type*} [AddCommGroup H] [AddCommGroup K]
  [Module F2 H] [Module F2 K] {ℓ : Nat}

theorem linearMap_replace (f : H →ₗ[F2] K) (a : BucketSampler.Direction ℓ)
    (S : Fin ℓ → H) (fresh : H) :
    (fun i => f (LowerDirectionFiber.replace a S fresh i)) =
      LowerDirectionFiber.replace a (fun i => f (S i)) (f fresh) := by
  rw [LowerDirectionFiber.replace_eq, LowerDirectionFiber.replace_eq]
  funext i
  simp only [Pi.add_apply, BucketSampler.rankOne, map_add, map_smul, map_sub]

end Linear

section Local

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}

omit [Fintype C] in
theorem original_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (raw : CutCallExtension.Extended (C := C) projected rows) :
    CutCallExtension.original slots rows
        (ChildAssemblyProjection.rawPullback (C := Option C) rows p raw) =
      ChildAssemblyProjection.rawPullback (C := C) rows p
        (CutCallExtension.original projected rows raw) := rfl

omit [Fintype C] in
theorem fresh_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (raw : CutCallExtension.Extended (C := C) projected rows) :
    CutCallExtension.fresh slots rows
        (ChildAssemblyProjection.rawPullback (C := Option C) rows p raw) =
      HPullback p (CutCallExtension.fresh projected rows raw) :=
  ChildAssemblyProjection.recursiveSum_pullback p (fun i => (raw i).1 none)

def observePullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    (CutChildGrouping.Assembled (C := C) projected rows × H projected) →ₗ[F2]
      (CutChildGrouping.Assembled (C := C) slots rows × H slots) :=
  (ChildAssemblyProjection.assembledPullback (C := C) rows p).prodMap (HPullback p)

omit [Fintype C] in
theorem observe_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (raw : CutCallExtension.Extended (C := C) projected rows) :
    CutCallExtension.observe slots rows
        (ChildAssemblyProjection.rawPullback (C := Option C) rows p raw) =
      observePullback rows p (CutCallExtension.observe projected rows raw) := by
  apply Prod.ext
  · change CutChildGrouping.assemble slots rows
      (CutCallExtension.original slots rows
        (ChildAssemblyProjection.rawPullback (C := Option C) rows p raw)) =
      ChildAssemblyProjection.assembledPullback rows p
        (CutChildGrouping.assemble projected rows (CutCallExtension.original projected rows raw))
    rw [original_pullback]
    exact ChildAssemblyProjection.assemble_pullback rows p _
  · exact fresh_pullback rows p raw

theorem pushforward_observe (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (μ : FiniteDistribution (CutCallExtension.Extended (C := C) projected rows)) :
    (μ.pushforward (ChildAssemblyProjection.rawPullback (C := Option C) rows p)).pushforward
        (CutCallExtension.observe slots rows) =
      (μ.pushforward (CutCallExtension.observe projected rows)).pushforward
        (observePullback rows p) := by
  rw [FiniteDistribution.pushforward_comp, FiniteDistribution.pushforward_comp]
  congr 1
  funext raw
  exact observe_pullback rows p raw

theorem uniform_projected_observe (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    ((CutChildGrouping.rawLaw (C := Option C) projected rows).pushforward
        (ChildAssemblyProjection.rawPullback rows p)).pushforward
          (CutCallExtension.observe slots rows) =
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled (C := C) projected rows)).product
        (FiniteDistribution.uniform (H projected))).pushforward (observePullback rows p) := by
  rw [pushforward_observe, CutCallExtension.observe_law]

theorem HPullback_replace {ℓ : Nat}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (a : BucketSampler.Direction ℓ) (S : Fin ℓ → H projected) (fresh : H projected) :
    (fun i => HPullback p (LowerDirectionFiber.replace a S fresh i)) =
      LowerDirectionFiber.replace a (fun i => HPullback p (S i)) (HPullback p fresh) :=
  linearMap_replace (HPullback p) a S fresh

end Local

section Selected

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

theorem firstRows_pullback
    (p : ∀ s k, MixedSupport.Projection
      (WholeCutGrouping.cutSlots path slots s k) (WholeCutGrouping.cutSlots path projected s k))
    (exterior : WholeCutGrouping.Exterior rows repeats path slots)
    (projectedExterior : WholeCutGrouping.Exterior rows repeats path projected)
    (raw : LowerCutPair.Raw rows repeats path projected) :
    SelectedArrayReplacement.selectedRows rows path slots
        (LowerCutPair.first rows repeats path slots exterior
          (ChildAssemblyProjection.rawPullback rows p raw)) =
      (fun i => HPullback p
        (SelectedArrayReplacement.selectedRows rows path projected
          (LowerCutPair.first rows repeats path projected projectedExterior raw) i)) := by
  simp only [LowerCutPair.first, LowerCutRows.selectedRows_reconstruct_eq]
  rw [original_pullback]
  exact congrArg (LowerCutRows.selectRows rows repeats path slots)
    (ChildAssemblyProjection.assemble_pullback rows p
      (CutCallExtension.original (WholeCutGrouping.cutSlots path projected) rows raw))

theorem selectedPair_pullback
    (p : ∀ s k, MixedSupport.Projection
      (WholeCutGrouping.cutSlots path slots s k) (WholeCutGrouping.cutSlots path projected s k))
    (exterior : WholeCutGrouping.Exterior rows repeats path slots)
    (projectedExterior : WholeCutGrouping.Exterior rows repeats path projected)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats path projected) :
    LowerCutPair.selectedPair rows repeats path slots exterior a
        (ChildAssemblyProjection.rawPullback rows p raw) =
      ((fun i => HPullback p
          ((LowerCutPair.selectedPair rows repeats path projected projectedExterior a raw).1 i)),
       (fun i => HPullback p
          ((LowerCutPair.selectedPair rows repeats path projected projectedExterior a raw).2 i))) := by
  simp only [LowerCutPair.selectedPair, LowerCutPair.selected_second]
  apply Prod.ext
  · exact firstRows_pullback rows repeats path p exterior projectedExterior raw
  · rw [firstRows_pullback rows repeats path p exterior projectedExterior raw]
    simp only [LowerCutPair.fresh]
    rw [fresh_pullback]
    exact (HPullback_replace p a _ _).symm

end Selected
end
end PerfectCompleteness.LowerCutProjection

end

section

namespace PerfectCompleteness.LowerCutSingleFiberDisintegration

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (a : BucketSampler.Direction (rows (m + 1)))

abbrev Raw := CutChildGrouping.Raw (C := LowerCutPair.Calls rows repeats path)
  (cutSlots path slots) rows

abbrev Coordinates := LowerCutFiberDisintegration.Background rows repeats path slots a ×
  H (cutSlots path slots)

def coordinateEquiv :
    (LowerCutCallSplit.Complement rows repeats path slots ×
      LowerCutCallSplit.NativeRows rows path slots) ≃
        Coordinates rows repeats path slots a where
  toFun z := ((z.1, LowerDirectionFiber.complement a z.2),
    z.2 (LowerDirectionFiber.pivot a))
  invFun z := (z.1.1, LowerDirectionFiber.restore a z.1.2 z.2)
  left_inv z := Prod.ext rfl (LowerDirectionFiber.restore_complement a z.2)
  right_inv z := Prod.ext
    (Prod.ext rfl (LowerDirectionFiber.complement_restore a z.1.2 z.2))
    (LowerDirectionFiber.restore_pivot a z.1.2 z.2)

@[simp] theorem coordinateEquiv_apply
    (z : LowerCutCallSplit.Complement rows repeats path slots ×
      LowerCutCallSplit.NativeRows rows path slots) :
    coordinateEquiv rows repeats path slots a z =
      ((z.1, LowerDirectionFiber.complement a z.2),
        z.2 (LowerDirectionFiber.pivot a)) := rfl

def coordinates (raw : Raw rows repeats path slots) :
    Coordinates rows repeats path slots a :=
  coordinateEquiv rows repeats path slots a
    (LowerCutCallSplit.splitAssembled rows repeats path slots
      (CutChildGrouping.assemble (cutSlots path slots) rows raw))

@[simp] theorem coordinates_complement (raw : Raw rows repeats path slots) :
    (coordinates rows repeats path slots a raw).1.1 =
      LowerCutCallSplit.complement rows repeats path slots
        (CutChildGrouping.assemble (cutSlots path slots) rows raw) := rfl

theorem coordinates_law :
    (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
      (cutSlots path slots) rows).pushforward (coordinates rows repeats path slots a) =
      ((FiniteDistribution.uniform
        (LowerCutPairBackground.Complement rows repeats path slots)).product
          (FiniteDistribution.uniform
            (LowerCutFiberDisintegration.Quotient rows path slots a))).product
        (FiniteDistribution.uniform (H (cutSlots path slots))) := by
  have hsplit :
      (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
        (cutSlots path slots) rows).pushforward (fun raw =>
          LowerCutCallSplit.splitAssembled rows repeats path slots
            (CutChildGrouping.assemble (cutSlots path slots) rows raw)) =
        FiniteDistribution.uniform
          (LowerCutCallSplit.Complement rows repeats path slots ×
            LowerCutCallSplit.NativeRows rows path slots) := by
    rw [← FiniteDistribution.pushforward_comp, CutChildGrouping.assemble_law]
    exact UniformLinearImage.uniform_pushforward_linearMap
      (LowerCutCallSplit.splitAssembled rows repeats path slots)
      (LowerCutCallSplit.splitAssembled_surjective rows repeats path slots)
  have h := congrArg
    (fun μ : FiniteDistribution
        (LowerCutCallSplit.Complement rows repeats path slots ×
          LowerCutCallSplit.NativeRows rows path slots) =>
      μ.pushforward (coordinateEquiv rows repeats path slots a)) hsplit
  rw [FiniteDistribution.pushforward_comp] at h
  have hcoord := UniformConditioning.uniform_transport
    (coordinateEquiv rows repeats path slots a)
  rw [FiniteDistribution.transport_eq_pushforward] at hcoord
  have hfinal := h.trans hcoord
  change (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
    (cutSlots path slots) rows).pushforward (fun raw =>
      coordinateEquiv rows repeats path slots a
        (LowerCutCallSplit.splitAssembled rows repeats path slots
          (CutChildGrouping.assemble (cutSlots path slots) rows raw))) = _
  calc
    _ = FiniteDistribution.uniform (Coordinates rows repeats path slots a) := hfinal
    _ = _ := by
      apply FiniteDistribution.eq_of_weight_eq
      intro z
      simp only [FiniteDistribution.uniform, FiniteDistribution.product,
        Coordinates, LowerCutFiberDisintegration.Background,
        Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

theorem reconstruct_eq_arraysAt (exterior : Exterior rows repeats path slots)
    (raw : Raw rows repeats path slots) :
    LowerCutRows.reconstruct rows repeats path slots exterior raw =
      LowerCutFiberDisintegration.arraysAt rows repeats path slots a exterior
        (coordinates rows repeats path slots a raw).1
        (coordinates rows repeats path slots a raw).2 := by
  simp only [LowerCutFiberDisintegration.arraysAt, coordinates,
    coordinateEquiv_apply, LowerDirectionFiber.restore_complement]
  rw [← LowerCutAssembled.reconstruct_assemble,
    ← LowerCutPairBackground.reconstruct_merge, LowerCutCallSplit.merge_split]

theorem expectation_fiber (exterior : Exterior rows repeats path slots)
    (f : LowerCutFiberDisintegration.Background rows repeats path slots a →
      Arrays slots rows → ℝ) :
    (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
      (cutSlots path slots) rows).expectation (fun raw =>
        f (coordinates rows repeats path slots a raw).1
          (LowerCutRows.reconstruct rows repeats path slots exterior raw)) =
      (((FiniteDistribution.uniform
        (LowerCutPairBackground.Complement rows repeats path slots)).product
          (FiniteDistribution.uniform
            (LowerCutFiberDisintegration.Quotient rows path slots a))).product
        (FiniteDistribution.uniform (H (cutSlots path slots)))).expectation
          (fun z => f z.1
            (LowerCutFiberDisintegration.arraysAt rows repeats path slots a exterior z.1 z.2)) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Coordinates rows repeats path slots a) =>
      μ.expectation (fun z => f z.1
        (LowerCutFiberDisintegration.arraysAt rows repeats path slots a exterior z.1 z.2)))
    (coordinates_law rows repeats path slots a)
  rw [FiniteDistribution.expectation_pushforward] at h
  simpa only [← reconstruct_eq_arraysAt rows repeats path slots a exterior] using h

theorem probability_fiber (exterior : Exterior rows repeats path slots)
    (event : LowerCutFiberDisintegration.Background rows repeats path slots a →
      Arrays slots rows → Bool) :
    (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
      (cutSlots path slots) rows).probability (fun raw =>
        event (coordinates rows repeats path slots a raw).1
          (LowerCutRows.reconstruct rows repeats path slots exterior raw)) =
      (((FiniteDistribution.uniform
        (LowerCutPairBackground.Complement rows repeats path slots)).product
          (FiniteDistribution.uniform
            (LowerCutFiberDisintegration.Quotient rows path slots a))).product
        (FiniteDistribution.uniform (H (cutSlots path slots)))).probability
          (fun z => event z.1
            (LowerCutFiberDisintegration.arraysAt rows repeats path slots a exterior z.1 z.2)) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Coordinates rows repeats path slots a) =>
      μ.probability (fun z => event z.1
        (LowerCutFiberDisintegration.arraysAt rows repeats path slots a exterior z.1 z.2)))
    (coordinates_law rows repeats path slots a)
  rw [FiniteDistribution.probability_pushforward] at h
  simpa only [← reconstruct_eq_arraysAt rows repeats path slots a exterior] using h

end
end PerfectCompleteness.LowerCutSingleFiberDisintegration

end

end OAI
