import OAI.Combinatorics.BalancedRyser.Probability.GlobalTupleLaw
import OAI.Combinatorics.BalancedRyser.Probability.RootConditioning

namespace OAI

namespace Balanced.TupleAlignment

open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

abbrev OutsideGenerators (T : FourTuple F) :=
  {g : Direction F // g ∉ Set.range T.generator}

noncomputable def globalTupleSplitEquiv (T : FourTuple F)
    (hT : Function.Injective T.generator) :
    MergedPairs F ≃ (Fin 4 → Bool → F) × (OutsideGenerators T → Bool → F) :=
  restrictionEquiv ⟨T.generator,hT⟩

omit [Field F] [Fintype F] in
@[simp] theorem globalTupleSplitEquiv_first (T : FourTuple F)
    (hT : Function.Injective T.generator) (M : MergedPairs F) (i : Fin 4) :
    (globalTupleSplitEquiv T hT M).1 i = M (T.generator i) := rfl

omit [Fintype F] in
theorem tuplePoint_eq_split (T : FourTuple F) (hT : Function.Injective T.generator)
    (M : MergedPairs F) :
    tuplePoint M T = tuplePositionEquiv T.generator (adjacent_ne_of_injective T hT)
      T.side (globalTupleSplitEquiv T hT M).1 := by
  funext i
  simp only [tuplePoint, constituent, tuplePositionEquiv_apply, globalTupleSplitEquiv_first]

private def subtypeFstEquiv {A B : Type*} (p : A → Prop) :
    {z : A × B // p z.1} ≃ {a : A // p a} × B where
  toFun z := (⟨z.1.1,z.2⟩,z.1.2)
  invFun z := ⟨(z.1.1,z.2),z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def globalAlignedOffsetsEquiv (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (c : F) :
    {M : MergedPairs F // ∀ i, OnLine (tuplePoint M T i) (g,c)} ≃
      (Fin 4 → F) × (OutsideGenerators T → Bool → F) :=
  ((globalTupleSplitEquiv T hT).subtypeEquiv (fun M => by
    simp only [tuplePoint_eq_split T hT M])).trans
    ((subtypeFstEquiv (fun o : Fin 4 → Bool → F =>
      ∀ i, OnLine (tuplePositionEquiv T.generator (adjacent_ne_of_injective T hT)
        T.side o i) (g,c))).trans
      (Equiv.prodCongr
        (alignedOffsetsEquiv T.generator (adjacent_ne_of_injective T hT) T.side g c)
        (Equiv.refl _)))

theorem globalAlignedOffsets_supported (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (c : F) :
    ∃ M ∈ {M : MergedPairs F | ∀ i, OnLine (tuplePoint M T i) (g,c)},
      M ∈ (offsetLaw F).support := by
  let M := (globalAlignedOffsetsEquiv T hT g c).symm
    ((fun _ => 0), fun _ _ => 0)
  exact ⟨M.1, M.2, by simp [offsetLaw]⟩

theorem globalAlignedOffsets_conditional_law (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (c : F) :
    (offsetLaw F).filter
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}
      (globalAlignedOffsets_supported T hT g c) =
    (PMF.uniformOfFintype ((Fin 4 → F) × (OutsideGenerators T → Bool → F))).map
      (fun x => ((globalAlignedOffsetsEquiv T hT g c).symm x).1) := by
  classical
  let : Nonempty {M : MergedPairs F // ∀ i, OnLine (tuplePoint M T i) (g,c)} :=
    ⟨(globalAlignedOffsetsEquiv T hT g c).symm ((fun _ => 0), fun _ _ => 0)⟩
  let : Nonempty ({M : MergedPairs F | ∀ i, OnLine (tuplePoint M T i) (g,c)} : Set (MergedPairs F)) :=
    ⟨(globalAlignedOffsetsEquiv T hT g c).symm ((fun _ => 0), fun _ _ => 0)⟩
  simp only [offsetLaw]
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype {M : MergedPairs F //
    ∀ i, OnLine (tuplePoint M T i) (g,c)}).map Subtype.val = _
  have h := uniform_map_equiv (globalAlignedOffsetsEquiv T hT g c).symm
  rw [← h, PMF.map_comp]
  rfl

omit [Fintype F] in
theorem globalAlignedOffsets_generated_outside (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (c : F)
    (x : (Fin 4 → F) × (OutsideGenerators T → Bool → F)) (d : OutsideGenerators T) :
    ((globalAlignedOffsetsEquiv T hT g c).symm x).1 d.1 = x.2 d := by
  have h := congrArg (fun z => z.2 d) ((globalAlignedOffsetsEquiv T hT g c).apply_symm_apply x)
  exact h

omit [Fintype F] in
theorem globalAlignedOffsets_generated_positions (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (c : F)
    (x : (Fin 4 → F) × (OutsideGenerators T → Bool → F)) (i : Fin 4) :
    tuplePoint ((globalAlignedOffsetsEquiv T hT g c).symm x).1 T i =
      ((linePointEquiv g c).symm (x.1 i)).1 := by
  rw [tuplePoint_eq_split T hT]
  change tuplePositionEquiv T.generator (adjacent_ne_of_injective T hT) T.side
    ((globalTupleSplitEquiv T hT)
      ((globalTupleSplitEquiv T hT).symm
        (((alignedOffsetsEquiv T.generator (adjacent_ne_of_injective T hT)
          T.side g c).symm x.1).1, x.2))).1 i = _
  rw [Equiv.apply_symm_apply]
  exact alignedOffsets_generated_positions T.generator (adjacent_ne_of_injective T hT)
    T.side g c x.1 i

end Balanced.TupleAlignment

end OAI
