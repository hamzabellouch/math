import OAI.Combinatorics.BalancedRyser.Local.TupleAlignment
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformConditioning

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem alignedOffsets_supported (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    ∃ o ∈ {o : Fin 4 → Bool → F |
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)},
      o ∈ (PMF.uniformOfFintype (Fin 4 → Bool → F)).support := by
  let o := (alignedOffsetsEquiv d hd σ g c).symm (fun _ => 0)
  exact ⟨o.1, o.2, PMF.mem_support_uniformOfFintype _⟩

theorem alignedOffsets_conditional_law (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}
      (alignedOffsets_supported d hd σ g c) =
    (PMF.uniformOfFintype (Fin 4 → F)).map
      (fun x => ((alignedOffsetsEquiv d hd σ g c).symm x).1) := by
  let : Nonempty {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} :=
    ⟨(alignedOffsetsEquiv d hd σ g c).symm (fun _ => 0)⟩
  let : Nonempty ({o : Fin 4 → Bool → F |
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} : Set (Fin 4 → Bool → F)) :=
    ⟨(alignedOffsetsEquiv d hd σ g c).symm (fun _ => 0)⟩
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype {o : Fin 4 → Bool → F //
    ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).map Subtype.val = _
  have h := uniform_map_equiv (alignedOffsetsEquiv d hd σ g c).symm
  rw [← h, PMF.map_comp]
  rfl

omit [Fintype F] [DecidableEq F] in
theorem alignedOffsets_generated_positions (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (x : Fin 4 → F) (i : Fin 4) :
    tuplePositionEquiv d hd σ ((alignedOffsetsEquiv d hd σ g c).symm x).1 i =
      ((linePointEquiv g c).symm (x i)).1 := by
  change tuplePositionEquiv d hd σ
    ((tuplePositionEquiv d hd σ).symm (fun j => ((linePointEquiv g c).symm (x j)).1)) i = _
  rw [Equiv.apply_symm_apply]

end Balanced.TupleAlignment

end OAI
