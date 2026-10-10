import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactSourceInputCorrectness

namespace OAI

/-! The literal coordinate list has the exact final mediator enumeration,
including the original vertices. This identifies the machine output with
the geometric realization without an unproved permutation. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ContactMediator

private theorem siteCount (d : SquareLatticeHeisenberg) :
    d.vertices + d.edges * 2 + d.edges * 2 * 2 + (d.edges * 2 + d.edges * 2 * 2) * 2 =
      d.vertices + d.edges * 2 + d.edges * 4 + d.edges * 4 + d.edges * 8 := by omega

theorem literal_array (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) = List.ofFn (ContactRationalGlobal.position d P ℓ) := by
  rw [literal_blocks]
  conv_rhs =>
    rw [List.ofFn_congr (siteCount d)]
    rw [List.ofFn_add, List.ofFn_add, List.ofFn_add, List.ofFn_add]
  simp only [List.append_assoc]
  refine congrArg₂ List.append ?_ (congrArg₂ List.append ?_
    (congrArg₂ List.append ?_ (congrArg₂ List.append ?_ ?_)))
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (siteEquiv d.vertices d.edges (Sum.inl i)).val = i.val
    simp [siteEquiv, encodeSite, MediatorGraph.old, MediatorGraph.vertexEquiv]
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (firstIndex d i).val = d.vertices + i.val
    exact firstIndex_val d i
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (secondIndex d i).val = d.vertices + d.edges * 2 + i.val
    exact secondIndex_val d i
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (thirdFirstIndex d i).val = d.vertices + d.edges * 2 + d.edges * 4 + i.val
    simpa only [Nat.mul_assoc] using thirdFirstIndex_val d i
  · apply congrArg List.ofFn
    funext i
    apply congrArg (ContactRationalGlobal.position d P ℓ)
    apply Fin.ext
    change (thirdSecondIndex d i).val =
      d.vertices + d.edges * 2 + d.edges * 4 + d.edges * 4 + i.val
    simpa only [Nat.mul_assoc] using thirdSecondIndex_val d i

end ContinuumCoulomb.ContactGeometryBlockProgram

namespace ContinuumCoulomb.ContactSourceInputProgram
open ContactMediator

theorem literal_array (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) = List.ofFn (ContactRationalGlobal.position d P ℓ) := by
  rw [literal_positions, ContactGeometryBlockProgram.literal_array]

theorem scaled_literal_array (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) :
    scaledPositions (q, literalInput d P ℓ) =
      List.ofFn (fun x => (q * (ContactRationalGlobal.position d P ℓ x).1,
        q * (ContactRationalGlobal.position d P ℓ x).2)) := by
  simp only [scaledPositions, literal_array, List.map_ofFn, Function.comp_def]

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
