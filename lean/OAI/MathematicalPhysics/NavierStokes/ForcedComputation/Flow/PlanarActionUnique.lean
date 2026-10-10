import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarActionOrder

namespace OAI

/-! Every pulse in the compiler has one owner and one phase. Its explicit
index is the inverse of reading the finite action list. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

theorem blocks_nodup {α β : Type*} {k : ℕ} (l : List α) (f : α → Fin k → β)
    (hl : l.Nodup) (hf : Function.Injective (fun p : α × Fin k => f p.1 p.2)) :
    (blocks l f).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    apply List.nodup_ofFn.mpr
    intro i j hij
    exact congrArg Prod.snd (@hf (a, i) (a, j) hij)
  · apply hl.imp
    intro a b hab x hxa hxb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hxa
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hxb
    exact hab (congrArg Prod.fst (@hf (a, i) (b, j) (hi.trans hj.symm)))

theorem blocks_disjoint {α β γ : Type*} {k m : ℕ} (l : List α) (r : List β)
    (f : α → Fin k → γ) (g : β → Fin m → γ)
    (hfg : ∀ a b i j, f a i ≠ g b j) : List.Disjoint (blocks l f) (blocks r g) := by
  intro x hx hy
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨b, _, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hy
  exact hfg a b i j (hi.trans hj.symm)

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting

theorem extractionBlock_injective (M : Alternating.Machine) (hM : M.WellFormed) :
    Function.Injective (fun p : Branch (finiteMachine M hM) × Fin 2 => extractionBlock p.1 p.2) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  fin_cases i <;> fin_cases j <;>
    simp [extractionBlock] at h
  all_goals (cases h; rfl)

theorem insertionBlock_injective (M : Alternating.Machine) (hM : M.WellFormed) :
    Function.Injective (fun p : Branch (finiteMachine M hM) × Fin 2 => insertionBlock p.1 p.2) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  fin_cases i <;> fin_cases j <;>
    simp [insertionBlock] at h
  all_goals (cases h; rfl)

theorem scalingBlock_injective (M : Alternating.Machine) (hM : M.WellFormed) :
    Function.Injective (fun p : Branch (finiteMachine M hM) × Fin 4 => scalingBlock p.1 p.2) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  have hb := congrArg Action.owner h
  have hi := congrArg Action.phase h
  change Phase.scale i = Phase.scale j at hi
  cases hb
  cases hi
  rfl

theorem actions_nodup (M : Alternating.Machine) (hM : M.WellFormed) : (actions M hM).Nodup := by
  have he := blocks_nodup (sourceOrder M hM) extractionBlock (sourceOrder_nodup M hM)
    (extractionBlock_injective M hM)
  have hs := blocks_nodup (geometricBranches M hM) scalingBlock (List.nodup_dedup _)
    (scalingBlock_injective M hM)
  have hi := blocks_nodup (targetOrder M hM) insertionBlock (targetOrder_nodup M hM)
    (insertionBlock_injective M hM)
  have hes : List.Disjoint (blocks (sourceOrder M hM) extractionBlock)
      (blocks (geometricBranches M hM) scalingBlock) := by
    apply blocks_disjoint
    intro b c i j h
    have hp := congrArg Action.phase h
    fin_cases i <;> cases hp
  have hei : List.Disjoint (blocks (sourceOrder M hM) extractionBlock)
      (blocks (targetOrder M hM) insertionBlock) := by
    apply blocks_disjoint
    intro b c i j h
    have hp := congrArg Action.phase h
    fin_cases i <;> fin_cases j <;> cases hp
  have hsi : List.Disjoint (blocks (geometricBranches M hM) scalingBlock)
      (blocks (targetOrder M hM) insertionBlock) := by
    apply blocks_disjoint
    intro b c i j h
    have hp := congrArg Action.phase h
    fin_cases j <;> cases hp
  rw [actions_eq_blocks]
  apply (he.append hs hes).append hi
  intro a ha hb
  rcases List.mem_append.mp ha with ha | ha
  · exact hei ha hb
  · exact hsi ha hb

theorem Action.get_index {M : Alternating.Machine} {hM : M.WellFormed} (a : Action M hM) :
    (actions M hM).get ⟨a.index, a.index_lt⟩ = a := by
  rcases a with ⟨b, phase⟩
  cases phase with
  | extractHorizontal => exact extractionIndex_get M hM b 0
  | extractVertical => exact extractionIndex_get M hM b 1
  | scale k => exact scalingIndex_get M hM b k
  | insertVertical => exact insertionIndex_get M hM b 0
  | insertHorizontal => exact insertionIndex_get M hM b 1

theorem Action.index_get (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (actions M hM).length) : ((actions M hM).get i).index = i.val := by
  have h := (List.nodup_iff_injective_get.mp (actions_nodup M hM))
    (Action.get_index ((actions M hM).get i))
  exact congrArg Fin.val h

end ForcedComputation.Recorder.Planar

end OAI
