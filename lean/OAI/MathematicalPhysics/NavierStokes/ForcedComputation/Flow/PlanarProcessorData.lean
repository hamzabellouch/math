import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarNeighborhood
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProcessorOrbit

namespace OAI

/-! The explicitly translated finite rational rectangle table used by the
normalized planar processor. -/

noncomputable section
namespace ForcedComputation.PlanarRouting

open ShearFlows Set

def translatedInstruction (v : Fin 2 → ℚ) (r : Instruction) : Instruction :=
  ⟨translatedBox v r.source, translatedBox v r.target, r.factor⟩

theorem translatedBox_image (v : Fin 2 → ℚ) (R : RationalBox 2) :
    translatedPoint v '' R.carrier = (translatedBox v R).carrier := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (mem_translatedBox v R x).mpr hx
  · intro y hy
    let x : Plane := fun j => y j - (v j : ℝ)
    have he : translatedPoint v x = y := by
      funext j
      simp only [translatedPoint, x, sub_add_cancel]
    exact ⟨x, (mem_translatedBox v R x).mp (he.symm ▸ hy), he⟩

theorem translatedInstruction_affine (v : Fin 2 → ℚ) (r : Instruction) (x : Plane) :
    (translatedInstruction v r).affine (translatedPoint v x) =
      translatedPoint v (r.affine x) := by
  ext j
  fin_cases j <;>
    simp [translatedInstruction, Instruction.affine, translatedPoint, translatedBox,
      RationalBox.center] <;> ring

theorem translatedInstruction_image (v : Fin 2 → ℚ) (r : Instruction)
    (hr : r.affine '' r.source.carrier = r.target.carrier) :
    (translatedInstruction v r).affine '' (translatedInstruction v r).source.carrier =
      (translatedInstruction v r).target.carrier := by
  change (translatedInstruction v r).affine '' (translatedBox v r.source).carrier =
    (translatedBox v r.target).carrier
  calc
    _ = (translatedInstruction v r).affine '' (translatedPoint v '' r.source.carrier) := by
      rw [translatedBox_image]
    _ = (fun x => (translatedInstruction v r).affine (translatedPoint v x)) '' r.source.carrier :=
      Set.image_image _ _ _
    _ = (fun x => translatedPoint v (r.affine x)) '' r.source.carrier := by
      congr 1
      funext x
      exact translatedInstruction_affine v r x
    _ = translatedPoint v '' (r.affine '' r.source.carrier) := (Set.image_image _ _ _).symm
    _ = _ := by rw [hr, translatedBox_image]

theorem translatedBox_separation (v : Fin 2 → ℚ) {R S : RationalBox 2}
    (h : PositivelySeparated R.carrier S.carrier) :
    PositivelySeparated (translatedBox v R).carrier (translatedBox v S).carrier := by
  obtain ⟨ε, hε, hsep⟩ := h
  refine ⟨ε, hε, ?_⟩
  rw [← translatedBox_image, ← translatedBox_image]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have he : ‖translatedPoint v x - translatedPoint v y‖ = ‖x - y‖ := by
    simpa only [dist_eq_norm] using Recorder.Planar.translatedPoint_dist v x y
  rw [he]
  exact hsep x hx y hy

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting Set

def normalizedInstruction (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_wellFormed hI))) : Instruction :=
  translatedInstruction (initialShift (freshInput I) (freshInput_valid hI))
    (instruction (freshMachine I.1) (freshInput_wellFormed hI) b)

def normalizedProgram (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : List Instruction :=
  (geometricBranches (freshMachine I.1) (freshInput_wellFormed hI)).map (normalizedInstruction I hI)

def normalizedNeighborhood (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_wellFormed hI))) : Set Plane :=
  translatedPoint (initialShift (freshInput I) (freshInput_valid hI)) ''
    branchNeighborhood (freshMachine I.1) (freshInput_wellFormed hI) b

theorem normalizedInstruction_mem (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1)) :
    normalizedInstruction I hI b ∈ normalizedProgram I hI := by
  apply List.mem_map.mpr
  refine ⟨b, ?_, rfl⟩
  simpa only [geometricBranches, List.mem_dedup] using mem_compileBranches _ _ b

theorem normalizedInstruction_properties (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1)) :
    (normalizedInstruction I hI b).source.positive ∧
    (normalizedInstruction I hI b).target.positive ∧
    0 < (normalizedInstruction I hI b).factor ∧
    (normalizedInstruction I hI b).affine '' (normalizedInstruction I hI b).source.carrier =
      (normalizedInstruction I hI b).target.carrier := by
  exact ⟨translatedBox_positive _ (instruction_source_positive _ _ b),
    translatedBox_positive _ (instruction_target_positive _ _ b),
    instruction_factor_pos _ _ b, translatedInstruction_image _ _ (instruction_image _ _ b)⟩

theorem normalizedInstruction_separation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    {b c : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1)} (hne : b ≠ c) :
    PositivelySeparated (normalizedInstruction I hI b).source.carrier
      (normalizedInstruction I hI c).source.carrier ∧
    PositivelySeparated (normalizedInstruction I hI b).target.carrier
      (normalizedInstruction I hI c).target.carrier :=
  ⟨translatedBox_separation _ (instruction_source_separation _ _ hne),
    translatedBox_separation _ (instruction_target_separation _ _ hne)⟩

theorem normalizedInstruction_neighborhood (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1)) :
    IsOpen (normalizedNeighborhood I hI b) ∧
    (normalizedInstruction I hI b).source.carrier ⊆ normalizedNeighborhood I hI b := by
  have he : normalizedNeighborhood I hI b =
      (Homeomorph.addRight (fun j => (initialShift (freshInput I) (freshInput_valid hI) j : ℝ))) ''
        branchNeighborhood (freshMachine I.1) (freshInput_valid hI).1 b := rfl
  constructor
  · rw [he]
    exact (Homeomorph.addRight _).isOpenMap _ (branchNeighborhood_open _ _ b)
  · change (translatedBox _ _).carrier ⊆ _
    rw [← translatedBox_image]
    exact Set.image_mono (source_subset_branchNeighborhood _ _ b)

theorem normalizedInstruction_period (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    {y : Plane} (hy : y ∈ normalizedNeighborhood I hI b) :
    Ψ 0 1 y = (normalizedInstruction I hI b).affine y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [normalized_branch_neighborhood_period I hI b hx hΨ]
  exact (translatedInstruction_affine _ _ x).symm

theorem normalizedInstruction_encodes (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hs : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D) :
    ∃ b, normalizedInstruction I hI b ∈ normalizedProgram I hI ∧
      normalizedPoint I hI C ∈ (normalizedInstruction I hI b).source.carrier ∧
      (normalizedInstruction I hI b).affine (normalizedPoint I hI C) = normalizedPoint I hI D := by
  obtain ⟨b, _, _, hx, he⟩ := step_branch hs
  refine ⟨b, normalizedInstruction_mem I hI b, (mem_translatedBox _ _ _).mpr hx, ?_⟩
  change (translatedInstruction (initialShift (freshInput I) (freshInput_valid hI))
    (instruction (freshMachine I.1) (freshInput_valid hI).1 b)).affine
      (translatedPoint (initialShift (freshInput I) (freshInput_valid hI))
        (point (freshMachine I.1) (freshInput_valid hI).1 C)) =
    translatedPoint (initialShift (freshInput I) (freshInput_valid hI))
      (point (freshMachine I.1) (freshInput_valid hI).1 D)
  rw [translatedInstruction_affine, he]

end ForcedComputation.Recorder.Planar

end

end OAI
