import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchStages
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchOrder

namespace OAI

/-! The eight local pulse endpoints for one filled source rectangle. -/

noncomputable section

namespace ForcedComputation.PlanarRouting

open ShearFlows Set

theorem mem_translationTube_left {R : RationalBox 2} {x : Plane}
    (hx : x ∈ R.carrier) (p : Fin 2 → ℚ) : x ∈ (translationTube R p).carrier := by
  intro j
  have hl : ((translationTube R p).lower j : ℝ) ≤ (R.lower j : ℝ) := by
    exact_mod_cast min_le_left (R.lower j) ((recenter R p).lower j)
  have hu : (R.upper j : ℝ) ≤ ((translationTube R p).upper j : ℝ) := by
    exact_mod_cast le_max_left (R.upper j) ((recenter R p).upper j)
  exact ⟨hl.trans (hx j).1, (hx j).2.trans hu⟩

theorem mem_translationTube_right {R : RationalBox 2} {x : Plane}
    (p : Fin 2 → ℚ) (hx : x ∈ (recenter R p).carrier) :
    x ∈ (translationTube R p).carrier := by
  intro j
  have hl : ((translationTube R p).lower j : ℝ) ≤ ((recenter R p).lower j : ℝ) := by
    exact_mod_cast min_le_right (R.lower j) ((recenter R p).lower j)
  have hu : ((recenter R p).upper j : ℝ) ≤ ((translationTube R p).upper j : ℝ) := by
    exact_mod_cast le_max_right (R.upper j) ((recenter R p).upper j)
  exact ⟨hl.trans (hx j).1, (hx j).2.trans hu⟩

theorem recenter_mem {R : RationalBox 2} {x : Plane} (hx : x ∈ R.carrier)
    (p : Fin 2 → ℚ) :
    x + ((fun j => (p j : ℝ)) - R.center) ∈ (recenter R p).carrier := by
  rw [← recenter_image]
  exact mem_image_of_mem _ hx

theorem recenter_twice (R : RationalBox 2) (p q : Fin 2 → ℚ) :
    recenter (recenter R p) q = recenter R q := by
  apply box_ext
  · funext j
    change q j - halfWidthQ (recenter R p) j = q j - halfWidthQ R j
    rw [recenter_halfWidthQ]
  · funext j
    change q j + halfWidthQ (recenter R p) j = q j + halfWidthQ R j
    rw [recenter_halfWidthQ]

theorem recenter_self (R : RationalBox 2) : recenter R (centerQ R) = R := by
  apply box_ext
  · funext j
    exact centerQ_sub_halfWidthQ R j
  · funext j
    exact centerQ_add_halfWidthQ R j

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian Set

def horizontalPoint (R : RationalBox 2) (p : Fin 2 → ℚ) (x : Plane) : Plane :=
  x + ((fun j => (horizontalCenter R (p 0) j : ℝ)) - R.center)

def branchAnchors (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) : Fin 9 → Plane :=
  let r := instruction M hM b
  let p := parkingFor M hM b
  let ε := parkingScale (geometricBranches M hM).length
  ![x, horizontalPoint r.source p x,
    scaledStage r ε (3 / 8) p x 0,
    scaledStage r ε (3 / 8) p x 1,
    scaledStage r ε (3 / 8) p x 2,
    scaledStage r ε (3 / 8) p x 3,
    scaledStage r ε (3 / 8) p x 4,
    horizontalPoint r.target p (r.affine x), r.affine x]

@[simp] theorem branchAnchors_first (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) : branchAnchors M hM b x 0 = x := rfl

@[simp] theorem branchAnchors_last (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) :
    branchAnchors M hM b x 8 = (instruction M hM b).affine x := rfl

theorem branchAnchors_endpoint (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (x : Plane) (k : Fin 8) :
    (⟨b, ownPhase k⟩ : Action M hM).primitive.endpoint (branchAnchors M hM b x k.castSucc) =
      branchAnchors M hM b x k.succ := by
  have hε := (parkingScale_pos (geometricBranches M hM).length).ne'
  have hμ := (instruction_factor_pos M hM b).ne'
  fin_cases k
  · ext j
    fin_cases j <;>
      simp [Action.primitive, ownPhase, branchAnchors, Primitive.endpoint, Primitive.path,
        translationPath, horizontalPoint, horizontalCenter]
  · change (Primitive.translation ![0, parkingFor M hM b 1 -
        centerQ (instruction M hM b).source 1]).endpoint
        (horizontalPoint (instruction M hM b).source (parkingFor M hM b) x) =
      scaledStage (instruction M hM b) (parkingScale (geometricBranches M hM).length)
        (3 / 8) (parkingFor M hM b) x 0
    rw [scaledStage_zero _ hε (by norm_num)]
    ext j
    fin_cases j <;>
      simp [Primitive.endpoint, Primitive.path,
        translationPath, horizontalPoint, horizontalCenter, parkedSource]
  · exact scaledStage_succ _ hε (by norm_num) hμ _ _ 0
  · exact scaledStage_succ _ hε (by norm_num) hμ _ _ 1
  · exact scaledStage_succ _ hε (by norm_num) hμ _ _ 2
  · exact scaledStage_succ _ hε (by norm_num) hμ _ _ 3
  · change (Primitive.translation ![0, centerQ (instruction M hM b).target 1 -
        parkingFor M hM b 1]).endpoint
        (scaledStage (instruction M hM b) (parkingScale (geometricBranches M hM).length)
          (3 / 8) (parkingFor M hM b) x 4) =
      horizontalPoint (instruction M hM b).target (parkingFor M hM b) ((instruction M hM b).affine x)
    rw [scaledStage_final _ hε (by norm_num)]
    ext j
    fin_cases j <;>
      simp [Primitive.endpoint, Primitive.path, translationPath, horizontalPoint, horizontalCenter]
    ring
  · ext j
    fin_cases j <;>
      simp [Action.primitive, ownPhase, branchAnchors, Primitive.endpoint, Primitive.path,
        translationPath, horizontalPoint, horizontalCenter]
    ring

theorem branchAnchors_mem_rectangle (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 8) :
    branchAnchors M hM b x k.castSucc ∈ (⟨b, ownPhase k⟩ : Action M hM).rectangle.carrier ∧
      branchAnchors M hM b x k.succ ∈ (⟨b, ownPhase k⟩ : Action M hM).rectangle.carrier := by
  let r := instruction M hM b
  let p := parkingFor M hM b
  have ht : r.affine x ∈ r.target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hsh : horizontalPoint r.source p x ∈
      (recenter r.source (horizontalCenter r.source (p 0))).carrier := recenter_mem hx _
  have hsp : parkedSource r p x ∈ (recenter r.source p).carrier := recenter_mem hx p
  have hth : horizontalPoint r.target p (r.affine x) ∈
      (recenter r.target (horizontalCenter r.target (p 0))).carrier := recenter_mem ht _
  have htp : r.affine x + ((fun j => (p j : ℝ)) - r.target.center) ∈
      (recenter r.target p).carrier := recenter_mem ht p
  have hε := (parkingScale_pos (geometricBranches M hM).length).ne'
  have hw := instruction_halfWidths M hM b
  have hp (j : Fin 5) :
      scaledStage r (parkingScale (geometricBranches M hM).length) (3 / 8) p x j ∈
        (parkingBox (geometricBranches M hM).length (bandScale M) (branchIndex M hM b)).carrier :=
    scaledStage_mem_parking (bandScale_pos M).le (branchIndex M hM b) r
      (instruction_factor_pos M hM b) (instruction_image M hM b) hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 hx j
  fin_cases k
  · exact ⟨mem_translationTube_left hx _, mem_translationTube_right _ hsh⟩
  · constructor
    · exact mem_translationTube_left hsh _
    · change scaledStage r _ _ p x 0 ∈ (translationTube (recenter r.source _) p).carrier
      rw [scaledStage_zero r hε (by norm_num)]
      apply mem_translationTube_right
      rw [recenter_twice]
      exact hsp
  · exact ⟨hp 0, hp 1⟩
  · exact ⟨hp 1, hp 2⟩
  · exact ⟨hp 2, hp 3⟩
  · exact ⟨hp 3, hp 4⟩
  · constructor
    · change scaledStage r _ _ p x 4 ∈ (translationTube (recenter r.target p) _).carrier
      rw [scaledStage_final r hε (by norm_num)]
      exact mem_translationTube_left htp _
    · apply mem_translationTube_right
      rw [recenter_twice]
      exact hth
  · constructor
    · exact mem_translationTube_left hth _
    · apply mem_translationTube_right
      rw [recenter_twice, recenter_self]
      exact ht

theorem branch_curve_mem_rectangle (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 8) (t : ℝ) :
    (compiledPulse M hM (branchIndices M hM b k)).curve
        (branchAnchors M hM b x k.castSucc) t ∈
      (compiledPulse M hM (branchIndices M hM b k)).rectangle.carrier := by
  have hm := branchAnchors_mem_rectangle M hM b hx k
  have hθ := smoothRamp_range
    ((compiledPulse M hM (branchIndices M hM b k)).start : ℝ)
    ((compiledPulse M hM (branchIndices M hM b k)).finish : ℝ) t
  change (((actions M hM).get (branchIndices M hM b k)).primitive).path _ _ t ∈
    (((actions M hM).get (branchIndices M hM b k)).rectangle).carrier
  rw [branchIndices_get]
  apply Primitive.path_mem_box
  · exact hm.1
  · rw [branchAnchors_endpoint]
    exact hm.2
  · exact hθ

end ForcedComputation.Recorder.Planar

end

end OAI
