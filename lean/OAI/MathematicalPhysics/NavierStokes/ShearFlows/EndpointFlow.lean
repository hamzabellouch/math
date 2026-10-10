import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Localization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

def branchNodes (d : Input) (i : Fin d.instructions.length) (X : Plane) (ζ : ℝ) :
    Fin 8 → Space :=
  ![atHeight X (d.codingHeight + ζ),
    atHeight X (d.privateHeight i + ζ),
    atHeight (scalingPoint d.instructions[i] X 1) (d.privateHeight i + ζ),
    atHeight (scalingPoint d.instructions[i] X 2) (d.privateHeight i + ζ),
    atHeight (scalingPoint d.instructions[i] X 3) (d.privateHeight i + ζ),
    atHeight (scalingPoint d.instructions[i] X 4) (d.privateHeight i + ζ),
    atHeight (d.instructions[i].affine X) (d.privateHeight i + ζ),
    atHeight (d.instructions[i].affine X) (d.codingHeight + ζ)]

@[simp] theorem atHeight_add (X Y : Plane) (z w : ℝ) :
    atHeight X z + atHeight Y w = atHeight (X+Y) (z+w) := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem atHeight_smul (c : ℝ) (X : Plane) (z : ℝ) :
    c • atHeight X z = atHeight (c • X) (c*z) := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem horizontal_add (x y : Space) :
    horizontal (x+y) = horizontal x + horizontal y := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem horizontal_smul (c : ℝ) (x : Space) :
    horizontal (c • x) = c • horizontal x := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem horizontal_basis_two : horizontal (basis 2) = 0 := by
  ext j
  fin_cases j <;> rfl

theorem branchNodes_scaling (d : Input) (i : Fin d.instructions.length)
    (X : Plane) (ζ : ℝ) (k : Fin 4) :
    branchNodes d i X ζ (scalingIndex k).castSucc =
      atHeight (scalingPoint d.instructions[i] X k.castSucc) (d.privateHeight i + ζ) ∧
    branchNodes d i X ζ (scalingIndex k).succ =
      atHeight (scalingPoint d.instructions[i] X k.succ) (d.privateHeight i + ζ) := by
  fin_cases k <;> simp [branchNodes, scalingIndex, scalingPoint_initial]

theorem branchNodes_advance {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) {X Y : Plane} (hY : Y ∈ (d.sources i).carrier)
    (hXY : ‖X-Y‖ < (d.tubeRadius : ℝ)) {ζ : ℝ} (hζ : |ζ| < (d.tubeRadius : ℝ))
    (j : Fin 7) :
    branchNodes d i X ζ j.castSucc + d.spatialFields j (branchNodes d i X ζ j.castSucc) =
      branchNodes d i X ζ j.succ := by
  have hζ' : |(d.privateHeight i : ℝ)+ζ-d.privateHeight i| < (d.heightRadius : ℝ) := by
    simpa using hζ.trans (by exact_mod_cast (tubeRadius_bounds hd).2.2.2.1)
  have hs (k : Fin 4) :
      branchNodes d i X ζ (scalingIndex k).castSucc +
        d.spatialFields (scalingIndex k) (branchNodes d i X ζ (scalingIndex k).castSucc) =
        branchNodes d i X ζ (scalingIndex k).succ := by
    rw [(branchNodes_scaling d i X ζ k).1, (branchNodes_scaling d i X ζ k).2]
    have h := spatialFields_scaling_partial hd i hY hXY hζ' k 1
    have hf := scalingStage_finish (b := d.instructions[i]) (hd.factor_pos _ (List.getElem_mem _)).ne'
      (k := k) (X := X)
    simp only [one_smul, hf] at h
    exact h
  fin_cases j
  · change atHeight X (d.codingHeight + ζ) +
      d.spatialFields 0 (atHeight X (d.codingHeight + ζ)) = atHeight X (d.privateHeight i + ζ)
    rw [spatialFields_lift_value hd i hY (hXY.trans (by exact_mod_cast (tubeRadius_bounds hd).1))]
    ext k
    fin_cases k <;> simp [atHeight, basis]
    ring
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · change atHeight (scalingPoint d.instructions[i] X 4) (d.privateHeight i + ζ) +
        d.spatialFields 5 (atHeight (scalingPoint d.instructions[i] X 4) (d.privateHeight i + ζ)) =
      atHeight (d.instructions[i].affine X) (d.privateHeight i + ζ)
    rw [spatialFields_translate_value hd i _ hζ', atHeight_add, add_zero]
    congr 1
    rw [scalingPoint_final, affine_eq_target_add_scaledOffset]
    dsimp [Input.sources, Input.targets]
    abel
  · change atHeight (d.instructions[i].affine X) (d.privateHeight i + ζ) +
        d.spatialFields 6 (atHeight (d.instructions[i].affine X) (d.privateHeight i + ζ)) =
      atHeight (d.instructions[i].affine X) (d.codingHeight + ζ)
    have hF : d.instructions[i].affine Y ∈ (d.targets i).carrier := by
      change d.instructions[i].affine Y ∈ d.instructions[i].target.carrier
      rw [← hd.image_eq d.instructions[i] (List.getElem_mem _)]
      exact mem_image_of_mem _ hY
    have hC : (0 : ℝ) < d.prefixConstant := by exact_mod_cast
      (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (prefixConstant_ge_one d))
    have hclose : ‖d.instructions[i].affine X-d.instructions[i].affine Y‖ < (d.targetRadius : ℝ) :=
      (affine_lipschitz hd (List.getElem_mem _) X Y).trans_lt
        ((mul_lt_mul_of_pos_left hXY hC).trans (by exact_mod_cast (tubeRadius_bounds hd).2.1))
    rw [spatialFields_lower_value hd i hF hclose]
    ext k
    fin_cases k <;> simp [atHeight, basis]
    ring

theorem materialFlow_branchNodes {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (i : Fin d.instructions.length) {X Y : Plane} (hY : Y ∈ (d.sources i).carrier)
    (hXY : ‖X-Y‖ < (d.tubeRadius : ℝ)) {ζ : ℝ} (hζ : |ζ| < (d.tubeRadius : ℝ)) :
    ∀ k : Fin 8, Φ ((k.val : ℝ)/8) (atHeight X (d.codingHeight+ζ)) = branchNodes d i X ζ k := by
  intro k
  induction k using Fin.induction with
  | zero => simpa [branchNodes] using hΦ.initial (atHeight X (d.codingHeight+ζ))
  | succ k ih =>
    have he := materialFlow_block_endpoint hd hΦ k (atHeight X (d.codingHeight+ζ))
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    change Φ (((k.val : ℝ)+1)/8) _ = Φ ((k.val : ℝ)/8) _ +
      d.spatialFields k (Φ ((k.val : ℝ)/8) _) at he
    simp only [Fin.val_castSucc] at ih
    rw [he, ih]
    exact branchNodes_advance hd i hY hXY hζ k

theorem materialFlow_branch_segment {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (i : Fin d.instructions.length) {X Y : Plane} (hY : Y ∈ (d.sources i).carrier)
    (hXY : ‖X-Y‖ < (d.tubeRadius : ℝ)) {ζ : ℝ} (hζ : |ζ| < (d.tubeRadius : ℝ))
    (j : Fin 7) {t : ℝ} (ht : t ∈ Icc (blockStart j) (blockFinish j)) :
    Φ t (atHeight X (d.codingHeight+ζ)) =
      (1-standardSchedule.progress j t) • branchNodes d i X ζ j.castSucc +
        standardSchedule.progress j t • branchNodes d i X ζ j.succ := by
  rw [materialFlow_on_block hd hΦ j _ ht]
  have he := materialFlow_branchNodes hd hΦ i hY hXY hζ j.castSucc
  change Φ (blockStart j) _ = _ at he
  rw [he, ← branchNodes_advance hd i hY hXY hζ j]
  module

theorem realizingVelocity_periodMap {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    {b : Instruction} (hb : b ∈ d.instructions) {x : Space}
    (hx : x ∈ sourceTube b d.codingHeight d.tubeRadius) :
    Φ 1 x = atHeight (b.affine (horizontal x)) (x 2) := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hb
  rcases hx with ⟨Y,hY,hXY,hz⟩
  let idx : Fin d.instructions.length := ⟨i,hi⟩
  have he := materialFlow_branchNodes hd hΦ idx hY hXY hz 7
  have hx' : atHeight (horizontal x) ((d.codingHeight : ℝ)+(x 2-d.codingHeight)) = x := by
    rw [add_sub_cancel, atHeight_reconstruct]
  simp only [hx'] at he
  rw [materialFlow_period_tail hd hΦ x (by norm_num)]
  simpa [branchNodes, idx, add_sub_cancel] using he

end ShearFlows

end

end OAI
