import OAI.MathematicalPhysics.NavierStokes.ShearFlows.StageFlow

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

namespace Input

def prefixConstant (d : Input) : ℚ :=
  (d.instructions.map (fun b => 2*(1+b.factor+b.factor⁻¹))).foldr max 1

def codingRadius (d : Input) : ℚ :=
  letI := neZeroThree
  min (d.codingHeight - d.chart.lower 2) (d.chart.upper 2 - d.codingHeight) / 4

def tubeRadius (d : Input) : ℚ :=
  positiveMinimum [d.sourceRadius, d.targetRadius / d.prefixConstant,
    d.horizontalRadius / d.prefixConstant, d.heightRadius, d.codingRadius] / 2

end Input

theorem prefixConstant_ge_one (d : Input) : 1 ≤ d.prefixConstant := by
  unfold Input.prefixConstant
  generalize d.instructions.map (fun b => 2*(1+b.factor+b.factor⁻¹)) = xs
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

theorem prefixConstant_bound {d : Input} {b : Instruction} (hb : b ∈ d.instructions) :
    prefixBound b.factor ≤ (d.prefixConstant : ℝ) := by
  rw [prefixBound_rational]
  apply Rat.cast_le.mpr
  have hm : (2*(1+b.factor+b.factor⁻¹) : ℚ) ∈
      d.instructions.map (fun b => 2*(1+b.factor+b.factor⁻¹)) := List.mem_map.mpr ⟨b,hb,rfl⟩
  unfold Input.prefixConstant
  generalize d.instructions.map (fun b => 2*(1+b.factor+b.factor⁻¹)) = xs at *
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with h | h
    · exact h.le.trans (le_max_left _ _)
    · exact (ih h).trans (le_max_right _ _)

theorem codingRadius_pos {d : Input} (hd : ValidInput d) : 0 < d.codingRadius := by
  have ha : d.chart.lower 2 < d.codingHeight := by exact_mod_cast hd.height_inside.1
  have hb : d.codingHeight < d.chart.upper 2 := by exact_mod_cast hd.height_inside.2
  exact div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)

theorem tubeRadius_pos {d : Input} (hd : ValidInput d) : 0 < d.tubeRadius := by
  have hC : 0 < d.prefixConstant := lt_of_lt_of_le (by norm_num) (prefixConstant_ge_one d)
  apply div_pos _ (by norm_num : (0 : ℚ) < 2)
  apply positiveMinimum_pos
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact sourceRadius_pos hd
  · exact div_pos (targetRadius_pos hd) hC
  · exact div_pos (horizontalRadius_pos hd) hC
  · exact div_pos (heightSpacing_pos hd) (by norm_num)
  · exact codingRadius_pos hd

theorem tubeRadius_bounds {d : Input} (hd : ValidInput d) :
    d.tubeRadius < d.sourceRadius ∧
    d.prefixConstant * d.tubeRadius < d.targetRadius ∧
    d.prefixConstant * d.tubeRadius < d.horizontalRadius ∧
    d.tubeRadius < d.heightRadius ∧ d.tubeRadius < d.codingRadius := by
  have hδ := tubeRadius_pos hd
  have hC : 0 < d.prefixConstant := lt_of_lt_of_le (by norm_num) (prefixConstant_ge_one d)
  have hle (r : ℚ) (h : r ∈ [d.sourceRadius, d.targetRadius / d.prefixConstant,
      d.horizontalRadius / d.prefixConstant, d.heightRadius, d.codingRadius]) :
      d.tubeRadius < r := by
    have hh := positiveMinimum_le_of_mem h
    change 0 < positiveMinimum _ / 2 at hδ
    change positiveMinimum _ / 2 < r
    linarith
  refine ⟨hle _ (by simp), ?_, ?_, hle _ (by simp), hle _ (by simp)⟩
  · have h := (lt_div_iff₀ hC).mp (hle _ (by simp :
        d.targetRadius / d.prefixConstant ∈ _))
    simpa [mul_comm] using h
  · have h := (lt_div_iff₀ hC).mp (hle _ (by simp :
        d.horizontalRadius / d.prefixConstant ∈ _))
    simpa [mul_comm] using h

def scalingPoint (b : Instruction) (X : Plane) (k : Fin 5) : Plane :=
  b.source.center + scalingEndpoints b.factor (X-b.source.center) k

theorem scalingPoint_initial (b : Instruction) (X : Plane) : scalingPoint b X 0 = X := by
  simp [scalingPoint, scalingEndpoints]

theorem scalingPoint_final (b : Instruction) (X : Plane) :
    scalingPoint b X 4 = b.source.center + scaledOffset b X := rfl

theorem scalingPoint_bound {d : Input} (hd : ValidInput d) {b : Instruction}
    (hb : b ∈ d.instructions) {Y : Plane} (hY : Y ∈ b.source.carrier) (k : Fin 5) :
    ‖scalingPoint b Y k - b.source.center‖ ≤ 2*(d.h : ℝ) := by
  obtain ⟨hr,hs,hmul,hdiv⟩ := instruction_offset_bounds hd hb hY
  simpa only [scalingPoint, add_sub_cancel_left] using scaling_endpoints_bound
    (by exact_mod_cast hd.factor_pos b hb) (by exact_mod_cast hd.h_pos.le)
    (Y-b.source.center) hr hs hmul hdiv k

theorem scalingPoint_lipschitz {d : Input} (hd : ValidInput d) {b : Instruction}
    (hb : b ∈ d.instructions) (X Y : Plane) (k : Fin 5) :
    ‖scalingPoint b X k - scalingPoint b Y k‖ ≤ (d.prefixConstant : ℝ)*‖X-Y‖ := by
  have h := scalingEndpoints_lipschitz (lam := (b.factor : ℝ)) (by exact_mod_cast hd.factor_pos b hb)
    (X-b.source.center) (Y-b.source.center) k
  have hsub : (X-b.source.center)-(Y-b.source.center) = X-Y := by abel
  simp only [scalingPoint, add_sub_add_left_eq_sub]
  rw [hsub] at h
  exact h.trans (mul_le_mul_of_nonneg_right (prefixConstant_bound hb) (norm_nonneg _))

theorem affine_lipschitz {d : Input} (hd : ValidInput d) {b : Instruction}
    (hb : b ∈ d.instructions) (X Y : Plane) :
    ‖b.affine X-b.affine Y‖ ≤ (d.prefixConstant : ℝ)*‖X-Y‖ := by
  have h := scalingPoint_lipschitz hd hb X Y 4
  simpa only [scalingPoint_final, affine_eq_target_add_scaledOffset, add_sub_add_left_eq_sub] using h

theorem scalingPoint_in_plateau {d : Input} (hd : ValidInput d) {b : Instruction}
    (hb : b ∈ d.instructions) {X Y : Plane} (hY : Y ∈ b.source.carrier)
    (hXY : ‖X-Y‖ < (d.tubeRadius : ℝ)) (k : Fin 5) (j : Fin 2) :
    scalingPoint b X k j ∈ Icc (d.horizontalBox.lower j - d.horizontalRadius : ℝ)
      (d.horizontalBox.upper j + d.horizontalRadius : ℝ) := by
  have hC : (0 : ℝ) < d.prefixConstant := by exact_mod_cast
    (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (prefixConstant_ge_one d))
  have hdist : ‖scalingPoint b X k - scalingPoint b Y k‖ < (d.horizontalRadius : ℝ) :=
    (scalingPoint_lipschitz hd hb X Y k).trans_lt
      ((mul_lt_mul_of_pos_left hXY hC).trans (by exact_mod_cast (tubeRadius_bounds hd).2.2.1))
  have hoff := abs_le.mp ((norm_le_pi_norm (scalingPoint b Y k - b.source.center) j).trans
    (scalingPoint_bound hd hb hY k))
  have hclose := abs_lt.mp ((norm_le_pi_norm (scalingPoint b X k - scalingPoint b Y k) j).trans_lt hdist)
  simp only [Pi.sub_apply] at hoff hclose
  have hcenter := hd.source_centers b hb j
  dsimp [Input.horizontalBox, RationalBox.inflate]
  push_cast
  constructor <;> linarith [hcenter.1,hcenter.2]

@[simp] theorem plane_eta (X : Plane) : ![X 0, X 1] = X := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem atHeight_horizontal (X : Plane) (z : ℝ) : horizontal (atHeight X z) = X :=
  plane_eta X

@[simp] theorem atHeight_reconstruct (x : Space) : atHeight (horizontal x) (x 2) = x := by
  ext j
  fin_cases j <;> rfl

theorem spatialFields_lift_value {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) {X Y : Plane} (hY : Y ∈ (d.sources i).carrier)
    (hXY : ‖X-Y‖ < (d.sourceRadius : ℝ)) (z : ℝ) :
    d.spatialFields 0 (atHeight X z) = ((d.privateHeight i : ℝ)-d.codingHeight) • basis 2 := by
  have hm (j) : d.sourceMask j X = if j = i then 1 else 0 := sourceMask_near_box hd i j hY hXY
  simp [Input.spatialFields, sevenFields, transverseSum, selectTwo_apply, atHeight, hm]

theorem spatialFields_lower_value {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) {X Y : Plane} (hY : Y ∈ (d.targets i).carrier)
    (hXY : ‖X-Y‖ < (d.targetRadius : ℝ)) (z : ℝ) :
    d.spatialFields 6 (atHeight X z) = ((d.codingHeight : ℝ)-d.privateHeight i) • basis 2 := by
  have hm (j) : d.targetMask j X = if j = i then 1 else 0 := targetMask_near_box hd i j hY hXY
  simp [Input.spatialFields, sevenFields, transverseSum, selectTwo_apply, atHeight, hm]

def scalingIndex (k : Fin 4) : Fin 7 := ⟨k.val+1, by omega⟩

def scalingVelocity (b : Instruction) (U : Plane) (k : Fin 4) : Space :=
  ![(-(b.factor : ℝ) * (U 0 - b.source.center 0)) • basis 1,
    (((b.factor : ℝ)⁻¹-1) * (U 1 - b.source.center 1)) • basis 0,
    (U 0 - b.source.center 0) • basis 1,
    (((b.factor : ℝ)-1) * (U 1 - b.source.center 1)) • basis 0] k

theorem spatialFields_scaling_value {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) (k : Fin 4) {U : Plane} {z : ℝ}
    (hU : ∀ j, U j ∈ Icc (d.horizontalBox.lower j - d.horizontalRadius : ℝ)
      (d.horizontalBox.upper j + d.horizontalRadius : ℝ))
    (hz : |z - (d.privateHeight i : ℝ)| < (d.heightRadius : ℝ)) :
    d.spatialFields (scalingIndex k) (atHeight U z) = scalingVelocity d.instructions[i] U k := by
  have hZ (j) := heightMask_near_privateHeight hd i j hz
  have hg (j) := horizontalProfile_eq hd i j (hU j)
  fin_cases k <;> simp [Input.spatialFields, sevenFields, scalingIndex, scalingVelocity,
    transverseSum, selectTwo_apply, atHeight, hZ, hg, Input.sources]

theorem spatialFields_scaling_partial {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) {X Y : Plane}
    (hY : Y ∈ (d.sources i).carrier) (hXY : ‖X-Y‖ < (d.tubeRadius : ℝ))
    {z : ℝ} (hz : |z-(d.privateHeight i : ℝ)| < (d.heightRadius : ℝ))
    (k : Fin 4) (θ : ℝ) :
    atHeight (scalingPoint d.instructions[i] X k.castSucc) z + θ •
      d.spatialFields (scalingIndex k) (atHeight (scalingPoint d.instructions[i] X k.castSucc) z) =
        atHeight (scalingStage d.instructions[i] k θ X) z := by
  have hf := spatialFields_scaling_value hd i k
    (scalingPoint_in_plateau hd (b := d.instructions[i]) (List.getElem_mem _) hY hXY k.castSucc) hz
  simp only [Fin.getElem_fin] at hf ⊢
  rw [hf]
  ext m
  fin_cases k <;> fin_cases m <;>
    simp [scalingVelocity, scalingPoint, scalingStage, partialShear, shearX, shearY,
      atHeight, basis, scalingEndpoints] <;> ring

theorem spatialFields_translate_value {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) (U : Plane) {z : ℝ}
    (hz : |z - (d.privateHeight i : ℝ)| < (d.heightRadius : ℝ)) :
    d.spatialFields 5 (atHeight U z) =
      atHeight ((d.targets i).center - (d.sources i).center) 0 := by
  have hZ (j) := heightMask_near_privateHeight hd i j hz
  simp [Input.spatialFields, sevenFields, transverseSum, atHeight, hZ]

theorem sourceTube_in_chart {d : Input} (hd : ValidInput d)
    {b : Instruction} (hb : b ∈ d.instructions) :
    sourceTube b d.codingHeight d.tubeRadius ⊆ d.inChart := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hb
  rintro x ⟨Y,hY,hXY,hz⟩
  have hX := near_box_inside_plateau (d.sources ⟨i,hi⟩) hY
    (hXY.trans (by exact_mod_cast (tubeRadius_bounds hd).1))
  have hc := collar_inside_chart (sourceRadius_pos hd) (⟨i,hi⟩ : Fin d.instructions.length)
  have hr : (0 : ℝ) < d.sourceRadius := by exact_mod_cast sourceRadius_pos hd
  have hhor (j : Fin 2) : (d.chart.lower j.castSucc : ℝ) < x j.castSucc ∧
      x j.castSucc < (d.chart.upper j.castSucc : ℝ) := by
    have hlo : (d.planarLower j : ℝ) < (d.sources ⟨i,hi⟩).lower j - 2*d.sourceRadius := by
      exact_mod_cast (hc j).1
    have hhi : ((d.sources ⟨i,hi⟩).upper j : ℝ) + 2*d.sourceRadius < d.planarUpper j := by
      exact_mod_cast (hc j).2
    have hx := hX j
    have he : horizontal x j = x j.castSucc := by fin_cases j <;> rfl
    rw [he] at hx
    change (d.planarLower j : ℝ) < x j.castSucc ∧ x j.castSucc < d.planarUpper j
    constructor <;> linarith [hx.1,hx.2]
  have hz' : |x 2 - (d.codingHeight : ℝ)| < (d.codingRadius : ℝ) :=
    hz.trans (by exact_mod_cast (tubeRadius_bounds hd).2.2.2.2)
  have ha : (d.codingRadius : ℝ) ≤ ((d.codingHeight : ℝ)-d.chart.lower 2)/4 := by
    dsimp [Input.codingRadius]
    push_cast
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hb : (d.codingRadius : ℝ) ≤ ((d.chart.upper 2 : ℝ)-d.codingHeight)/4 := by
    dsimp [Input.codingRadius]
    push_cast
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  intro j
  fin_cases j
  · exact hhor 0
  · exact hhor 1
  · change (d.chart.lower 2 : ℝ) < x 2 ∧ x 2 < (d.chart.upper 2 : ℝ)
    constructor <;> linarith [(abs_lt.mp hz').1,(abs_lt.mp hz').2,hd.height_inside.1,hd.height_inside.2]

end ShearFlows

end

end OAI
