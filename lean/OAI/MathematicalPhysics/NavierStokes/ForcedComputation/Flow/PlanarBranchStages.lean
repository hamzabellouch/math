import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSchedule

namespace OAI

/-! Eight local stages for one filled instruction rectangle. The four middle
stages use anisotropic shear coordinates, retaining the narrow parking column. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set

theorem Primitive.path_segment (p : Primitive) (x : Plane) (θ : ℝ → ℝ) (t : ℝ) :
    p.path θ x t = x + θ t • (p.endpoint x - x) := by
  cases p <;> ext j <;> fin_cases j <;>
    simp [Primitive.path, Primitive.endpoint, translationPath, horizontalPath, verticalPath,
      shearX, shearY, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem Primitive.path_mem_box (p : Primitive) (x : Plane) (θ : ℝ → ℝ) (t : ℝ)
    {R : RationalBox 2} (hx : x ∈ R.carrier) (hy : p.endpoint x ∈ R.carrier)
    (hθ : θ t ∈ Icc (0 : ℝ) 1) : p.path θ x t ∈ R.carrier := by
  rw [p.path_segment]
  intro j
  have hxj := hx j
  have hyj := hy j
  change (R.lower j : ℝ) ≤ x j + θ t * (p.endpoint x j - x j) ∧
    x j + θ t * (p.endpoint x j - x j) ≤ (R.upper j : ℝ)
  constructor <;> nlinarith [hθ.1, hθ.2]

def anisotropicPrimitive (a b μ : ℚ) (p : Fin 2 → ℚ) : Fin 4 → Primitive :=
  ![.vertical p (-μ * b / a), .horizontal p ((μ⁻¹ - 1) * a / b),
    .vertical p (b / a), .horizontal p ((μ - 1) * a / b)]

theorem anisotropicPrimitive_endpoint {a b μ : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hμ : μ ≠ 0)
    (p : Fin 2 → ℚ) (z : Plane) (k : Fin 4) :
    (anisotropicPrimitive a b μ p k).endpoint
        ((fun j => (p j : ℝ)) + diagonalScale a b z) =
      (fun j => (p j : ℝ)) + diagonalScale a b
        (partialShear μ k 1 z) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hμ' : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ
  fin_cases k <;> ext j <;> fin_cases j <;>
    simp [anisotropicPrimitive, Primitive.endpoint, Primitive.path, verticalPath, horizontalPath,
      diagonalScale, partialShear, shearX, shearY, Rat.cast_inv, Rat.cast_div, Rat.cast_mul,
      Rat.cast_sub, Rat.cast_one, Rat.cast_neg, Matrix.vecHead, Matrix.vecTail] <;>
    try field_simp

def parkedSource (r : Instruction) (p : Fin 2 → ℚ) (x : Plane) : Plane :=
  x + ((fun j => (p j : ℝ)) - r.source.center)

def scaledStage (r : Instruction) (a b : ℚ) (p : Fin 2 → ℚ) (x : Plane) (k : Fin 5) : Plane :=
  (fun j => (p j : ℝ)) + diagonalScale a b
    (scalingEndpoints r.factor (normalizedOffset a b 0 (x - r.source.center)) k)

theorem scaledStage_zero (r : Instruction) {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (p : Fin 2 → ℚ) (x : Plane) : scaledStage r a b p x 0 = parkedSource r p x := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  ext j
  fin_cases j <;>
    simp [scaledStage, parkedSource, scalingEndpoints, normalizedOffset, diagonalScale] <;>
    field_simp <;> ring

theorem scaledStage_final (r : Instruction) {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (p : Fin 2 → ℚ) (x : Plane) : scaledStage r a b p x 4 =
      r.affine x + ((fun j => (p j : ℝ)) - r.target.center) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  ext j
  fin_cases j <;>
    simp [scaledStage, Instruction.affine, scalingEndpoints, normalizedOffset, diagonalScale] <;>
    field_simp <;> ring

theorem scaledStage_succ (r : Instruction) {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hμ : r.factor ≠ 0) (p : Fin 2 → ℚ) (x : Plane) (k : Fin 4) :
    (anisotropicPrimitive a b r.factor p k).endpoint (scaledStage r a b p x k.castSucc) =
      scaledStage r a b p x k.succ := by
  rw [scaledStage, anisotropicPrimitive_endpoint ha hb hμ]
  have he := partial_shear_is_segment (show (r.factor : ℝ) ≠ 0 by exact_mod_cast hμ)
    (normalizedOffset a b 0 (x - r.source.center)) k (1 : ℝ)
  simp only [sub_self, zero_smul, one_smul, zero_add] at he
  rw [he]
  rfl

theorem normalizedOffset_parkedSource (r : Instruction) (a b : ℝ)
    (p : Fin 2 → ℚ) (x : Plane) :
    normalizedOffset a b (fun j => (p j : ℝ)) (parkedSource r p x) =
      normalizedOffset a b 0 (x - r.source.center) := by
  ext j
  fin_cases j <;> simp [normalizedOffset, parkedSource] <;> ring

theorem scaledStage_eq_route_start (r : Instruction) {a b : ℚ}
    (hμ : r.factor ≠ 0) (p : Fin 2 → ℚ) (x : Plane) (k : Fin 4) :
    scaledStage r a b p x k.castSucc =
      anisotropicRoute a b r.factor (fun j => (p j : ℝ)) (parkedSource r p x) (slotStart k) := by
  have hμ' : (r.factor : ℝ) ≠ 0 := by exact_mod_cast hμ
  have ht : (slotStart k : ℝ) ∈ slotRegion k := by
    fin_cases k <;> norm_num [slotStart, slotRegion]
  have hc : slotClock k (slotStart k) = 0 :=
    smoothRamp_before (by exact_mod_cast slot_order k) le_rfl
  rw [anisotropicRoute, normalizedOffset_parkedSource,
    route_eq_stage hμ' 0 _ ht]
  simp only [fourShearPath, hc, sub_zero, partial_shear_is_segment hμ',
    zero_smul, one_smul, zero_add, add_zero]
  rfl

theorem scaledStage_eq_route_final (r : Instruction) {a b : ℚ}
    (hμ : r.factor ≠ 0) (p : Fin 2 → ℚ) (x : Plane) :
    scaledStage r a b p x 4 =
      anisotropicRoute a b r.factor (fun j => (p j : ℝ)) (parkedSource r p x) 1 := by
  have hμ' : (r.factor : ℝ) ≠ 0 := by exact_mod_cast hμ
  rw [anisotropicRoute, normalizedOffset_parkedSource, route_final hμ']
  simp [scaledStage, scalingEndpoints]

theorem scaledStage_mem_parking {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ)
    (i : Fin n) (r : Instruction) (hr : 0 < r.factor)
    (himage : r.affine '' r.source.carrier = r.target.carrier)
    (hsx : r.source.halfWidth 0 ≤ (PlanarRouting.parkingScale n : ℝ) * (κ : ℝ) / 2)
    (htx : r.target.halfWidth 0 ≤ (PlanarRouting.parkingScale n : ℝ) * (κ : ℝ) / 2)
    (hsy : r.source.halfWidth 1 ≤ (3 / 8 : ℝ) * (κ : ℝ) / 2)
    (hty : r.target.halfWidth 1 ≤ (3 / 8 : ℝ) * (κ : ℝ) / 2)
    {x : Plane} (hx : x ∈ r.source.carrier) (k : Fin 5) :
    scaledStage r (PlanarRouting.parkingScale n) (3 / 8) (PlanarRouting.parkingCenter n i) x k ∈
      (PlanarRouting.parkingBox n κ i).carrier := by
  have hroute := PlanarRouting.instruction_scaling_mem_parking hκ i r hr himage hsx htx hsy hty hx
  refine Fin.lastCases ?_ (fun j => ?_) k
  · change scaledStage r (PlanarRouting.parkingScale n) (3 / 8)
      (PlanarRouting.parkingCenter n i) x 4 ∈ _
    rw [scaledStage_eq_route_final r (a := PlanarRouting.parkingScale n) (b := 3 / 8)
      hr.ne' (PlanarRouting.parkingCenter n i) x]
    simpa only [parkedSource, Rat.cast_div, Rat.cast_ofNat] using hroute 1
  · rw [scaledStage_eq_route_start r (a := PlanarRouting.parkingScale n) (b := 3 / 8)
      hr.ne' (PlanarRouting.parkingCenter n i) x j]
    simpa only [parkedSource, Rat.cast_div, Rat.cast_ofNat] using hroute (slotStart j)

end ForcedComputation.PlanarHamiltonian

end

end OAI
