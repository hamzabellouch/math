import OAI.MeasureTheory.Falconer.Geometry.RootPatchGeometry
import Mathlib.Analysis.Normed.MulAction

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def DyadicSquare.dilate (Q : DyadicSquare) (s : ℝ) : DyadicSquare :=
  ⟨s*Q.x,s*Q.y,s*Q.side⟩

theorem DyadicSquare.dilate_center (Q : DyadicSquare) (s : ℝ) :
    (Q.dilate s).center = s • Q.center := by
  ext i
  fin_cases i <;> simp [dilate,DyadicSquare.center] <;> ring

theorem DyadicSquare.dilate_child (Q : DyadicSquare) (s : ℝ) (i j : Bool) :
    (Q.dilate s).child i j = (Q.child i j).dilate s := by
  cases i <;> cases j <;> unfold dilate child <;> congr 1 <;> simp <;> ring

theorem DyadicSquare.dilate_descendant (Q : DyadicSquare) (s : ℝ) (p : CellPath) :
    (Q.dilate s).descendant p = (Q.descendant p).dilate s := by
  induction p generalizing Q with
  | nil => rfl
  | cons b p ih =>
    simp only [descendant,dilate_child,ih]

theorem DyadicSquare.mem_dilate (Q : DyadicSquare) {s : ℝ} (hs : 0 < s) (x : Plane) :
    s • x ∈ (Q.dilate s).carrier ↔ x ∈ Q.carrier := by
  change s*Q.x ≤ s*x 0 ∧ s*x 0 < s*Q.x+s*Q.side ∧
    s*Q.y ≤ s*x 1 ∧ s*x 1 < s*Q.y+s*Q.side ↔ _
  rw [← mul_add,← mul_add]
  simp only [mul_le_mul_iff_right₀ hs,mul_lt_mul_iff_right₀ hs,DyadicSquare.carrier,mem_ofPred_eq]

theorem DyadicSquare.dilate_carrier_preimage (Q : DyadicSquare) {s : ℝ} (hs : 0 < s) :
    (fun x : Plane => s • x) ⁻¹' (Q.dilate s).carrier = Q.carrier := by
  ext x
  exact Q.mem_dilate hs x

theorem DyadicSquare.dilate_carrier_image (Q : DyadicSquare) {s : ℝ} (hs : 0 < s) :
    (fun x : Plane => s • x) '' Q.carrier = (Q.dilate s).carrier := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (Q.mem_dilate hs y).mpr hy
  · intro hx
    refine ⟨s⁻¹ • x,?_,smul_inv_smul₀ hs.ne' x⟩
    apply (Q.mem_dilate hs (s⁻¹ • x)).mp
    simpa only [smul_inv_smul₀ hs.ne'] using hx

theorem DyadicSquare.dilate_descendant_mass (Q : DyadicSquare) {s : ℝ} (hs : 0 < s)
    (ρ : Measure Plane) (p : CellPath) :
    (ρ.map (fun x : Plane => s • x)) ((Q.dilate s).descendant p).carrier =
      ρ (Q.descendant p).carrier := by
  rw [dilate_descendant,Measure.map_apply (by fun_prop) (DyadicSquare.measurable _),
    dilate_carrier_preimage _ hs]

theorem sourceRadialUnit_dilate {s : ℝ} (hs : 0 < s) (x y : Plane) :
    sourceRadialUnit (s • x) (s • y) = sourceRadialUnit x y := by
  apply Subtype.ext
  change sourceRadialVector (s • x) (s • y) = sourceRadialVector x y
  unfold sourceRadialVector
  by_cases hxy : y = x
  · simp only [hxy,ite_true]
  · have hscaled : s • y ≠ s • x := fun h => hxy (smul_right_injective Plane hs.ne' h)
    rw [ite_eq_right hscaled,ite_eq_right hxy,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hs,
      mul_inv_rev,smul_smul]
    have he : (‖y-x‖⁻¹*s⁻¹)*s = ‖y-x‖⁻¹ := by
      rw [mul_assoc,inv_mul_cancel₀ hs.ne',mul_one]
    rw [he]

theorem sourceParentAxis_dilate (Q P : DyadicSquare) {s : ℝ} (hs : 0 < s) :
    sourceParentAxis (Q.dilate s) (P.dilate s) = sourceParentAxis Q P := by
  rw [sourceParentAxis,Q.dilate_center,P.dilate_center,sourceRadialUnit_dilate hs]
  rfl

theorem rootPatchEnvelope_dilate (x : Plane) (r s : ℝ) :
    (rootPatchEnvelope x r).dilate s = rootPatchEnvelope (s • x) (s*r) := by
  unfold rootPatchEnvelope DyadicSquare.dilate
  congr 1 <;> simp <;> ring

theorem normalized_root_patch_geometry (x y : Plane) (hxy : x ≠ y) :
    let r := dist x y/1000
    let s := 250/dist x y
    let Q := (rootPatchEnvelope x r).dilate s
    let P := (rootPatchEnvelope y r).dilate s
    0 < s ∧ Q.side = 1 ∧ P.side = 1 ∧ dist Q.center P.center = 250 ∧
    (fun z : Plane => s • z) '' closedBall x r ⊆ Q.carrier ∧
    (fun z : Plane => s • z) '' closedBall y r ⊆ P.carrier := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hs : 0 < 250/dist x y := by positivity
  dsimp only
  refine ⟨hs,?_,?_,?_,?_,?_⟩
  · dsimp [DyadicSquare.dilate,rootPatchEnvelope]
    field_simp
    ring
  · dsimp [DyadicSquare.dilate,rootPatchEnvelope]
    field_simp
    ring
  · rw [DyadicSquare.dilate_center,DyadicSquare.dilate_center,
      rootPatchEnvelope_center,rootPatchEnvelope_center,dist_smul₀,Real.norm_eq_abs,abs_of_pos hs]
    field_simp
  · rintro z ⟨w,hw,rfl⟩
    exact (DyadicSquare.mem_dilate _ hs w).mpr (closedBall_subset_rootPatchEnvelope x (by positivity) hw)
  · rintro z ⟨w,hw,rfl⟩
    exact (DyadicSquare.mem_dilate _ hs w).mpr (closedBall_subset_rootPatchEnvelope y (by positivity) hw)

end PlanarFalconer

end OAI
