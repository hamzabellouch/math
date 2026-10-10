import OAI.Geometry.Convex.GeneralMahler.Cone

namespace OAI
/-! Linear transformations in the paper's Cone reduction lemma. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure Real
open scoped ENNReal RealInnerProductSpace
namespace GeneralMahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Linear image, using the inverse so the cone is obviously closed. -/
def pushCone (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) : ProperCone ℝ E :=
  ProperCone.comap (B.symm.toContinuousLinearEquiv : E →L[ℝ] E) C

@[simp] lemma mem_pushCone {C : ProperCone ℝ E} {B : E ≃ₗ[ℝ] E} {x : E} :
    x ∈ pushCone B C ↔ B.symm x ∈ C := Iff.rfl

lemma pushCone_carrier (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) :
    (pushCone B C : Set E) = B '' (C : Set E) := by
  ext x
  obtain ⟨x,rfl⟩ := B.surjective x
  simp [B.injective.eq_iff]

@[simp] lemma apply_mem_interior_pushCone {C : ProperCone ℝ E} {B : E ≃ₗ[ℝ] E} {x : E} :
    B x ∈ interior (pushCone B C : Set E) ↔ x ∈ interior (C : Set E) := by
  let e := B.toContinuousLinearEquiv.toHomeomorph
  rw [pushCone_carrier]
  change e x ∈ interior (e '' (C : Set E)) ↔ _
  rw [← e.image_interior]
  simp

/-- Inverse transpose in Euclidean metric. -/
def contra (B : E ≃ₗ[ℝ] E) : E ≃ₗ[ℝ] E :=
  { LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) with
    invFun := LinearMap.adjoint (B : E →ₗ[ℝ] E)
    left_inv := by
      intro x
      apply ext_inner_left ℝ
      intro y
      change ⟪y, LinearMap.adjoint (B : E →ₗ[ℝ] E) (LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) x)⟫ = _
      rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
      simp
    right_inv := by
      intro x
      apply ext_inner_left ℝ
      intro y
      change ⟪y, LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) (LinearMap.adjoint (B : E →ₗ[ℝ] E) x)⟫ = _
      rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
      simp }

lemma pair_contra (B : E ≃ₗ[ℝ] E) (x y : E) :
    ⟪B x, contra B y⟫ = ⟪x,y⟫ := by
  change ⟪B x, LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) y⟫ = _
  rw [LinearMap.adjoint_inner_right]
  simp

lemma dual_pushCone (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) :
    posDual (pushCone B C) = pushCone (contra B) (posDual C) := by
  ext x
  obtain ⟨q,rfl⟩ := (contra B).surjective x
  rw [mem_pushCone, LinearEquiv.symm_apply_apply, mem_posDual, mem_posDual]
  constructor
  · intro hx y hy
    rw [← pair_contra B]
    exact hx (by simpa using hy)
  · intro hx y hy
    obtain ⟨v,rfl⟩ := B.surjective y
    rw [pair_contra B]
    apply hx (by simpa using hy)

def jac (B : E ≃ₗ[ℝ] E) : ℝ := LinearMap.det (B : E →ₗ[ℝ] E)

omit [FiniteDimensional ℝ E] in
@[simp] lemma jac_ne_zero (B : E ≃ₗ[ℝ] E) : jac B ≠ 0 := by
  rw [jac, ← LinearEquiv.coe_det]
  exact Units.ne_zero _

lemma jac_mul_contra (B : E ≃ₗ[ℝ] E) :
    jac B * jac (contra B) = 1 := by
  let b := stdOrthonormalBasis ℝ E
  have he : jac (contra B) = jac B.symm := by
    change LinearMap.det (LinearMap.adjoint _) = _
    rw [jac, ← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis]
    rw [LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    rfl
  rw [he]; exact LinearEquiv.det_mul_det_symm B

variable [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]

lemma chi_transform' (B D : E ≃ₗ[ℝ] E) (h : ∀ x y, ⟪B x, D y⟫ = ⟪x,y⟫)
    (C : ProperCone ℝ E) (y : E) :
    chi (pushCone B C) (D y) = |jac B| * chi C y := by
  let e := B.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he := setIntegral_map_equiv (μ := volume) e
    (fun x => exp (-⟪x,D y⟫)) (pushCone B C)
  change (∫ x in pushCone B C, exp (-⟪x,D y⟫) ∂ Measure.map (B : E →ₗ[ℝ] E) volume) =
    ∫ x in (⇑B) ⁻¹' (pushCone B C : Set E), exp (-⟪B x,D y⟫) at he
  rw [map_linearMap_addHaar_eq_smul_addHaar _ (jac_ne_zero B), Measure.restrict_smul,
    integral_smul_measure] at he
  have hp : ⇑B ⁻¹' (pushCone B C : Set E) = C := by ext; simp
  rw [hp] at he
  simp_rw [h] at he
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at he
  have hz : chi C y = |jac B|⁻¹ * chi (pushCone B C) (D y) := by
    -- reorder one remaining inner product
    unfold chi
    simpa only [real_inner_comm (D y), real_inner_comm y, jac, abs_inv, smul_eq_mul] using he.symm
  rw [hz, ← mul_assoc, mul_inv_cancel₀ (abs_pos.mpr (jac_ne_zero _)).ne', one_mul]

theorem chi_transform (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) (U V : E) :
    chi (pushCone B C) (contra B V) * chi (posDual (pushCone B C)) (B U) =
      chi C V * chi (posDual C) U := by
  have h : ∀ y x, ⟪contra B y, B x⟫ = ⟪y,x⟫ := by
    intro y x
    rw [real_inner_comm, pair_contra, real_inner_comm]
  rw [dual_pushCone, chi_transform' B _ (pair_contra B), chi_transform' _ B h]
  calc
    _ = |jac B * jac (contra B)| * (chi C V * chi (posDual C) U) := by rw [abs_mul]; ring
    _ = _ := by rw [jac_mul_contra]; simp

end GeneralMahler

end

end OAI
