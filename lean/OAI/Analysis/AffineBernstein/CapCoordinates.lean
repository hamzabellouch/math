import Mathlib
import OAI.Analysis.AffineBernstein.MatrixConcavity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def equivMatrix {n : ℕ} (B : Space n ≃L[ℝ] Space n) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis B.toLinearEquiv.toLinearMap

lemma toEuclideanCLM_equivMatrix {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (equivMatrix B) = B.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_toMatrix _ _ _

lemma equivMatrix_det_ne {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    (equivMatrix B).det ≠ 0 :=
  isUnit_iff_ne_zero.mp (B.toLinearEquiv.isUnit_det _ _)

lemma equivMatrix_det {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    (equivMatrix B).det = B.toContinuousLinearMap.det :=
  LinearMap.det_toMatrix _ _

def cleGraphPullback {n : ℕ} (u : Space n → ℝ) (B : Space n ≃L[ℝ] Space n)
    (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) (x : Space n) : ℝ :=
  a x+c*u (B x+d)+e

lemma cleGraphPullback_eq {n : ℕ} (u : Space n → ℝ) (B : Space n ≃L[ℝ] Space n)
    (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) :
    cleGraphPullback u B d a c e = affineGraphPullback u (equivMatrix B) d a c e := by
  funext x
  simp only [cleGraphPullback, affineGraphPullback, graphAffineFunction, affineBaseMap,
    toEuclideanCLM_equivMatrix, ContinuousLinearEquiv.coe_coe]

lemma cleGraphPullback_regular {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (B : Space n ≃L[ℝ] Space n) (d : Space n) (a : Space n →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (e : ℝ) :
    IsOpen {x | B x+d ∈ Ω} ∧ ContDiffOn ℝ ∞ (cleGraphPullback u B d a c e)
      {x | B x+d ∈ Ω} ∧
    (∀ x ∈ {x | B x+d ∈ Ω}, (hessian (cleGraphPullback u B d a c e) x).PosDef) ∧
    AffineMaximalOn {x | B x+d ∈ Ω} (cleGraphPullback u B d a c e) := by
  have he : {x | B x+d ∈ Ω} = affineBaseMap (equivMatrix B) d ⁻¹' Ω := by
    ext x
    change (B x+d ∈ Ω) ↔ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (equivMatrix B) x+d ∈ Ω)
    rw [toEuclideanCLM_equivMatrix]
    rfl
  rw [cleGraphPullback_eq,he]
  exact ⟨hΩ.preimage (contDiff_affineBaseMap _ _).continuous,
    contDiffOn_affineGraphPullback hu _ _ _ _ _,
    fun x hx => posDef_hessian_affineGraphPullback hΩ hu hp (equivMatrix_det_ne B) d a hc e hx,
    affineMaximalOn_affineGraphPullback hΩ hu hp hm (equivMatrix_det_ne B) d a hc e⟩

/-- A shear does not change height and straightens an upward vector. -/
def verticalShear {n : ℕ} (p : Space n) : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
  ({ toFun := fun z => (z.1-z.2 • p,z.2)
     invFun := fun z => (z.1+z.2 • p,z.2)
     map_add' := by intro x y; ext <;> simp [add_smul]; abel
     map_smul' := by intro t x; ext <;> simp [smul_sub,smul_smul]
     left_inv := by intro z; ext <;> simp
     right_inv := by intro z; ext <;> simp } :
     (Space n × ℝ) ≃ₗ[ℝ] (Space n × ℝ)).toContinuousLinearEquiv

@[simp] lemma verticalShear_apply {n : ℕ} (p : Space n) (z : Space n × ℝ) :
    verticalShear p z = (z.1-z.2 • p,z.2) := rfl

lemma verticalShear_straightens {n : ℕ} (e : Space n × ℝ) (he : e.2 ≠ 0) :
    verticalShear (e.2⁻¹ • e.1) e = ((0 : Space n),e.2) := by
  simp [smul_smul,he]

lemma vertical_map {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (z : ℝ) : M (0,z) = (0,c*z) := by
  have hp : ((0 : Space n),z) = z • ((0 : Space n),1) := by simp
  rw [hp,map_smul,hc]
  simp [mul_comm]

lemma triangular_fst {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (x : Space n) (t : ℝ) :
    (M (x,t)).1 = (M (x,0)).1 := by
  have he : (x,t) = (x,0)+((0 : Space n),t) := by simp
  rw [he,map_add,vertical_map M hc]
  simp

lemma triangular_snd {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (x : Space n) (t : ℝ) :
    (M (x,t)).2 = (M (x,0)).2+c*t := by
  have he : (x,t) = (x,0)+((0 : Space n),t) := by simp
  rw [he,map_add,vertical_map M hc]
  rfl

lemma triangular_symm_vertical {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) :
    M.symm (0,1) = (0,c⁻¹) := by
  apply M.injective
  rw [M.apply_symm_apply,vertical_map M hc,mul_inv_cancel₀ hcn]

/-- The induced invertible horizontal map of a triangular ambient affine map. -/
def triangularBaseEquiv {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) : Space n ≃L[ℝ] Space n :=
  ({ toFun := fun x => (M (x,0)).1
     invFun := fun y => (M.symm (y,0)).1
     map_add' := by intro x y; simpa using congrArg Prod.fst (M.map_add (x,0) (y,0))
     map_smul' := by intro t x; simpa using congrArg Prod.fst (M.map_smul t (x,0))
     left_inv := by
       intro x
       have h := triangular_fst M.symm (triangular_symm_vertical M hc hcn)
         (M (x,0)).1 (M (x,0)).2
       simpa using h.symm
     right_inv := by
       intro y
       have h := triangular_fst M hc (M.symm (y,0)).1 (M.symm (y,0)).2
       simpa using h.symm } : Space n ≃ₗ[ℝ] Space n).toContinuousLinearEquiv

@[simp] lemma triangularBaseEquiv_apply {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (x : Space n) :
    triangularBaseEquiv M hc hcn x = (M (x,0)).1 := rfl

@[simp] lemma triangularBaseEquiv_symm_apply {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (x : Space n) :
    (triangularBaseEquiv M hc hcn).symm x = (M.symm (x,0)).1 := rfl

end AffineBernstein
end

end OAI
