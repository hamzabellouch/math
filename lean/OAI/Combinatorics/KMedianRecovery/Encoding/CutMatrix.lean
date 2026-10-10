import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.KindRows

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cutMatrix (d : ℝ) (M : Matrix V V ℝ) (u : V → ℝ) : Matrix V V ℝ :=
  ((d^2-1)/d^2) • M + (2*(d+1)/d^2) • vecMulVec (M *ᵥ u) (M *ᵥ u)

def quad (M : Matrix V V ℝ) (x : V → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

omit [DecidableEq V] in
lemma cutMatrix_pos (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) : (cutMatrix d M u).PosDef := by
  have hα : 0<(d^2-1)/d^2 := div_pos (by nlinarith) (by positivity)
  have hβ : 0≤2*(d+1)/d^2 := by positivity
  have hh : (vecMulVec (M *ᵥ u) (M *ᵥ u)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (M *ᵥ u)
  exact (hM.smul hα).add_posSemidef (hh.smul hβ)

omit [DecidableEq V] in
lemma quad_cutMatrix (d : ℝ) (M : Matrix V V ℝ) (u x : V → ℝ) :
    quad (cutMatrix d M u) x = (d^2-1)/d^2*quad M x+
      (2*(d+1)/d^2)*(x ⬝ᵥ (M *ᵥ u))^2 := by
  simp only [quad,cutMatrix,add_mulVec,smul_mulVec,dotProduct_add,
    dotProduct_smul,vecMulVec_mulVec,op_smul_eq_smul,smul_eq_mul]
  rw [dotProduct_comm (M *ᵥ u) x]
  ring

omit [DecidableEq V] in
lemma bilinear_symm (M : Matrix V V ℝ) (hM : M.IsHermitian) (x y : V → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have ht : Mᵀ=M := (isHermitian_iff_isSymm.mp hM).eq
  simpa only [ht] using dotProduct_transpose_mulVec M x y

omit [DecidableEq V] in
lemma quad_add_scaled (M : Matrix V V ℝ) (hM : M.IsHermitian) (x u : V → ℝ) (t : ℝ) :
    quad M (x+t • u)=quad M x+2*t*(u ⬝ᵥ (M *ᵥ x))+t^2*quad M u := by
  simp only [quad,mulVec_add,mulVec_smul,add_dotProduct,smul_dotProduct,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  rw [bilinear_symm M hM x u]
  ring

omit [DecidableEq V] in
lemma quad_nonneg (M : Matrix V V ℝ) (hM : M.PosSemidef) (x : V → ℝ) : 0≤quad M x := by
  simpa only [star_trivial,quad] using hM.dotProduct_mulVec_nonneg x

omit [DecidableEq V] in

lemma matrix_cut_contains (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u x : V → ℝ) (hu : quad M u=1) (hx : quad M x≤1)
    (hcut : u ⬝ᵥ (M *ᵥ x)≤0) :
    quad (cutMatrix d M u) (x+(1/(d+1)) • u) ≤ 1 := by
  let t := u ⬝ᵥ (M *ᵥ x)
  have ht : -1≤t := by
    have hh := quad_nonneg M hM.posSemidef (x+(-t) • u)
    rw [quad_add_scaled M hM.isHermitian,hu] at hh
    change 0≤quad M x+2*(-t)*t+(-t)^2*1 at hh
    nlinarith
  have hh := scalar_cut_bound d (quad M x) t hd hx hcut ht
  rw [quad_cutMatrix,quad_add_scaled M hM.isHermitian,hu]
  have he : (x+(1/(d+1)) • u) ⬝ᵥ (M *ᵥ u) = t+1/(d+1) := by
    rw [add_dotProduct,smul_dotProduct,bilinear_symm M hM.isHermitian x u]
    change t+(1/(d+1))*quad M u=t+1/(d+1)
    rw [hu,mul_one]
  rw [he]
  convert hh using 1
  ring

lemma rank_one_det (M : Matrix V V ℝ) (hM : M.PosDef) (u : V → ℝ)
    (hu : quad M u=1) (γ : ℝ) :
    (M+γ • vecMulVec (M *ᵥ u) (M *ᵥ u)).det=M.det*(1+γ) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hinv : M⁻¹ *ᵥ (M *ᵥ u)=u := by
    rw [mulVec_mulVec,nonsing_inv_mul _ hunit,one_mulVec]
  rw [←smul_vecMulVec,vecMulVec_eq Unit,det_add_replicateCol_mul_replicateRow hunit]
  congr 1
  rw [det_unique]
  simp only [Matrix.add_apply,one_apply_eq]
  rw [Matrix.mul_assoc,←replicateCol_mulVec,mulVec_smul,hinv,
    replicateRow_mul_replicateCol_apply,dotProduct_smul,smul_eq_mul,
    dotProduct_comm (M *ᵥ u) u]
  change 1+γ*quad M u=1+γ
  rw [hu,mul_one]

lemma cutMatrix_det (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1) :
    (cutMatrix d M u).det = (((d^2-1)/d^2)^(Fintype.card V)*(d+1)/(d-1))*M.det := by
  have hd0 : d≠0 := by linarith
  have hdm : d-1≠0 := by linarith
  have hds : d^2-1≠0 := by nlinarith
  have he : cutMatrix d M u = ((d^2-1)/d^2) •
      (M+(2/(d-1)) • vecMulVec (M *ᵥ u) (M *ᵥ u)) := by
    unfold cutMatrix
    rw [smul_add,smul_smul]
    congr 2
    field_simp
    ring
  rw [he,det_smul,rank_one_det M hM u hu]
  have hc : 1+2/(d-1)=(d+1)/(d-1) := by field_simp; ring
  rw [hc]
  ring

end MetricKMedianRecovery.Ellipsoid

end OAI
