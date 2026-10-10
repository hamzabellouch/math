import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.CutMatrix

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V]

lemma quad_smul_vec (M : Matrix V V ℝ) (x : V → ℝ) (t : ℝ) :
    quad M (t • x)=t^2*quad M x := by
  simp only [quad,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

lemma quad_smul_matrix (M : Matrix V V ℝ) (x : V → ℝ) (t : ℝ) :
    quad (t • M) x=t*quad M x := by
  simp only [quad,smul_mulVec,dotProduct_smul,smul_eq_mul]

lemma quad_perturb (M : Matrix V V ℝ) (hM : M.PosSemidef) (x e : V → ℝ)
    (δ : ℝ) (hδ : 0<δ) (hx : quad M x≤1) (he : quad M e≤δ^2) :
    quad M (x+e)≤(1+δ)^2 := by
  let b := x ⬝ᵥ (M *ᵥ e)
  have hh := quad_nonneg M hM (e+(-δ) • x)
  rw [quad_add_scaled M hM.isHermitian] at hh
  change 0≤quad M e+2*(-δ)*b+(-δ)^2*quad M x at hh
  have hqx := mul_le_mul_of_nonneg_left hx (sq_nonneg δ)
  have hb : b≤δ := by nlinarith
  have hform := quad_add_scaled M hM.isHermitian x e 1
  simp only [one_smul,one_pow,one_mul,mul_one] at hform
  rw [bilinear_symm M hM.isHermitian e x] at hform
  change quad M (x+e)=quad M x+2*b+quad M e at hform
  nlinarith

lemma quad_cut_unit (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (u : V → ℝ)
    (hu : quad M u=1) : quad (cutMatrix d M u) u=(d+1)^2/d^2 := by
  have hd0 : d≠0 := by linarith
  rw [quad_cutMatrix]
  change (d^2-1)/d^2*quad M u+(2*(d+1)/d^2)*(quad M u)^2=_
  rw [hu]
  field_simp
  ring

lemma center_inflation_scalar (d : ℝ) (hd : 1≤d) :
    (1-1/(8*d^2))*(1+1/(32*d^2))^2≤1 := by
  have hd0 : 0<d := by linarith
  have hz : 0<1/(32*d^2) := by positivity
  have he : 1/(8*d^2)=4*(1/(32*d^2)) := by ring
  rw [he]
  nlinarith [sq_nonneg (1/(32*d^2)),pow_nonneg hz.le 3]

lemma approximate_center_contains (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u x : V → ℝ) (hu : quad M u=1) (hx : quad M x≤1)
    (hcut : u ⬝ᵥ (M *ᵥ x)≤0) (ρ : ℝ)
    (hρlo : 1-1/(32*d)≤ρ) (hρhi : ρ≤1) :
    quad ((1-1/(8*d^2)) • cutMatrix d M u) (x+(ρ/(d+1)) • u)≤1 := by
  have hd0 : 0<d := by linarith
  have hdp : d+1≠0 := by linarith
  let δ := 1/(32*d^2)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hlam : 0≤1-1/(8*d^2) := by
    have hh : 1/(8*d^2)≤1 := (div_le_one (by positivity)).mpr (by nlinarith)
    linarith
  let e := ((ρ-1)/(d+1)) • u
  have he : quad (cutMatrix d M u) e≤δ^2 := by
    rw [quad_smul_vec,quad_cut_unit d hd M u hu]
    have heq : ((ρ-1)/(d+1))^2*((d+1)^2/d^2)=((1-ρ)/d)^2 := by
      field_simp
      ring
    rw [heq]
    have hg : 0≤(1-ρ)/d := div_nonneg (by linarith) hd0.le
    have hk : (1-ρ)/d≤δ := by
      apply (div_le_iff₀ hd0).mpr
      have hi : δ*d=1/(32*d) := by dsimp [δ]; field_simp
      rw [hi]
      linarith
    nlinarith
  have hq := quad_perturb (cutMatrix d M u) (cutMatrix_pos d hd M hM u).posSemidef
    (x+(1/(d+1)) • u) e δ hδ (matrix_cut_contains d hd M hM u x hu hx hcut) he
  have hid : x+(ρ/(d+1)) • u=(x+(1/(d+1)) • u)+e := by
    dsimp [e]
    rw [add_assoc,←add_smul]
    congr 2
    ring
  rw [hid,quad_smul_matrix]
  exact (mul_le_mul_of_nonneg_left hq hlam).trans (center_inflation_scalar d hd.le)

end

open Matrix
open scoped Matrix MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma det_ge_one (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (hbound : (M-1).PosSemidef) : 1≤M.det := by
  have he (i : V) : 1≤hM.eigenvalues i := by
    let v := hM.eigenvectorBasis i
    have hv : star (v : V → ℝ) ⬝ᵥ (v : V → ℝ)=1 := by
      rw [dotProduct_comm,←EuclideanSpace.inner_eq_star_dotProduct,inner_self_eq_norm_sq_to_K]
      simp only [v,hM.eigenvectorBasis.orthonormal.1 i,one_pow,algebraMap.coe_one]
    have hp := hbound.dotProduct_mulVec_nonneg (v : V → ℝ)
    simp only [sub_mulVec,one_mulVec,dotProduct_sub,hv] at hp
    have hval := hM.eigenvalues_eq i
    change hM.eigenvalues i = star (v : V → ℝ) ⬝ᵥ (M *ᵥ (v : V → ℝ)) at hval
    linarith
  rw [hM.det_eq_prod_eigenvalues]
  exact Finset.one_le_prod₀ fun index _ => by simpa using he index

lemma det_mono_posDef (A B : Matrix V V ℝ) (hA : A.PosDef)
    (hBA : (B-A).PosSemidef) : A.det≤B.det := by
  let S : Matrix V V ℝ := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsq : S*S=A := by simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hSd : S.det≠0 := by
    intro he
    have hh := congrArg Matrix.det hsq
    rw [det_mul,he,zero_mul] at hh
    linarith [hA.det_pos]
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSd
  let K := S⁻¹
  have hKherm : K.IsHermitian := hS.inv.isHermitian
  have hconj : K*A*K=1 := by
    rw [←hsq]
    change S⁻¹*(S*S)*S⁻¹=1
    rw [←Matrix.mul_assoc,nonsing_inv_mul _ hSu,one_mul,mul_nonsing_inv _ hSu]
  have hC : (K*B*K-1).PosSemidef := by
    have hh := hBA.mul_mul_conjTranspose_same K
    rw [hKherm.eq,mul_sub,sub_mul,hconj] at hh
    exact hh
  have hCh : (K*B*K).IsHermitian := by
    simpa only [sub_add_cancel] using hC.isHermitian.add (isHermitian_one (n:=V) (α:=ℝ))
  have hd := det_ge_one (K*B*K) hCh hC
  have hone := congrArg Matrix.det hconj
  simp only [det_mul,det_one] at hd hone
  have hK0 : K.det≠0 := by
    change (S⁻¹).det≠0
    rw [det_nonsing_inv]
    exact Ring.isUnit_iff_inverse_ne_zero.mp hSu
  have hp : 0<K.det^2 := sq_pos_of_ne_zero hK0
  have hh : K.det^2*A.det≤K.det^2*B.det := by nlinarith [hd]
  exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_comm] using hh)

end MetricKMedianRecovery.Ellipsoid

end OAI
