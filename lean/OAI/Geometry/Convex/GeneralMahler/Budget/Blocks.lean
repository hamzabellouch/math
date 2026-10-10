import OAI.Geometry.Convex.GeneralMahler.Budget.Segment
import OAI.Geometry.Convex.GeneralMahler.LFun

namespace OAI
/-! Algebra of the positive layer blocks (with no commutation
assumptions). All entries here are in a fixed spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Seg Roots Layers Profile
variable {m:ℕ}
def hsN (A:Mat m) := trN (A*star A)
def ipN (A B:Mat m) := trN (A*star B)
def cmu (A B:Mat m) := A*B-B*A
lemma symm_entry {A:Mat m} (h:A.IsHermitian) (i j) : A i j=A j i := by
  have he:= congrFun (congrFun h i) j; simpa using he.symm
def mats (f:Fin m→ℝ) := (∑ i,f i)/(m:ℝ)
lemma trace_pair (A B:Mat m) : trN (A*B)=mats (fun i=>∑ j,A i j*B j i) := by
  unfold trN trace mats; rfl
lemma traceDiag (A:Mat m) (f:Fin m→ℝ) :
    trN (A*Matrix.diagonal f)=mats (fun i=>A i i*f i) := by
  unfold trN trace mats; simp only [Matrix.diag,Matrix.mul_diagonal]
lemma hsN_eq (A:Mat m) : hsN A=mats (fun i=>∑ j,A i j^2) := by
  rw [hsN,trace_pair]; congr 1; ext; simp [pow_two]
lemma hsN_pos (A:Mat m) : 0 ≤ hsN A := by rw [hsN_eq]; unfold mats; positivity
lemma hsN_loc (A:Mat m) (u:Frm m) : hsN (u.loc A)=hsN A := by
  rw [hsN,hsN,← u.loc_star,← u.loc_mul,trN,trN,u.loc_trace]
lemma Frm.loc_psd (u:Frm m) {A:Mat m} (ha:0≤A):0≤u.loc A := by
  have he := ha.posSemidef.conjTranspose_mul_mul_same u.val
  exact he.nonneg
lemma Frm.loc_le (u:Frm m) {A B:Mat m} (ha:A ≤ B):u.loc A ≤ u.loc B := by
  rw [← sub_nonneg,← u.loc_sub]
  apply u.loc_psd (sub_nonneg.mpr ha)

lemma cmu_eig (A B:Mat m) (u:Frm m) (he:u.Dgn A) :
    hsN (cmu A B)=mats (fun i=>∑ j,(u.eig A i-u.eig A j)^2 * (u.loc B i j)^2) := by
  rw [← hsN_loc (cmu A B) u,hsN_eq]
  unfold cmu
  rw [u.loc_sub,u.loc_mul,u.loc_mul,show u.loc A=_ from he]
  congr 1; ext i; apply Finset.sum_congr rfl; intro j _
  rw [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

lemma mats_add (f g:Fin m→ℝ) :
    mats (fun i=>f i+g i)=mats f+mats g := by unfold mats; rw [Finset.sum_add_distrib,add_div]
lemma mats_s (a:ℝ) (f:Fin m→ℝ) :
    mats (fun i=>a*f i)=a*mats f := by unfold mats; rw [← Finset.mul_sum]; ring
lemma mats_le {f g:Fin m→ℝ} (h:∀ i,f i≤g i) : mats f ≤ mats g := by unfold mats; gcongr; apply h

-- entries in frame of A, eigenvalues x_i
structure block (m:ℕ) where
  x : Fin m→ℝ
  z : ℝ
  P : Mat m
  hp : 0≤P
  hi : P≤1

namespace block
variable (b:block m)
def E : Mat m := b.P-Matrix.diagonal (fun i=>jump b.z (b.x i))
def L (i:Fin m) := signE (b.x i) b.z
def a (i:Fin m) := |b.x i-b.z|
def S : Mat m := Matrix.of fun i j=>rcoef (b.x i) (b.x j) b.z*b.E i j

lemma az (i:Fin m) : b.a i*b.L i=b.x i-b.z := by
  unfold a L signE; split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring
lemma Sspec (i j) :
    b.S i j = (if b.L i=b.L j then b.L i*√(b.a i)*√(b.a j) else 0)*b.E i j := rfl
lemma Ediag (i) : b.E i i=b.P i i-jump b.z (b.x i) := by unfold E; simp
lemma Her : b.E.IsHermitian :=
  b.hp.posSemidef.1.sub (Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl)
lemma Spar : 0≤b.S := by
  let f := fun i=> if b.z<b.x i then √(b.a i) else 0
  let g := fun i=> if b.z<b.x i then 0 else √(b.a i)
  let F := Matrix.diagonal f
  let G := Matrix.diagonal g
  have hp (f:Fin m→ℝ) : (Matrix.diagonal f).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl
  have hi := add_nonneg (sand_nonneg b.hp (hp f)) (sand_nonneg (sub_nonneg.mpr b.hi) (hp g))
  apply hi.trans_eq
  change F*b.P*F+G*(1-b.P)*G=b.S
  ext i j
  unfold F G
  rw [Matrix.add_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.diagonal_mul,b.Sspec]
  unfold f g E jump L signE
  by_cases h:i=j
  · subst j
    rcases lt_or_ge b.z (b.x i) with h|h
    · simp [h,not_le_of_gt h]; ring
    simp [h,not_lt_of_ge h]; ring
  by_cases h₁:b.z<b.x i <;> by_cases h₂:b.z<b.x j <;>
    norm_num [h,h₁,h₂] <;> ring

lemma Sdiag (i) : b.S i i=b.a i*b.L i*b.E i i := by
  rw [b.Sspec,ite_eq_left rfl,mul_assoc (b.L i),← pow_two,Real.sq_sqrt]
  · ring
  exact abs_nonneg _
lemma Ed2 (i) :
    (∑ j,b.E i j^2) ≤ b.L i*b.E i i := by
  have he (A:Mat m) (h:A.IsHermitian) : (∑ j,A i j^2)=(A*A) i i := by
    rw [Matrix.mul_apply]; congr 1; ext j; rw [symm_entry h i j, pow_two]
  rw [he b.E b.Her,E,sub_mul,mul_sub,mul_sub]
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.diagonal_apply_eq]
  have hi : b.P*b.P ≤ b.P := by
    have hu : Commute b.P (1-b.P) := (Commute.one_right _).sub_right (Commute.refl _)
    have h := mul_comm_nonneg b.hp (sub_nonneg.mpr b.hi) hu
    rwa [mul_sub,mul_one,sub_nonneg] at h
  have hz : 0 ≤ (b.P-b.P*b.P) i i := (Matrix.le_iff.mp hi).diag_nonneg
  unfold L signE jump; split_ifs <;> simp only [Matrix.sub_apply] at * <;> grind

lemma tr_blk (w:Fin m→ℝ) (hw:∀ i,0≤w i) :
    mats (fun i=> ∑ j,(b.a i*w i+b.a j*w j)/2*b.E i j^2) ≤
    mats (fun i=>b.S i i*w i) := by
  have he :
      (∑ i,∑ j,(b.a i*w i+b.a j*w j)/2*b.E i j^2)=
      ∑ i,b.a i*w i*∑ j,b.E i j^2 := by
    have h (i j) :
        (b.a i*w i+b.a j*w j)/2*b.E i j^2=
        (b.a i*w i*b.E i j^2+b.a j*w j*b.E j i^2)/2 := by rw [symm_entry b.Her i j]; ring
    let F := fun i j=> b.a i*w i*b.E i j^2
    simp_rw [h,← Finset.sum_div,Finset.sum_add_distrib, Finset.mul_sum]
    change ((∑ i,∑ j,F i j)+(∑ j,∑ i,F i j))/2=∑ i,∑ j,F i j
    rw [Finset.sum_comm]; ring
  unfold mats
  rw [he]
  gcongr
  change _ ≤ b.S i i*w i
  rw [b.Sdiag]
  apply le_trans (mul_le_mul_of_nonneg_left (b.Ed2 _) (mul_nonneg (abs_nonneg _) (hw _)))
  apply le_of_eq; unfold a; ring

end block
end GeneralMahler

end

end OAI
