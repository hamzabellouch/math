import OAI.Analysis.StrictMeans.LatticeGeometry

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma lineIndex_mul_pos (p : ℤ → ℝ) (a : ℝ) (ha : 0<a) (i : ℤ) :
    lineIndex (fun j=>a*p j) i=lineIndex p i := by
  simp only [lineIndex,mul_lt_mul_iff_right₀ ha,mul_le_mul_iff_right₀ ha]

lemma signed_square_index (a t : ℝ) (ha : a≠0) (i : ℤ) :
    lineIndex (fun j=>a*((j:ℝ)-t)^2) i =
      if i=(if 0<a then ⌈t-1/2⌉ else ⌊t+1/2⌋) then (if 0<a then 1 else -1) else 0 := by
  rcases lt_or_gt_of_ne ha with ha|ha
  · have he : (fun j : ℤ=>a*((j:ℝ)-t)^2) = (fun j : ℤ =>(-a)*(-((j:ℝ)-t)^2)) := by funext j; ring
    rw [he,lineIndex_mul_pos _ _ (by linarith),concave_line_index]
    simp [not_lt.mpr ha.le]
  · rw [lineIndex_mul_pos _ _ ha,convex_line_index]
    simp [ha]

def signedVertex (a c x y : ℝ) : Lattice :=
  toLex ((if 0<a then ⌈x-1/2⌉ else ⌊x+1/2⌋),(if 0<c then ⌈y-1/2⌉ else ⌊y+1/2⌋))

lemma signed_diagonal_index (a c x y : ℝ) (ha : a≠0) (hc : c≠0) (v : Lattice) :
    heightIndex (latticeHeight (fun i=>a*((i:ℝ)-x)^2) (fun j=>c*((j:ℝ)-y)^2)) ex ey v =
      if v=signedVertex a c x y then (if 0<a then 1 else -1)*(if 0<c then 1 else -1) else 0 := by
  rw [latticeHeight_index]
  change lineIndex (fun i=>a*((i:ℝ)-x)^2) (ofLex v).1 *
    lineIndex (fun j=>c*((j:ℝ)-y)^2) (ofLex v).2 = _
  rw [signed_square_index _ _ ha,signed_square_index _ _ hc]
  have hv : v=signedVertex a c x y ↔
      (ofLex v).1=(if 0<a then ⌈x-1/2⌉ else ⌊x+1/2⌋) ∧
      (ofLex v).2=(if 0<c then ⌈y-1/2⌉ else ⌊y+1/2⌋) := by
    change v=toLex _ ↔ _
    rw [← ofLex_inj]
    exact Prod.ext_iff
  simp only [hv]
  split_ifs <;> simp_all

lemma diagonal_sample {o p : ℂ} {s a c : ℝ} (hs : s≠0) :
    (fun v=>quadratic a 0 c (meshPoint o s v-p)) =
      latticeHeight (fun i=>(a*s^2/2)*((i:ℝ)-(p.re-o.re)/s)^2)
        (fun j=>(c*s^2/2)*((j:ℝ)-(p.im-o.im)/s)^2) := by
  funext v
  simp only [quadratic,latticeHeight,meshPoint,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,latticeCoord_re,latticeCoord_im,
    smul_eq_mul]
  field_simp
  ring

lemma nearest_integer_bound (t : ℝ) :
    |(⌈t-1/2⌉:ℝ)-t|≤1/2 ∧ |(⌊t+1/2⌋:ℝ)-t|≤1/2 := by
  have h₁ := Int.le_ceil (t-1/2)
  have h₂ := Int.ceil_lt_add_one (t-1/2)
  have h₃ := Int.floor_le (t+1/2)
  have h₄ := Int.lt_floor_add_one (t+1/2)
  constructor <;> rw [abs_le] <;> constructor <;> linarith

lemma signedVertex_close {o p : ℂ} {s : ℝ} (hs : 0<s) (a c : ℝ) :
    dist (meshPoint o s (signedVertex a c ((p.re-o.re)/s) ((p.im-o.im)/s))) p≤ s := by
  let v := signedVertex a c ((p.re-o.re)/s) ((p.im-o.im)/s)
  have hx : |((ofLex v).1:ℝ)-(p.re-o.re)/s|≤1/2 := by
    dsimp [v,signedVertex]
    split_ifs <;> [exact (nearest_integer_bound _).1; exact (nearest_integer_bound _).2]
  have hy : |((ofLex v).2:ℝ)-(p.im-o.im)/s|≤1/2 := by
    dsimp [v,signedVertex]
    split_ifs <;> [exact (nearest_integer_bound _).1; exact (nearest_integer_bound _).2]
  have hre : (meshPoint o s v-p).re=s*(((ofLex v).1:ℝ)-(p.re-o.re)/s) := by
    simp only [meshPoint,Complex.sub_re,Complex.add_re,Complex.smul_re,latticeCoord_re,smul_eq_mul]
    field_simp; ring
  have him : (meshPoint o s v-p).im=s*(((ofLex v).2:ℝ)-(p.im-o.im)/s) := by
    simp only [meshPoint,Complex.sub_im,Complex.add_im,Complex.smul_im,latticeCoord_im,smul_eq_mul]
    field_simp; ring
  calc
    dist (meshPoint o s v) p = ‖meshPoint o s v-p‖ := dist_eq_norm _ _
    _ ≤ |(meshPoint o s v-p).re|+|(meshPoint o s v-p).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ s := by
      rw [hre,him,abs_mul,abs_mul,abs_of_pos hs]
      nlinarith [mul_le_mul_of_nonneg_left hx hs.le,mul_le_mul_of_nonneg_left hy hs.le]

lemma diagonal_local_sum {a c : ℝ} (ha : a≠0) (hc : c≠0)
    {o p : ℂ} {s r : ℝ} (hs : 0<s) (hr : s≤r) {S : Finset Lattice}
    (hS : ∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) :
    ∑ v∈S, heightIndex (fun w=>quadratic a 0 c (meshPoint o s w-p)) ex ey v =
      (if 0<a then 1 else -1)*(if 0<c then 1 else -1) := by
  rw [diagonal_sample hs.ne']
  have has : a*s^2/2≠0 := div_ne_zero (mul_ne_zero ha (pow_ne_zero _ hs.ne')) (by norm_num)
  have hcs : c*s^2/2≠0 := div_ne_zero (mul_ne_zero hc (pow_ne_zero _ hs.ne')) (by norm_num)
  simp_rw [signed_diagonal_index _ _ _ _ has hcs]
  have hv : signedVertex (a*s^2/2) (c*s^2/2) ((p.re-o.re)/s) ((p.im-o.im)/s)∈S :=
    (hS _).mpr ((signedVertex_close hs _ _).trans hr)
  simp only [Finset.sum_ite_eq',hv,ite_true]
  have hA : 0<a*s^2/2 ↔ 0<a := by
    rw [div_pos_iff_of_pos_right (by norm_num),mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hs.ne')]
  have hC : 0<c*s^2/2 ↔ 0<c := by
    rw [div_pos_iff_of_pos_right (by norm_num),mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hs.ne')]
  simp only [hA,hC]

end
end StrictInverseFirstPower.Grid

end

end OAI
