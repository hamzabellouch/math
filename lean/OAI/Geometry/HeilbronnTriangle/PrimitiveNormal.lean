import Mathlib

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix

abbrev Vector := Fin 3 → ℤ

def coordGcd (v : Vector) : ℕ :=
  Int.gcd (Int.gcd (v 0) (v 1) : ℤ) (v 2)

def IsPrimitive (v : Vector) : Prop := coordGcd v = 1

lemma coordGcd_eq_zero_iff (v : Vector) : coordGcd v = 0 ↔ v = 0 := by
  rw [coordGcd, Int.gcd_eq_zero_iff]
  constructor
  · rintro ⟨h01, h2⟩
    have h01' : Int.gcd (v 0) (v 1) = 0 := by exact_mod_cast h01
    obtain ⟨h0, h1⟩ := Int.gcd_eq_zero_iff.mp h01'
    ext i
    fin_cases i <;> simp_all
  · intro h
    subst v
    simp

lemma coordGcd_dvd (v : Vector) (i : Fin 3) : (coordGcd v : ℤ) ∣ v i := by
  have h01 := Int.gcd_dvd_left (Int.gcd (v 0) (v 1) : ℤ) (v 2)
  have h2 := Int.gcd_dvd_right (Int.gcd (v 0) (v 1) : ℤ) (v 2)
  fin_cases i
  · exact dvd_trans h01 (Int.gcd_dvd_left _ _)
  · exact dvd_trans h01 (Int.gcd_dvd_right _ _)
  · exact h2

lemma exists_dot_eq_coordGcd (v : Vector) :
    ∃ z : Vector, v ⬝ᵥ z = (coordGcd v : ℤ) := by
  let d : ℤ := Int.gcd (v 0) (v 1)
  refine ⟨![Int.gcdA (v 0) (v 1) * Int.gcdA d (v 2),
    Int.gcdB (v 0) (v 1) * Int.gcdA d (v 2), Int.gcdB d (v 2)], ?_⟩
  have h01 := Int.gcd_eq_gcd_ab (v 0) (v 1)
  have h2 := Int.gcd_eq_gcd_ab d (v 2)
  simp only [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  change _ = (Int.gcd d (v 2) : ℤ)
  rw [h2]
  change _ = (Int.gcd (v 0) (v 1) : ℤ) * _ + _
  rw [h01]
  ring

lemma isPrimitive_iff_exists_dot_eq_one (v : Vector) :
    IsPrimitive v ↔ ∃ z : Vector, v ⬝ᵥ z = 1 := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_dot_eq_coordGcd v
    change coordGcd v = 1 at h
    exact ⟨z, by simpa [h] using hz⟩
  · rintro ⟨z, hz⟩
    have hd : (coordGcd v : ℤ) ∣ v ⬝ᵥ z := by
      rw [vec3_dotProduct]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left (coordGcd_dvd v 0) _)
        (dvd_mul_of_dvd_left (coordGcd_dvd v 1) _))
        (dvd_mul_of_dvd_left (coordGcd_dvd v 2) _)
    rw [hz] at hd
    have hd' : coordGcd v ∣ 1 := by exact_mod_cast hd
    exact Nat.dvd_one.mp hd'

lemma IsPrimitive.ne_zero {v : Vector} (h : IsPrimitive v) : v ≠ 0 := by
  intro hv
  have hg := (coordGcd_eq_zero_iff v).mpr hv
  unfold IsPrimitive at h
  omega

theorem exists_primitive_factor (v : Vector) (hv : v ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ ∃ w : Vector, IsPrimitive w ∧ v = g • w := by
  let g : ℤ := coordGcd v
  have hg : 0 < g := by
    have : coordGcd v ≠ 0 := by simpa [coordGcd_eq_zero_iff] using hv
    change (0 : ℤ) < (coordGcd v : ℤ)
    exact_mod_cast Nat.pos_of_ne_zero this
  let w : Vector := fun i => v i / g
  have hscale : v = g • w := by
    ext i
    exact (Int.mul_ediv_cancel' (coordGcd_dvd v i)).symm
  obtain ⟨z, hz⟩ := exists_dot_eq_coordGcd v
  have hw : w ⬝ᵥ z = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hg)
    calc
      g * (w ⬝ᵥ z) = (g • w) ⬝ᵥ z := by rw [smul_dotProduct, smul_eq_mul]
      _ = v ⬝ᵥ z := by rw [← hscale]
      _ = g := hz
      _ = g * 1 := by ring
  exact ⟨g, hg, w, (isPrimitive_iff_exists_dot_eq_one w).mpr ⟨z, hw⟩, hscale⟩

lemma coordinate_abs_le_of_factor {v w : Vector} {g : ℤ}
    (hg : 0 < g) (hscale : v = g • w) (i : Fin 3) : |w i| ≤ |v i| := by
  have hg1 : 1 ≤ g := hg
  rw [hscale, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hg]
  nlinarith [abs_nonneg (w i)]

theorem exists_primitive_normal (u v : Vector) (huv : u ⨯₃ v ≠ 0) :
    ∃ w : Vector, IsPrimitive w ∧ w ≠ 0 ∧ u ⬝ᵥ w = 0 ∧ v ⬝ᵥ w = 0 ∧
      (∀ z : Vector, Matrix.det ![u, v, z] = 0 ↔ z ⬝ᵥ w = 0) ∧
      (∀ i : Fin 3, |w i| ≤ |(u ⨯₃ v) i|) := by
  obtain ⟨g, hg, w, hw, hscale⟩ := exists_primitive_factor (u ⨯₃ v) huv
  have hdot (z : Vector) : z ⬝ᵥ u ⨯₃ v = 0 ↔ z ⬝ᵥ w = 0 := by
    rw [hscale, dotProduct_smul, smul_eq_mul, mul_eq_zero]
    simp [ne_of_gt hg]
  refine ⟨w, hw, hw.ne_zero, (hdot u).mp (dot_self_cross u v),
    (hdot v).mp (dot_cross_self u v), ?_, ?_⟩
  · intro z
    rw [← triple_product_eq_det, ← triple_product_permutation z u v]
    exact hdot z
  · exact coordinate_abs_le_of_factor hg hscale

def rowNormals (A : Matrix (Fin 3) (Fin 3) ℤ) : Fin 3 → Vector :=
  ![A 1 ⨯₃ A 2, A 2 ⨯₃ A 0, A 0 ⨯₃ A 1]

lemma mulVec_rowNormals (A : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) :
    (A *ᵥ rowNormals A i) j = if j = i then A.det else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [rowNormals, mulVec, vecHead, vecTail, cross_apply, det_fin_three] <;> ring

lemma exists_rowNormal_ne_zero (A : Matrix (Fin 3) (Fin 3) ℤ)
    (h : (fun j => A j 0) ⨯₃ (fun j => A j 1) ≠ 0) :
    ∃ i : Fin 3, rowNormals A i ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  ext i
  fin_cases i
  · simpa [rowNormals, cross_apply, mul_comm] using congrFun (hn 0) 2
  · simpa [rowNormals, cross_apply, mul_comm] using congrFun (hn 1) 2
  · simpa [rowNormals, cross_apply, mul_comm] using congrFun (hn 2) 2

lemma coefficients_zero_of_cross_ne_zero (u v : Vector) (h : u ⨯₃ v ≠ 0)
    (a b : ℤ) (hab : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have ha : a • (u ⨯₃ v) = 0 := by
    calc
      a • (u ⨯₃ v) = (a • u + b • v) ⨯₃ v := by
        ext i
        fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring
      _ = 0 := by rw [hab]; simp
  have hb : b • (u ⨯₃ v) = 0 := by
    calc
      b • (u ⨯₃ v) = u ⨯₃ (a • u + b • v) := by
        ext i
        fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring
      _ = 0 := by rw [hab]; simp
  exact ⟨(smul_eq_zero.mp ha).resolve_right h, (smul_eq_zero.mp hb).resolve_right h⟩

lemma kernel_coordinates_ne_zero (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpair : ∀ i j : Fin 3, i ≠ j → Aᵀ i ⨯₃ Aᵀ j ≠ 0)
    (w : Vector) (hw : w ≠ 0) (hk : A *ᵥ w = 0) :
    ∀ i : Fin 3, w i ≠ 0 := by
  have hrow (j : Fin 3) : A j 0 * w 0 + A j 1 * w 1 + A j 2 * w 2 = 0 := by
    simpa only [mulVec, vec3_dotProduct, Pi.zero_apply] using congrFun hk j
  intro i hi
  fin_cases i
  · change w 0 = 0 at hi
    have hrel : w 1 • Aᵀ 1 + w 2 • Aᵀ 2 = 0 := by
      ext j
      simpa [hi, mul_comm] using hrow j
    obtain ⟨h1, h2⟩ := coefficients_zero_of_cross_ne_zero _ _ (hpair 1 2 (by decide)) _ _ hrel
    apply hw
    ext j
    fin_cases j <;> simp [hi, h1, h2]
  · change w 1 = 0 at hi
    have hrel : w 0 • Aᵀ 0 + w 2 • Aᵀ 2 = 0 := by
      ext j
      simpa [hi, mul_comm] using hrow j
    obtain ⟨h0, h2⟩ := coefficients_zero_of_cross_ne_zero _ _ (hpair 0 2 (by decide)) _ _ hrel
    apply hw
    ext j
    fin_cases j <;> simp [hi, h0, h2]
  · change w 2 = 0 at hi
    have hrel : w 0 • Aᵀ 0 + w 1 • Aᵀ 1 = 0 := by
      ext j
      simpa [hi, mul_comm] using hrow j
    obtain ⟨h0, h1⟩ := coefficients_zero_of_cross_ne_zero _ _ (hpair 0 1 (by decide)) _ _ hrel
    apply hw
    ext j
    fin_cases j <;> simp [hi, h0, h1]

lemma abs_minor_le (a b c d X : ℤ) (hX : 0 ≤ X)
    (ha : |a| ≤ X) (hb : |b| ≤ X) (hc : |c| ≤ X) (hd : |d| ≤ X) :
    |a * b - c * d| ≤ 2 * X ^ 2 := by
  calc
    |a * b - c * d| ≤ |a * b| + |c * d| := by simpa using abs_sub_le (a * b) 0 (c * d)
    _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ X * X + X * X := add_le_add
      (mul_le_mul ha hb (abs_nonneg _) hX)
      (mul_le_mul hc hd (abs_nonneg _) hX)
    _ = 2 * X ^ 2 := by ring

lemma cross_coordinate_bound (u v : Vector) (X : ℤ) (hX : 0 ≤ X)
    (hu : ∀ i, |u i| ≤ X) (hv : ∀ i, |v i| ≤ X) (i : Fin 3) :
    |(u ⨯₃ v) i| ≤ 2 * X ^ 2 := by
  fin_cases i <;> simp only [cross_apply] <;>
    apply abs_minor_le _ _ _ _ X hX <;> first | apply hu | apply hv

theorem exists_primitive_right_null (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0)
    (hpair : ∀ i j : Fin 3, i ≠ j → Aᵀ i ⨯₃ Aᵀ j ≠ 0)
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
      (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
  obtain ⟨i, hi⟩ := exists_rowNormal_ne_zero A (hpair 0 1 (by decide))
  obtain ⟨g, hg, w, hw, hscale⟩ := exists_primitive_factor (rowNormals A i) hi
  have hk : A *ᵥ w = 0 := by
    ext j
    have hj : A j ⬝ᵥ rowNormals A i = 0 := by
      simpa [hdet, mulVec] using mulVec_rowNormals A i j
    rw [hscale, dotProduct_smul, smul_eq_mul] at hj
    exact (mul_eq_zero.mp hj).resolve_left (ne_of_gt hg)
  refine ⟨w, hw, hk, kernel_coordinates_ne_zero A hpair w hw.ne_zero hk, ?_⟩
  intro j
  apply le_trans (coordinate_abs_le_of_factor hg hscale j)
  fin_cases i <;> simp only [rowNormals] <;>
    apply cross_coordinate_bound _ _ X hX <;> apply hbound

theorem primitive_eq_or_eq_neg_of_cross_eq_zero (u v : Vector)
    (hu : IsPrimitive u) (hv : IsPrimitive v) (hcross : u ⨯₃ v = 0) :
    v = u ∨ v = -u := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one u).mp hu
  have hz' : z ⬝ᵥ u = 1 := by rwa [dotProduct_comm]
  have hrel : v = (z ⬝ᵥ v) • u := by
    have h := cross_cross_eq_smul_sub_smul' z u v
    rw [hcross] at h
    have h' : (z ⬝ᵥ v) • u = v := by
      simpa [hz, hz', sub_eq_zero] using h.symm
    exact h'.symm
  obtain ⟨t, ht⟩ := (isPrimitive_iff_exists_dot_eq_one v).mp hv
  have hunit : IsUnit (z ⬝ᵥ v) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨u ⬝ᵥ t, ?_⟩
    rw [hrel, smul_dotProduct, smul_eq_mul] at ht
    exact ht
  rcases Int.isUnit_iff.mp hunit with h | h
  · left
    simpa [h] using hrel
  · right
    simpa [h] using hrel

lemma cross_ne_zero_of_projective_ne (u v : Vector)
    (hu : u 2 ≠ 0) (hv : v 2 ≠ 0)
    (hproj : ((u 0 : ℝ) / u 2, (u 1 : ℝ) / u 2) ≠
      ((v 0 : ℝ) / v 2, (v 1 : ℝ) / v 2)) : u ⨯₃ v ≠ 0 := by
  intro hc
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := by
    simpa [cross_apply] using congrFun hc 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := by
    simpa [cross_apply] using congrFun hc 1
  have huR : (u 2 : ℝ) ≠ 0 := by exact_mod_cast hu
  have hvR : (v 2 : ℝ) ≠ 0 := by exact_mod_cast hv
  apply hproj
  apply Prod.ext
  · apply (div_eq_div_iff huR hvR).mpr
    have h1R : (u 2 : ℝ) * v 0 - (u 0 : ℝ) * v 2 = 0 := by exact_mod_cast h1
    nlinarith
  · apply (div_eq_div_iff huR hvR).mpr
    have h0R : (u 1 : ℝ) * v 2 - (u 2 : ℝ) * v 1 = 0 := by exact_mod_cast h0
    nlinarith

theorem exists_primitive_right_null_of_projections (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
    (hproj : ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
      (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
  apply exists_primitive_right_null A hdet _ X hX hbound
  intro i j hij
  exact cross_ne_zero_of_projective_ne _ _ (hheight i) (hheight j) (hproj i j hij)

def toEuclidean (v : Vector) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

lemma norm_le_three_mul_of_coordinate_bound (v : Vector) (R : ℝ)
    (hR : 0 ≤ R) (h : ∀ i, |(v i : ℝ)| ≤ R) : ‖toEuclidean v‖ ≤ 3 * R := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h0 := sq_le_sq₀ (abs_nonneg (v 0 : ℝ)) hR |>.mpr (h 0)
  have h1 := sq_le_sq₀ (abs_nonneg (v 1 : ℝ)) hR |>.mpr (h 1)
  have h2 := sq_le_sq₀ (abs_nonneg (v 2 : ℝ)) hR |>.mpr (h 2)
  simp only [sq_abs] at h0 h1 h2
  simp [toEuclidean, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg R]

theorem exists_bounded_primitive_right_null (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
    (hproj : ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
      (∀ i, w i ≠ 0) ∧ ‖toEuclidean w‖ ≤ 6 * (X : ℝ) ^ 2 := by
  obtain ⟨w, hw, hk, hn, hb⟩ :=
    exists_primitive_right_null_of_projections A hdet hheight hproj X hX hbound
  refine ⟨w, hw, hk, hn, ?_⟩
  have h := norm_le_three_mul_of_coordinate_bound w (2 * (X : ℝ) ^ 2)
    (by positivity) (fun i => by exact_mod_cast hb i)
  nlinarith

lemma one_le_norm_of_ne_zero (v : Vector) (hv : v ≠ 0) : 1 ≤ ‖toEuclidean v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have hi1 : (1 : ℤ) ≤ |v i| := abs_pos.mpr hi
  calc
    (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast hi1
    _ = ‖(toEuclidean v).ofLp i‖ := by simp [toEuclidean]
    _ ≤ ‖toEuclidean v‖ := PiLp.norm_apply_le _ _

lemma modulus_le_norm_of_coordinate_zero (q : ℕ) (x : Vector) (k : Fin 3)
    (hk : x k ≠ 0) (hmod : (x k : ZMod q) = 0) :
    (q : ℝ) ≤ ‖toEuclidean x‖ := by
  have hd : (q : ℤ) ∣ x k := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have hab : (q : ℤ) ≤ |x k| :=
    Int.le_of_dvd (abs_pos.mpr hk) ((dvd_abs _ _).mpr hd)
  calc
    (q : ℝ) ≤ |(x k : ℝ)| := by exact_mod_cast hab
    _ = ‖(toEuclidean x).ofLp k‖ := by simp [toEuclidean]
    _ ≤ ‖toEuclidean x‖ := PiLp.norm_apply_le _ _

theorem modulus_le_norm_of_reduction_in_difference_line (q : ℕ) (x : Vector)
    (hx : ∀ k, x k ≠ 0) (i j : Fin 3)
    (hline : ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • (Pi.single i 1 - Pi.single j 1)) :
    (q : ℝ) ≤ ‖toEuclidean x‖ := by
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨a, ha⟩ := hline
  apply modulus_le_norm_of_coordinate_zero q x k (hx k)
  have hk := congrFun ha k
  simpa [Pi.single_apply, hki, hkj] using hk

lemma half_modulus_lt_shell_radius (q : ℕ) (x : Vector)
    (hx : ∀ k, x k ≠ 0) (i j : Fin 3)
    (hline : ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • (Pi.single i 1 - Pi.single j 1))
    (R : ℝ) (hR : ‖toEuclidean x‖ < 2 * R) : (q : ℝ) / 2 < R := by
  have h := modulus_le_norm_of_reduction_in_difference_line q x hx i j hline
  linarith

end Problem355.PrimitiveNormal

end OAI
