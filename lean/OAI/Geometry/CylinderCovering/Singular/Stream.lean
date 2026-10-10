import OAI.Geometry.CylinderCovering.Singular.StreamDefinitions

namespace OAI

noncomputable section

namespace CylinderCovering.SingularStream
open RuledApproximation
open scoped ContDiff

lemma potential_eq (p b r : ℝ) :
    potential p b r = (1 / 2 : ℝ) * (2 * r) ^ (p - 2) * (b ^ 2 - r ^ 2) := by
  unfold potential
  rw [show r / (1 / 2 : ℝ) = 2 * r by ring]

theorem potential_contDiffAt (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fun w : Plane => potential p (w 0) (w 1)) z := by
  have hs : ContDiffAt ℝ ∞ (fun w : Plane => w 1 / (1 / 2 : ℝ)) z := by
    fun_prop
  have hp := hs.rpow_const_of_ne (p := p - 2) (by positivity)
  exact (contDiffAt_const.mul hp).mul (by fun_prop)

theorem potential_wall_pos (p r : ℝ) : potential p r r = 0 := by
  simp [potential]

theorem potential_wall_neg (p r : ℝ) : potential p (-r) r = 0 := by
  simp [potential]

theorem potential_homogeneous (p b : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    potential p (t * b) (t * r) = t ^ p * potential p b r := by
  rw [potential_eq, potential_eq,
    show 2 * (t * r) = t * (2 * r) by ring,
    Real.mul_rpow ht.le (by positivity : (0 : ℝ) ≤ 2 * r)]
  have hpow : t ^ p = t ^ (p - 2) * t ^ (2 : ℕ) := by
    calc
      t ^ p = t ^ ((p - 2) + 2) := by congr 1; ring
      _ = t ^ (p - 2) * t ^ (2 : ℕ) := by rw [Real.rpow_add ht, Real.rpow_two]
  rw [hpow]
  ring

theorem potential_deriv_b (p b : ℝ) {r : ℝ} (_hr : 0 < r) :
    deriv (fun x : ℝ => potential p x r) b = singularField p (vec2 b r) 1 := by
  have hd := ((hasDerivAt_pow 2 b).sub_const (r ^ 2)).const_mul
    ((1 / 2 : ℝ) * (2 * r) ^ (p - 2))
  have he : (fun x : ℝ => (1 / 2 : ℝ) * (2 * r) ^ (p - 2) *
      (x ^ 2 - r ^ 2)) = (fun x => potential p x r) := by
    funext x
    exact (potential_eq p x r).symm
  rw [he] at hd
  rw [hd.deriv]
  dsimp only [singularField, vec2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub]
  rw [show r / (1 / 2 : ℝ) = 2 * r by ring]
  ring

theorem potential_neg_deriv_r (p b : ℝ) {r : ℝ} (hr : 0 < r) :
    -deriv (fun y : ℝ => potential p b y) r = singularField p (vec2 b r) 0 := by
  have hpow := ((hasDerivAt_id r).const_mul 2).rpow_const
    (p := p - 2) (Or.inl (by positivity : (2 : ℝ) * r ≠ 0))
  have hd := ((hpow.const_mul (1 / 2 : ℝ)).mul
    ((hasDerivAt_pow 2 r).const_sub (b ^ 2)))
  have he : (fun y : ℝ => (1 / 2 : ℝ) * (2 * y) ^ (p - 2) *
      (b ^ 2 - y ^ 2)) = (fun y => potential p b y) := by
    funext y
    exact (potential_eq p b y).symm
  change HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * (2 * y) ^ (p - 2) *
    (b ^ 2 - y ^ 2)) _ r at hd
  rw [he] at hd
  rw [hd.deriv]
  have hlow : (2 * r) ^ (p - 2 - 1) = (2 * r) ^ (p - 2) / (2 * r) := by
    rw [Real.rpow_sub_one (by positivity : (2 : ℝ) * r ≠ 0)]
  have hhigh : (2 * r) ^ (p - 1) = (2 * r) ^ (p - 2) * (2 * r) := by
    rw [show p - 1 = (p - 2) + 1 by ring,
      Real.rpow_add_one (by positivity : (2 : ℝ) * r ≠ 0)]
  dsimp only [singularField, vec2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [show r / (1 / 2 : ℝ) = 2 * r by ring, hlow, hhigh]
  field_simp [hr.ne']
  ring

theorem field_hamiltonian (p b : ℝ) {r : ℝ} (hr : 0 < r) :
    singularField p (vec2 b r) =
      vec2 (-deriv (fun y : ℝ => potential p b y) r)
        (deriv (fun x : ℝ => potential p x r) b) := by
  rw [potential_neg_deriv_r p b hr, potential_deriv_b p b hr]
  ext i
  fin_cases i <;> simp [vec2]

end CylinderCovering.SingularStream

end

end OAI
