import OAI.Geometry.HarmonicGrowth.Basic

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open Matrix
open scoped BigOperators

namespace HarmonicCounterexample.Berger

variable {ι : Type*} [Fintype ι]

lemma dot_self_nonneg (w : ι → ℝ) : 0 ≤ w ⬝ᵥ w := by
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)

lemma dot_self_pos {w : ι → ℝ} (hw : w ≠ 0) : 0 < w ⬝ᵥ w :=
  lt_of_le_of_ne (dot_self_nonneg w) (Ne.symm (mt dotProduct_self_eq_zero.mp hw))

/-- Bessel's two-vector inequality, without an implicit Euclidean norm instance. -/
lemma two_vector_bessel {u v : ι → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (w : ι → ℝ) : (u ⬝ᵥ w)^2 + (v ⬝ᵥ w)^2 ≤ w ⬝ᵥ w := by
  have hvu : v ⬝ᵥ u = 0 := by rwa [dotProduct_comm]
  have hwu : w ⬝ᵥ u = u ⬝ᵥ w := dotProduct_comm _ _
  have hwv : w ⬝ᵥ v = v ⬝ᵥ w := dotProduct_comm _ _
  have h := dot_self_nonneg (w - (u ⬝ᵥ w) • u - (v ⬝ᵥ w) • v)
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    hu, hv, huv, hvu, hwu, hwv, smul_eq_mul] at h
  nlinarith

variable [DecidableEq ι]

/-- Cartesian coefficient tensor of dr²+r²G(a,q,J), with u=x/r,
v=Jx/r and c=a²q^(-1/m). The radial eigenvalue remains exactly one. -/
def tensor (u v : ι → ℝ) (c q : ℝ) : Matrix ι ι ℝ :=
  c • 1 + (1-c) • vecMulVec u u + (c*(q-1)) • vecMulVec v v

omit [Fintype ι] in
lemma tensor_symmetric (u v : ι → ℝ) (c q : ℝ) : (tensor u v c q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [tensor, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, star_trivial]
  by_cases h : i = j
  · subst j
    ring
  · simp only [Matrix.one_apply, ite_eq_right h, ite_eq_right (Ne.symm h)]
    ring

lemma tensor_quadratic (u v w : ι → ℝ) (c q : ℝ) :
    w ⬝ᵥ (tensor u v c q *ᵥ w) =
      c * (w ⬝ᵥ w) + (1-c) * (u ⬝ᵥ w)^2 + c*(q-1)*(v ⬝ᵥ w)^2 := by
  simp only [tensor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
  rw [dotProduct_comm w u, dotProduct_comm w v]
  ring

/-- Uniform ellipticity with the exact three eigenvalue bounds. -/
theorem tensor_lower_bound {u v : ι → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    {c q ell : ℝ} (hell1 : ell ≤ 1) (hellc : ell ≤ c) (hellcq : ell ≤ c*q)
    (w : ι → ℝ) : ell * (w ⬝ᵥ w) ≤ w ⬝ᵥ (tensor u v c q *ᵥ w) := by
  rw [tensor_quadratic]
  have hb := two_vector_bessel hu hv huv w
  have h₁ := mul_nonneg (sub_nonneg.2 hell1) (sq_nonneg (u ⬝ᵥ w))
  have h₂ := mul_nonneg (sub_nonneg.2 hellcq) (sq_nonneg (v ⬝ᵥ w))
  have h₃ := mul_nonneg (sub_nonneg.2 hellc)
    (show 0 ≤ w ⬝ᵥ w - (u ⬝ᵥ w)^2 - (v ⬝ᵥ w)^2 by linarith)
  nlinarith

/-- Actual positive definiteness of the Berger radial extension, including
q<1 on the negative-amplitude control pulses. -/
theorem tensor_posDef {u v : ι → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    {c q : ℝ} (hc : 0 < c) (hq : 0 < q) : (tensor u v c q).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (tensor_symmetric _ _ _ _)
  intro w hw
  simp only [star_trivial]
  let ell := min 1 (min c (c*q))
  have hell : 0 < ell := lt_min (by norm_num) (lt_min hc (mul_pos hc hq))
  have hb := tensor_lower_bound hu hv huv (min_le_left 1 (min c (c*q)))
    ((min_le_right 1 (min c (c*q))).trans (min_le_left c (c*q)))
    ((min_le_right 1 (min c (c*q))).trans (min_le_right c (c*q))) w
  exact lt_of_lt_of_le (mul_pos hell (dot_self_pos hw)) hb

lemma tensor_radial {u v : ι → ℝ}
    (hu : u ⬝ᵥ u = 1) (huv : u ⬝ᵥ v = 0) (c q : ℝ) :
    tensor u v c q *ᵥ u = u := by
  have hvu : v ⬝ᵥ u = 0 := by rwa [dotProduct_comm]
  simp only [tensor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, hu, hvu, MulOpposite.op_one,
    MulOpposite.op_zero, one_smul, zero_smul, smul_zero, add_zero]
  rw [← add_smul]
  simp

lemma tensor_hopf {u v : ι → ℝ}
    (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) (c q : ℝ) :
    tensor u v c q *ᵥ v = (c*q) • v := by
  simp only [tensor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, hv, huv, MulOpposite.op_one,
    MulOpposite.op_zero, one_smul, zero_smul, smul_zero, add_zero]
  rw [← add_smul]
  congr 1
  ring

lemma tensor_horizontal {u v w : ι → ℝ}
    (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0) (c q : ℝ) :
    tensor u v c q *ᵥ w = c • w := by
  simp [tensor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    huw, hvw]

end HarmonicCounterexample.Berger

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open Matrix
open scoped BigOperators
open Matrix
open scoped BigOperators

namespace HarmonicCounterexample.Berger

/-- Exactly the two standing equations for an orthogonal complex structure.
Both orientation classes are permitted. -/
structure ComplexStructure (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Matrix ι ι ℝ
  square : matrix * matrix = -1
  orthogonal : matrixᵀ * matrix = 1

namespace ComplexStructure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma skew (J : ComplexStructure ι) : J.matrixᵀ = -J.matrix := by
  have h := congrArg (fun A => J.matrixᵀ * A) J.square
  rw [← mul_assoc, J.orthogonal, one_mul, mul_neg, mul_one] at h
  have hh := congrArg Neg.neg h
  simpa only [neg_neg] using hh.symm

lemma preserves_dot (J : ComplexStructure ι) (x y : ι → ℝ) :
    (J.matrix *ᵥ x) ⬝ᵥ (J.matrix *ᵥ y) = x ⬝ᵥ y := by
  calc
    (J.matrix *ᵥ x) ⬝ᵥ (J.matrix *ᵥ y) = x ⬝ᵥ (J.matrixᵀ *ᵥ (J.matrix *ᵥ y)) := by
      rw [dotProduct_mulVec x J.matrixᵀ (J.matrix *ᵥ y), vecMul_transpose]
    _ = x ⬝ᵥ y := by rw [mulVec_mulVec, J.orthogonal, one_mulVec]

lemma orthogonal_radial (J : ComplexStructure ι) (x : ι → ℝ) :
    x ⬝ᵥ (J.matrix *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (J.matrix *ᵥ x) = -(x ⬝ᵥ (J.matrix *ᵥ x)) := by
    calc
      x ⬝ᵥ (J.matrix *ᵥ x) = (J.matrixᵀ *ᵥ x) ⬝ᵥ x := by
        rw [dotProduct_mulVec, ← vecMul_transpose J.matrixᵀ x, transpose_transpose]
      _ = -(x ⬝ᵥ (J.matrix *ᵥ x)) := by
        rw [J.skew, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith

/-- Reindexing does not change either defining equation. -/
def reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (J : ComplexStructure ι) (e : κ ≃ ι) : ComplexStructure κ where
  matrix := J.matrix.submatrix e e
  square := by
    rw [submatrix_mul_equiv, J.square]
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply, e.injective.eq_iff]
  orthogonal := by
    rw [transpose_submatrix, submatrix_mul_equiv, J.orthogonal, submatrix_one_equiv]

/-- A genuine model in every even dimension, not a nonemptiness assumption. -/
def block (s : ℕ) : ComplexStructure (Fin s ⊕ Fin s) where
  matrix := fromBlocks 0 (-1) 1 0
  square := by
    rw [fromBlocks_multiply]
    simp only [mul_zero, mul_neg, mul_one, add_zero, zero_add]
    simpa only [neg_zero, fromBlocks_one] using
      (fromBlocks_neg (1 : Matrix (Fin s) (Fin s) ℝ)
        (0 : Matrix (Fin s) (Fin s) ℝ) (0 : Matrix (Fin s) (Fin s) ℝ)
        (1 : Matrix (Fin s) (Fin s) ℝ)).symm
  orthogonal := by
    rw [fromBlocks_transpose, fromBlocks_multiply]
    simp

def standard (s : ℕ) : ComplexStructure (Fin (s+s)) :=
  (block s).reindex finSumFinEquiv.symm

end ComplexStructure
end HarmonicCounterexample.Berger

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open Matrix
open scoped BigOperators
open Matrix
open scoped BigOperators
open Filter Matrix
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Cartesian

abbrev Coord (n : ℕ) := Fin n → ℝ

def squareRadius {n : ℕ} (x : Coord n) : ℝ := x ⬝ᵥ x

def radius {n : ℕ} (x : Coord n) : ℝ := Real.sqrt (squareRadius x)

def logRadius {n : ℕ} (x : Coord n) : ℝ := (1/2:ℝ) * Real.log (squareRadius x)

lemma squareRadius_nonneg {n : ℕ} (x : Coord n) : 0 ≤ squareRadius x := by
  unfold squareRadius dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

@[simp] lemma squareRadius_zero {n : ℕ} : squareRadius (0 : Coord n) = 0 := by
  simp [squareRadius]

@[simp] lemma squareRadius_eq_zero {n : ℕ} {x : Coord n} : squareRadius x = 0 ↔ x = 0 :=
  dotProduct_self_eq_zero

lemma squareRadius_pos {n : ℕ} {x : Coord n} (hx : x ≠ 0) : 0 < squareRadius x :=
  lt_of_le_of_ne (squareRadius_nonneg x) (Ne.symm (mt squareRadius_eq_zero.mp hx))

lemma radius_nonneg {n : ℕ} (x : Coord n) : 0 ≤ radius x := Real.sqrt_nonneg _

@[simp] lemma radius_zero {n : ℕ} : radius (0 : Coord n) = 0 := by simp [radius]

lemma radius_pos {n : ℕ} {x : Coord n} (hx : x ≠ 0) : 0 < radius x :=
  Real.sqrt_pos.2 (squareRadius_pos hx)

lemma radius_sq {n : ℕ} (x : Coord n) : radius x ^ 2 = squareRadius x :=
  Real.sq_sqrt (squareRadius_nonneg x)

lemma squareRadius_smooth {n : ℕ} : ContDiff ℝ ∞ (@squareRadius n) := by
  unfold squareRadius dotProduct
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

lemma radius_continuous {n : ℕ} : Continuous (@radius n) :=
  Real.continuous_sqrt.comp squareRadius_smooth.continuous

lemma radius_smoothAt {n : ℕ} {x : Coord n} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radius x :=
  squareRadius_smooth.contDiffAt.sqrt (squareRadius_pos hx).ne'

lemma logRadius_smoothAt {n : ℕ} {x : Coord n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ logRadius x :=
  contDiffAt_const.mul (squareRadius_smooth.contDiffAt.log (squareRadius_pos hx).ne')

lemma norm_le_radius {n : ℕ} (x : Coord n) : ‖x‖ ≤ radius x := by
  apply (pi_norm_le_iff_of_nonneg (radius_nonneg x)).2
  intro i
  have hi : x i * x i ≤ squareRadius x :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  have hr := radius_sq x
  rw [Real.norm_eq_abs]
  apply (abs_le).2
  constructor <;> nlinarith [radius_nonneg x]

/-- Euclidean radial sublevels are genuinely compact in the Cartesian space. -/
lemma radius_sublevel_compact {n : ℕ} (R : ℝ) : IsCompact {x : Coord n | radius x ≤ R} := by
  apply (isCompact_closedBall (0 : Coord n) R).of_isClosed_subset
  · exact isClosed_le radius_continuous continuous_const
  · intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_radius x).trans hx

lemma logRadius_eq_log_radius {n : ℕ} (x : Coord n) :
    logRadius x = Real.log (radius x) := by
  unfold logRadius
  rw [← radius_sq x, Real.log_pow]
  ring

lemma exp_logRadius {n : ℕ} {x : Coord n} (hx : x ≠ 0) :
    Real.exp (logRadius x) = radius x := by
  rw [logRadius_eq_log_radius x, Real.exp_log (radius_pos hx)]

lemma radius_exp_bound {n : ℕ} {x : Coord n} {t : ℝ} (hx : x ≠ 0) :
    logRadius x < t ↔ radius x < Real.exp t := by
  rw [logRadius_eq_log_radius x, Real.log_lt_iff_lt_exp (radius_pos hx)]

end HarmonicCounterexample.Cartesian

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open Matrix
open scoped BigOperators
open Matrix
open scoped BigOperators
open Filter Matrix
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Cartesian
open Berger

/-- Unit radial vector in the background Cartesian metric. -/
def radialUnit {n : ℕ} (x : Coord n) : Coord n := (radius x)⁻¹ • x

/-- Unit Hopf vector for the indicated orthogonal complex structure. -/
def hopfUnit {n : ℕ} (J : ComplexStructure (Fin n)) (x : Coord n) : Coord n :=
  (radius x)⁻¹ • (J.matrix *ᵥ x)

lemma radialUnit_unit {n : ℕ} {x : Coord n} (hx : x ≠ 0) :
    radialUnit x ⬝ᵥ radialUnit x = 1 := by
  simp only [radialUnit, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  change (radius x)⁻¹ * ((radius x)⁻¹ * squareRadius x) = 1
  rw [← radius_sq x]
  have h := (radius_pos hx).ne'
  field_simp

lemma hopfUnit_unit {n : ℕ} (J : ComplexStructure (Fin n)) {x : Coord n} (hx : x ≠ 0) :
    hopfUnit J x ⬝ᵥ hopfUnit J x = 1 := by
  simp only [hopfUnit, smul_dotProduct, dotProduct_smul, smul_eq_mul, J.preserves_dot]
  change (radius x)⁻¹ * ((radius x)⁻¹ * squareRadius x) = 1
  rw [← radius_sq x]
  have h := (radius_pos hx).ne'
  field_simp

lemma radial_hopf_orthogonal {n : ℕ} (J : ComplexStructure (Fin n)) (x : Coord n) :
    radialUnit x ⬝ᵥ hopfUnit J x = 0 := by
  simp [radialUnit, hopfUnit, smul_dotProduct, dotProduct_smul, J.orthogonal_radial]

lemma radialUnit_smoothAt {n : ℕ} {x : Coord n} (hx : x ≠ 0) (i : Fin n) :
    ContDiffAt ℝ ∞ (fun y => radialUnit y i) x := by
  exact ((radius_smoothAt hx).inv (radius_pos hx).ne').mul (contDiff_apply ℝ ℝ i).contDiffAt

lemma hopfUnit_smoothAt {n : ℕ} (J : ComplexStructure (Fin n))
    {x : Coord n} (hx : x ≠ 0) (i : Fin n) :
    ContDiffAt ℝ ∞ (fun y => hopfUnit J y i) x := by
  apply ((radius_smoothAt hx).inv (radius_pos hx).ne').mul
  change ContDiffAt ℝ ∞ (fun y => ∑ j, J.matrix i j * y j) x
  apply ContDiffAt.sum
  intro j _
  exact contDiffAt_const.mul (contDiff_apply ℝ ℝ j).contDiffAt

/-- The actual punctured Cartesian tensor; J may switch on round gaps. -/
def rawCoefficient {n : ℕ} (c q : ℝ → ℝ) (J : ℝ → ComplexStructure (Fin n))
    (x : Coord n) : Matrix (Fin n) (Fin n) ℝ :=
  if x = 0 then 1 else
    tensor (radialUnit x) (hopfUnit (J (logRadius x)) x) (c (logRadius x)) (q (logRadius x))

lemma rawCoefficient_posDef {n : ℕ} (c q : ℝ → ℝ) (J : ℝ → ComplexStructure (Fin n))
    (hc : ∀ t, 0 < c t) (hq : ∀ t, 0 < q t) (x : Coord n) :
    (rawCoefficient c q J x).PosDef := by
  classical
  unfold rawCoefficient
  split_ifs with hx
  · exact Matrix.PosDef.one
  · exact tensor_posDef (radialUnit_unit hx) (hopfUnit_unit _ hx)
      (radial_hopf_orthogonal _ _) (hc _) (hq _)

lemma fixedTensor_smoothAt {n : ℕ} (c q : ℝ → ℝ) (J : ComplexStructure (Fin n))
    (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q) {x : Coord n} (hx : x ≠ 0)
    (i j : Fin n) : ContDiffAt ℝ ∞
      (fun y => tensor (radialUnit y) (hopfUnit J y) (c (logRadius y)) (q (logRadius y)) i j) x := by
  have hlog := logRadius_smoothAt hx
  have hc' := hc.contDiffAt.comp x hlog
  have hq' := hq.contDiffAt.comp x hlog
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · exact hc'.mul contDiffAt_const
    · exact (contDiffAt_const.sub hc').mul ((radialUnit_smoothAt hx i).mul (radialUnit_smoothAt hx j))
  · exact (hc'.mul (hq'.sub contDiffAt_const)).mul
      ((hopfUnit_smoothAt J hx i).mul (hopfUnit_smoothAt J hx j))

lemma rawCoefficient_smoothAt_nonzero {n : ℕ} (c q : ℝ → ℝ)
    (J : ℝ → ComplexStructure (Fin n))
    (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hJ : ∀ t, (∀ᶠ s in 𝓝 t, J s = J t) ∨ (∀ᶠ s in 𝓝 t, q s = 1))
    {x : Coord n} (hx : x ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => rawCoefficient c q J y i j) x := by
  have hf := fixedTensor_smoothAt c q (J (logRadius x)) hc hq hx i j
  apply hf.congr_of_eventuallyEq
  have hne : ∀ᶠ y : Coord n in 𝓝 x, y ≠ 0 := isOpen_ne.mem_nhds hx
  rcases hJ (logRadius x) with hconst | hround
  · have h := (logRadius_smoothAt hx).continuousAt.eventually hconst
    filter_upwards [hne, h] with y hy hJy
    simp only [rawCoefficient, ite_eq_right hy, hJy]
  · have h := (logRadius_smoothAt hx).continuousAt.eventually hround
    filter_upwards [hne, h] with y hy hqy
    simp [rawCoefficient, hy, hqy, tensor]

lemma rawCoefficient_euclidean {n : ℕ} (c q : ℝ → ℝ)
    (J : ℝ → ComplexStructure (Fin n)) {T : ℝ}
    (hc : ∀ t ≤ T, c t = 1) (hq : ∀ t ≤ T, q t = 1)
    {x : Coord n} (hx : radius x < Real.exp T) : rawCoefficient c q J x = 1 := by
  classical
  by_cases hx0 : x = 0
  · simp [rawCoefficient, hx0]
  · have ht : logRadius x ≤ T := ((radius_exp_bound hx0).2 hx).le
    simp [rawCoefficient, hx0, hc _ ht, hq _ ht, tensor]

lemma rawCoefficient_smooth {n : ℕ} (c q : ℝ → ℝ)
    (J : ℝ → ComplexStructure (Fin n))
    (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hJ : ∀ t, (∀ᶠ s in 𝓝 t, J s = J t) ∨ (∀ᶠ s in 𝓝 t, q s = 1))
    {T : ℝ} (hc0 : ∀ t ≤ T, c t = 1) (hq0 : ∀ t ≤ T, q t = 1)
    (i j : Fin n) : ContDiff ℝ ∞ (fun y => rawCoefficient c q J y i j) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x = 0
  · subst x
    have he : ∀ᶠ y : Coord n in 𝓝 0, radius y < Real.exp T :=
      (radius_continuous.tendsto 0).eventually (eventually_lt_nhds (by simpa using Real.exp_pos T))
    have hf : ContDiffAt ℝ ∞ (fun _ : Coord n => (1 : Matrix (Fin n) (Fin n) ℝ) i j) 0 :=
      contDiffAt_const
    apply hf.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    rw [rawCoefficient_euclidean c q J hc0 hq0 hy]
  · exact rawCoefficient_smoothAt_nonzero c q J hc hq hJ hx i j

end HarmonicCounterexample.Cartesian

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open Matrix
open scoped BigOperators
open Matrix
open scoped BigOperators
open Filter Matrix
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Cartesian
open Berger

/-- A concrete smooth metric from the manuscript's logarithmic Berger data.
The local constancy alternative encodes switching J only inside round gaps. -/
def bergerMetric {n : ℕ} (c q : ℝ → ℝ) (J : ℝ → ComplexStructure (Fin n))
    (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hcp : ∀ t, 0 < c t) (hqp : ∀ t, 0 < q t)
    (hJ : ∀ t, (∀ᶠ s in 𝓝 t, J s = J t) ∨ (∀ᶠ s in 𝓝 t, q s = 1))
    {T : ℝ} (hc0 : ∀ t ≤ T, c t = 1) (hq0 : ∀ t ≤ T, q t = 1) : SmoothMetric n where
  coeff := rawCoefficient c q J
  smooth := rawCoefficient_smooth c q J hc hq hJ hc0 hq0
  positive := rawCoefficient_posDef c q J hcp hqp

lemma bergerMetric_euclidean {n : ℕ} (c q : ℝ → ℝ)
    (J : ℝ → ComplexStructure (Fin n))
    (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hcp : ∀ t, 0 < c t) (hqp : ∀ t, 0 < q t)
    (hJ : ∀ t, (∀ᶠ s in 𝓝 t, J s = J t) ∨ (∀ᶠ s in 𝓝 t, q s = 1))
    {T : ℝ} (hc0 : ∀ t ≤ T, c t = 1) (hq0 : ∀ t ≤ T, q t = 1) :
    EuclideanNearOrigin (bergerMetric c q J hc hq hcp hqp hJ hc0 hq0) := by
  refine ⟨Real.exp T, Real.exp_pos T, ?_⟩
  intro x hx
  apply rawCoefficient_euclidean c q J hc0 hq0
  have hs : radius x ^ 2 < Real.exp T ^ 2 := by
    rw [radius_sq]
    simpa only [squareRadius, dotProduct, pow_two] using hx
  nlinarith [radius_nonneg x, Real.exp_pos T]

/-- The radial unit eigenvalue is exact, not just a uniform comparison. -/
lemma rawCoefficient_radial {n : ℕ} (c q : ℝ → ℝ)
    (J : ℝ → ComplexStructure (Fin n)) (x : Coord n) :
    rawCoefficient c q J x *ᵥ x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hr : radius x • radialUnit x = x := by
      rw [radialUnit, smul_smul, mul_inv_cancel₀ (radius_pos hx).ne', one_smul]
    conv_lhs => arg 2; rw [← hr]
    rw [Matrix.mulVec_smul, rawCoefficient, ite_eq_right hx,
      tensor_radial (radialUnit_unit hx) (radial_hopf_orthogonal _ _), hr]

end HarmonicCounterexample.Cartesian

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open Matrix
open scoped BigOperators
open Matrix
open scoped BigOperators
open Filter Matrix
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample
open Matrix
variable {n : ℕ}

lemma coordDeriv_add {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (i : Fin n) :
    coordDeriv i (fun y => f y + h y) x = coordDeriv i f x + coordDeriv i h x := by
  simp only [coordDeriv, fderiv_fun_add hf hh, _root_.add_apply]

lemma coordDeriv_sub {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (i : Fin n) :
    coordDeriv i (fun y => f y - h y) x = coordDeriv i f x - coordDeriv i h x := by
  simp only [coordDeriv, fderiv_fun_sub hf hh, _root_.sub_apply]

lemma coordDeriv_mul {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (i : Fin n) :
    coordDeriv i (fun y => f y * h y) x =
      f x * coordDeriv i h x + h x * coordDeriv i f x := by
  simp only [coordDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]

lemma coordDeriv_const (c : ℝ) (x : Space n) (i : Fin n) :
    coordDeriv i (fun _ => c) x = 0 := by simp [coordDeriv]

lemma coordDeriv_coordinate (x : Space n) (i j : Fin n) :
    coordDeriv i (fun y => y j) x = (1 : Matrix (Fin n) (Fin n) ℝ) j i := by
  rw [coordDeriv, (hasFDerivAt_apply j x).fderiv]
  simp [ContinuousLinearMap.proj_apply, Pi.single_apply, Matrix.one_apply]

lemma coordDeriv_sum {κ : Type*} (s : Finset κ) {f : κ → Space n → ℝ} {x : Space n}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) x) (i : Fin n) :
    coordDeriv i (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, coordDeriv i (f k) x := by
  simp only [coordDeriv, fderiv_fun_sum hf, _root_.sum_apply]

lemma coordDeriv_linear (M : Matrix (Fin n) (Fin n) ℝ) (x : Space n) (i j : Fin n) :
    coordDeriv i (fun y => (M *ᵥ y) j) x = M j i := by
  calc
    _ = ∑ k : Fin n, coordDeriv i (fun y : Space n => M j k * y k) x :=
      coordDeriv_sum Finset.univ (f := fun k y => M j k * y k)
        (fun k _ => (differentiableAt_const _).mul
          (hasFDerivAt_apply k x).differentiableAt) i
    _ = _ := by
      simp only [coordDeriv_mul (differentiableAt_const _) (hasFDerivAt_apply _ _).differentiableAt,
        coordDeriv_const, coordDeriv_coordinate, mul_zero, add_zero, Matrix.one_apply]
      simp

lemma coordDeriv_congr {f h : Space n → ℝ} {x : Space n}
    (hf : f =ᶠ[𝓝 x] h) (i : Fin n) : coordDeriv i f x = coordDeriv i h x := by
  rw [coordDeriv, coordDeriv, hf.fderiv_eq]

lemma coordDeriv_chain {f : Space n → ℝ} {h : ℝ → ℝ} {x : Space n} {h' : ℝ}
    (hf : DifferentiableAt ℝ f x) (hh : HasDerivAt h h' (f x)) (i : Fin n) :
    coordDeriv i (fun y => h (f y)) x = h' * coordDeriv i f x := by
  change (fderiv ℝ (h ∘ f) x) (Pi.single i 1) = _
  rw [(hh.comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, coordDeriv]

lemma coordDeriv_inv {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) (i : Fin n) :
    coordDeriv i (fun y => (f y)⁻¹) x = -(f x ^ 2)⁻¹ * coordDeriv i f x := by
  exact coordDeriv_chain hf (hasDerivAt_inv h0) i

lemma coordDeriv_div {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x)
    (h0 : h x ≠ 0) (i : Fin n) :
    coordDeriv i (fun y => f y / h y) x =
      (h x * coordDeriv i f x-f x * coordDeriv i h x)/(h x)^2 := by
  simp only [div_eq_mul_inv]
  rw [coordDeriv_mul (h := fun y => (h y)⁻¹) hf (hh.inv h0), coordDeriv_inv hh h0]
  field_simp
  ring

lemma coordDeriv_pow {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (m : ℕ) (i : Fin n) :
    coordDeriv i (fun y => (f y)^m) x = (m:ℝ)*(f x)^(m-1)*coordDeriv i f x := by
  exact coordDeriv_chain hf (hasDerivAt_pow m (f x)) i

end HarmonicCounterexample

end

end OAI
