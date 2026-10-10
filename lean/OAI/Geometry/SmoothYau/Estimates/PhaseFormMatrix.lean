import Mathlib
import OAI.Geometry.SmoothYau.Geometry.RealForm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology

lemma continuous_quadratic_coercive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (q : V → ℝ) (hq : Continuous q)
    (hhom : ∀ (c : ℝ) (v : V), q (c • v) = c^2 * q v)
    (hpos : ∀ v ≠ 0, 0 < q v) : ∃ μ > 0, ∀ v, μ * ‖v‖^2 ≤ q v := by
  have hzero : q 0 = 0 := by simpa using hhom 0 0
  cases subsingleton_or_nontrivial V with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    rw [Subsingleton.elim v 0, norm_zero, hzero]
    norm_num
  | inr h =>
    let := h
    obtain ⟨v, hv⟩ : ∃ v : V, ‖v‖ = 1 := by
      obtain ⟨w, hw⟩ := exists_ne (0 : V)
      refine ⟨‖w‖⁻¹ • w, ?_⟩
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      ⟨v, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩ hq.continuousOn
    have hv₀norm : ‖v₀‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv₀
    have hv₀ne : v₀ ≠ 0 := by intro hz; simp [hz] at hv₀norm
    refine ⟨q v₀, hpos v₀ hv₀ne, ?_⟩
    intro w
    by_cases hw : w = 0
    · simp [hw, hzero]
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn.le), inv_mul_cancel₀ hwn.ne']
    have hh := hmin (show ‖w‖⁻¹ • w ∈ Metric.sphere (0 : V) 1 by
      simpa [Metric.mem_sphere, dist_zero_right] using hunit)
    change q v₀ ≤ q (‖w‖⁻¹ • w) at hh
    rw [hhom] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖w‖)
    calc
      _ ≤ (‖w‖⁻¹)^2 * q w * ‖w‖^2 := hh'
      _ = q w := by field_simp

variable {ι : Type*} [Fintype ι]

def realQuadratic (a : ι → ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * v i * v j

def squareSum (v : ι → ℝ) : ℝ := ∑ i, v i * v i

lemma realQuadratic_hom (a : ι → ι → ℝ) (c : ℝ) (v : ι → ℝ) :
    realQuadratic a (c • v) = c^2 * realQuadratic a v := by
  simp only [realQuadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma matrix_positive_coercive (a : Matrix ι ι ℝ) (ha : a.PosDef) :
    ∃ μ > 0, ∀ v : ι → ℝ, μ * squareSum v ≤ realQuadratic a v := by
  let q : EuclideanSpace ℝ ι → ℝ := fun v => realQuadratic a v
  have hc : Continuous q := by
    unfold q realQuadratic
    fun_prop
  have hp : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 → 0 < q v := by
    intro v hv
    have he : (fun i => v i) ≠ 0 := by
      intro hz
      apply hv
      ext i
      exact congrFun hz i
    have h := ha.dotProduct_mulVec_pos he
    dsimp [q, realQuadratic]
    simpa only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
      mul_left_comm, mul_assoc] using h
  have hh : ∀ (c : ℝ) (v : EuclideanSpace ℝ ι), q (c • v) = c^2*q v :=
    fun c v => realQuadratic_hom a c v
  obtain ⟨μ, hμ, hbound⟩ := continuous_quadratic_coercive q hc hh hp
  refine ⟨μ, hμ, fun v => ?_⟩
  have hb := hbound (WithLp.toLp 2 v)
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  simpa only [q, squareSum, sq, PiLp.toLp_apply] using hb

lemma squareSum_nonneg (v : ι → ℝ) : 0 ≤ squareSum v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma abs_mul_le_squareSum (v : ι → ℝ) (i j : ι) : |v i * v j| ≤ squareSum v := by
  have hi : v i * v i ≤ squareSum v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ i)
  have hj : v j * v j ≤ squareSum v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (v i + v j), sq_nonneg (v i - v j)]

lemma realQuadratic_abs_bound (a : ι → ι → ℝ) (v : ι → ℝ) :
    |realQuadratic a v| ≤ (∑ i, ∑ j, |a i j|) * squareSum v := by
  unfold realQuadratic
  calc
    _ ≤ ∑ i, |∑ j, a i j * v i * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j * v i * v j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_mul_le_squareSum v i j) (abs_nonneg _)

lemma realQuadratic_add (a b : ι → ι → ℝ) (v : ι → ℝ) :
    realQuadratic (a+b) v = realQuadratic a v + realQuadratic b v := by
  simp only [realQuadratic, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma realQuadratic_sub (a b : ι → ι → ℝ) (v : ι → ℝ) :
    realQuadratic (a-b) v = realQuadratic a v - realQuadratic b v := by
  simp only [realQuadratic, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma continuous_matrix_lower_near {T : Type*} [TopologicalSpace T]
    (a : T → ι → ι → ℝ) (ha : ∀ i j, Continuous (fun x => a x i j)) (x₀ : T)
    (hlower : ∀ v, 2 * squareSum v ≤ realQuadratic (a x₀) v) :
    ∀ᶠ x in nhds x₀, ∀ v, squareSum v ≤ realQuadratic (a x) v := by
  let variation : T → ℝ := fun x => ∑ i, ∑ j, |a x₀ i j - a x i j|
  have hc : Continuous variation := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (continuous_const.sub (ha i j)).abs
  have hzero : variation x₀ = 0 := by simp [variation]
  have he : ∀ᶠ x in nhds x₀, variation x < 1 :=
    (hc.tendsto x₀).eventually_lt_const (by rw [hzero]; norm_num)
  filter_upwards [he] with x hx v
  have hb := realQuadratic_abs_bound (a x₀ - a x) v
  rw [realQuadratic_sub] at hb
  change |realQuadratic (a x₀) v - realQuadratic (a x) v| ≤ variation x * squareSum v at hb
  have hh := mul_le_mul_of_nonneg_right hx.le (squareSum_nonneg v)
  have hh' := (le_abs_self (realQuadratic (a x₀) v - realQuadratic (a x) v)).trans hb
  linarith [hlower v]


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phaseProjection (z : ι → ℂ) : Matrix ι ι ℂ :=
  1 + vecMulVec z z

def continuedPhaseMatrix (Q : Matrix ι ι ℂ) (z : ι → ℂ) : Matrix ι ι ℂ :=
  (phaseProjection z)ᵀ * Q * phaseProjection z

omit [Fintype ι] in
lemma phaseProjection_transpose (z : ι → ℂ) :
    (phaseProjection z)ᵀ = phaseProjection z := by
  simp [phaseProjection]

lemma phaseProjection_annihilates (z : ι → ℂ) (hz : z ⬝ᵥ z = -1) :
    phaseProjection z *ᵥ z = 0 := by
  simp [phaseProjection, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hz]

lemma continuedPhaseMatrix_transpose (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q)
    (z : ι → ℂ) : (continuedPhaseMatrix Q z)ᵀ = continuedPhaseMatrix Q z := by
  simp only [continuedPhaseMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, hQ]
  rw [Matrix.mul_assoc]

lemma continuedPhaseMatrix_annihilates (Q : Matrix ι ι ℂ)
    (z : ι → ℂ) (hz : z ⬝ᵥ z = -1) :
    continuedPhaseMatrix Q z *ᵥ z = 0 := by
  rw [continuedPhaseMatrix, ← Matrix.mulVec_mulVec,
    phaseProjection_annihilates z hz, Matrix.mulVec_zero]

lemma continuedPhaseMatrix_eq (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q)
    (z : ι → ℂ) (hQz : Q *ᵥ z = 0) : continuedPhaseMatrix Q z = Q := by
  have hright : Q * phaseProjection z = Q := by
    simp [phaseProjection, Matrix.mul_add, Matrix.mul_vecMulVec, hQz]
  have hleft : (phaseProjection z)ᵀ * Q = Q := by
    have := congrArg Matrix.transpose hright
    simpa only [Matrix.transpose_mul, hQ] using this
  rw [continuedPhaseMatrix, hleft, hright]

omit [Fintype ι] in
@[fun_prop] lemma continuous_phaseProjection : Continuous (phaseProjection (ι := ι)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : ι → ℂ => (1 : Matrix ι ι ℂ) i j + z i * z j)
  fun_prop

lemma continuous_continuedPhaseMatrix (Q : Matrix ι ι ℂ) :
    Continuous (continuedPhaseMatrix Q) := by
  unfold continuedPhaseMatrix
  fun_prop

omit [DecidableEq ι] in
lemma strict_real_quadratic_coercive (A : Matrix ι ι ℝ)
    (hA : ∀ v : ι → ℝ, v ≠ 0 → 0 < realQuadratic A v) :
    ∃ μ > 0, ∀ v, μ * squareSum v ≤ realQuadratic A v := by
  let q : EuclideanSpace ℝ ι → ℝ := fun v => realQuadratic A v
  have hc : Continuous q := by unfold q realQuadratic; fun_prop
  have hp : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 → 0 < q v := by
    intro v hv
    apply hA
    intro he
    apply hv
    ext i
    exact congrFun he i
  obtain ⟨μ, hμ, hb⟩ := continuous_quadratic_coercive q hc
    (fun c v => realQuadratic_hom A c v) hp
  refine ⟨μ, hμ, fun v => ?_⟩
  have h := hb (WithLp.toLp 2 v)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa only [q, squareSum, sq, PiLp.toLp_apply] using h

omit [DecidableEq ι] in
lemma continuous_real_quadratic_coercive_near {T : Type*} [TopologicalSpace T]
    (A : T → Matrix ι ι ℝ) (hA : Continuous A) (t : T) (μ : ℝ) (hμ : 0 < μ)
    (hb : ∀ v, μ * squareSum v ≤ realQuadratic (A t) v) :
    ∀ᶠ s in 𝓝 t, ∀ v, (μ / 2) * squareSum v ≤ realQuadratic (A s) v := by
  let variation : T → ℝ := fun s => ∑ i, ∑ j, |A t i j - A s i j|
  have hc : Continuous variation := by unfold variation; fun_prop
  have hzero : variation t = 0 := by simp [variation]
  have he : ∀ᶠ s in 𝓝 t, variation s < μ / 2 :=
    (hc.tendsto t).eventually_lt_const (by rw [hzero]; positivity)
  filter_upwards [he] with s hs v
  have hab := realQuadratic_abs_bound ((fun i j => A t i j) - (fun i j => A s i j)) v
  rw [realQuadratic_sub] at hab
  change |realQuadratic (A t) v - realQuadratic (A s) v| ≤
    variation s * squareSum v at hab
  have hh := (le_abs_self (realQuadratic (A t) v - realQuadratic (A s) v)).trans hab
  have hv := mul_le_mul_of_nonneg_right hs.le (squareSum_nonneg v)
  linarith [hb v]

theorem phase_matrix_continuation {T : Type*} [TopologicalSpace T]
    (H : T → Matrix ι ι ℝ) (hH : Continuous H)
    (z : T → ι → ℂ) (hz : Continuous z) (t : T)
    (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q) (hQz : Q *ᵥ z t = 0)
    (hgap : ∀ v : ι → ℝ, v ≠ 0 →
      0 < realQuadratic (H t - Q.map Complex.re) v) :
    ∃ κ > 0, ∃ C > 0, ∀ᶠ s in 𝓝 t,
      (continuedPhaseMatrix Q (z s))ᵀ = continuedPhaseMatrix Q (z s) ∧
      (z s ⬝ᵥ z s = -1 → continuedPhaseMatrix Q (z s) *ᵥ z s = 0) ∧
      ‖continuedPhaseMatrix Q (z s)‖ ≤ C ∧
      ∀ v, 4 * κ * squareSum v ≤
        realQuadratic (H s - (continuedPhaseMatrix Q (z s)).map Complex.re) v := by
  let A : T → Matrix ι ι ℝ := fun s =>
    H s - (continuedPhaseMatrix Q (z s)).map Complex.re
  have hA : Continuous A := by
    apply hH.sub
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_re.comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((continuous_continuedPhaseMatrix Q).comp hz)))
  have hAt : A t = H t - Q.map Complex.re := by
    dsimp only [A]
    rw [continuedPhaseMatrix_eq Q hQ _ hQz]
  obtain ⟨μ, hμ, hb⟩ := strict_real_quadratic_coercive _ hgap
  have hlower := continuous_real_quadratic_coercive_near A hA t μ hμ (by
    rw [hAt]; exact hb)
  have hcont := ((continuous_continuedPhaseMatrix Q).comp hz).norm
  have hbound : ∀ᶠ s in 𝓝 t, ‖continuedPhaseMatrix Q (z s)‖ < ‖Q‖ + 1 :=
    (hcont.tendsto t).eventually_lt_const (by
      dsimp only [Function.comp_def]
      rw [continuedPhaseMatrix_eq Q hQ _ hQz]; linarith)
  refine ⟨μ / 8, by positivity, ‖Q‖ + 1, by positivity, ?_⟩
  filter_upwards [hlower, hbound] with s hs hB
  refine ⟨continuedPhaseMatrix_transpose Q hQ _,
    continuedPhaseMatrix_annihilates Q _, hB.le, ?_⟩
  intro v
  convert hs v using 1
  ring


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phaseFormMatrix (U : RealForm (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  fun i j => U (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)

def complexPhaseVector (a b : EuclideanSpace ℝ ι) : ι → ℂ :=
  fun i => (a i : ℂ) + Complex.I * (b i : ℂ)

def complexPhaseMatrix (U D : RealForm (EuclideanSpace ℝ ι)) : Matrix ι ι ℂ :=
  fun i j => (phaseFormMatrix U i j : ℂ) + Complex.I * (phaseFormMatrix D i j : ℂ)

omit [DecidableEq ι] in
lemma phaseFormMatrix_mulVec (U : RealForm (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ ι) (i : ι) :
    (phaseFormMatrix U *ᵥ (fun j => v j)) i = U (EuclideanSpace.basisFun ι ℝ i) v := by
  conv_rhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct,
    phaseFormMatrix, EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
lemma realQuadratic_phaseFormMatrix (U : RealForm (EuclideanSpace ℝ ι))
    (v : ι → ℝ) : realQuadratic (phaseFormMatrix U) v =
      U (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  have heq : realQuadratic (phaseFormMatrix U) v =
      ∑ i, v i * U (EuclideanSpace.basisFun ι ℝ i) w := by
    unfold realQuadratic
    apply Finset.sum_congr rfl
    intro i _
    rw [← phaseFormMatrix_mulVec U w i]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, w]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  change _ = U w w
  conv_rhs => arg 1; rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, EuclideanSpace.basisFun_repr, w]

omit [DecidableEq ι] in
lemma complexPhaseMatrix_re (U D : RealForm (EuclideanSpace ℝ ι)) :
    (complexPhaseMatrix U D).map Complex.re = phaseFormMatrix U := by
  ext i j
  simp [complexPhaseMatrix]

omit [DecidableEq ι] in
lemma complexPhaseMatrix_transpose (U D : RealForm (EuclideanSpace ℝ ι))
    (hU : U.IsSymm) (hD : D.IsSymm) :
    (complexPhaseMatrix U D)ᵀ = complexPhaseMatrix U D := by
  ext i j
  simp only [Matrix.transpose_apply, complexPhaseMatrix, phaseFormMatrix,
    hU.eq (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i),
    hD.eq (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)]

omit [DecidableEq ι] in
lemma complexPhaseMatrix_annihilates {H : RealForm (EuclideanSpace ℝ ι)}
    {a b : EuclideanSpace ℝ ι} (Q : AdmissiblePhaseHessian H a b) :
    complexPhaseMatrix Q.realPart Q.imagPart *ᵥ complexPhaseVector a b = 0 := by
  ext i
  apply Complex.ext
  · simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.zero_re,
      Complex.re_sum, complexPhaseMatrix, complexPhaseVector,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, add_zero, zero_add, sub_zero,
      Complex.mul_im, Finset.sum_sub_distrib]
    change (phaseFormMatrix Q.realPart *ᵥ (fun j => a j)) i -
      (phaseFormMatrix Q.imagPart *ᵥ (fun j => b j)) i = 0
    rw [phaseFormMatrix_mulVec, phaseFormMatrix_mulVec]
    rw [Q.real_symm.eq, Q.imag_symm.eq, Q.column_b, sub_self]
  · simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.zero_im,
      Complex.im_sum, complexPhaseMatrix, complexPhaseVector,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, add_zero, zero_add, sub_zero,
      Complex.mul_im, Finset.sum_add_distrib]
    change (phaseFormMatrix Q.realPart *ᵥ (fun j => b j)) i +
      (phaseFormMatrix Q.imagPart *ᵥ (fun j => a j)) i = 0
    rw [phaseFormMatrix_mulVec, phaseFormMatrix_mulVec]
    rw [Q.real_symm.eq, Q.imag_symm.eq, Q.column_a, add_neg_cancel]

omit [DecidableEq ι] in
lemma complexPhaseVector_square (a b : EuclideanSpace ℝ ι)
    (hab : inner ℝ a b = 0) (hs : inner ℝ b b = 1 + inner ℝ a a) :
    complexPhaseVector a b ⬝ᵥ complexPhaseVector a b = -1 := by
  have ha : (∑ i, a i * a i) = inner ℝ a a := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  have hb : (∑ i, b i * b i) = inner ℝ b b := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  have hab' : (∑ i, a i * b i) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hab
  apply Complex.ext
  · simp only [dotProduct, complexPhaseVector, Complex.re_sum, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero, Complex.mul_im, Complex.neg_re, Complex.one_re,
      Finset.sum_sub_distrib, ha, hb]
    linarith
  · simp only [dotProduct, complexPhaseVector, Complex.im_sum, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero, Complex.mul_im, Complex.neg_im, Complex.one_im,
      Finset.sum_add_distrib, mul_comm, hab']
    norm_num

omit [DecidableEq ι] in
theorem actual_complex_phase_matrix (H : RealForm (EuclideanSpace ℝ ι))
    (hH : H.IsSymm) (a b : EuclideanSpace ℝ ι)
    (hab : inner ℝ a b = 0) (hs : inner ℝ b b = 1 + inner ℝ a a)
    (hstrict : 0 < H a a + H b b) :
    ∃ Q : Matrix ι ι ℂ, Qᵀ = Q ∧ Q *ᵥ complexPhaseVector a b = 0 ∧
      ∃ κ > 0, ∀ v, κ * squareSum v ≤
        realQuadratic (phaseFormMatrix H - Q.map Complex.re) v := by
  obtain ⟨Q⟩ := phase_hessian_exists H hH a b hab hs hstrict
  refine ⟨complexPhaseMatrix Q.realPart Q.imagPart,
    complexPhaseMatrix_transpose _ _ Q.real_symm Q.imag_symm,
    complexPhaseMatrix_annihilates Q, ?_⟩
  apply strict_real_quadratic_coercive
  intro v hv
  rw [complexPhaseMatrix_re]
  have heq : phaseFormMatrix H - phaseFormMatrix Q.realPart =
      phaseFormMatrix (H - Q.realPart) := by ext i j; rfl
  rw [heq, realQuadratic_phaseFormMatrix]
  change 0 < H (WithLp.toLp 2 v) (WithLp.toLp 2 v) -
    Q.realPart (WithLp.toLp 2 v) (WithLp.toLp 2 v)
  apply sub_pos.mpr
  apply Q.gap
  intro he
  apply hv
  ext i
  have hi := congrArg (fun w : EuclideanSpace ℝ ι => w i) he
  exact hi




end YauCounterexamples
end

end OAI
