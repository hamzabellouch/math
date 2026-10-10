import Mathlib
import OAI.Probability.SKGap.Stability.StableFields

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap

def tapPotential {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : ℝ :=
  (∑ i, (y i * magnetization y i - log (cosh (y i)))) -
    (∑ i, h i * magnetization y i) -
    (1/2:ℝ) * quadraticForm J (magnetization y) +
    (j/2) * vectorSqNorm (magnetization y) -
    (j/(4*n)) * vectorSqNorm (magnetization y)^2

def weightedTap {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : Field n := fun i => spinVariance y i * tapField j J h y i

lemma singlePotential_hasDerivAt (x : ℝ) :
    HasDerivAt (fun z : ℝ => z * tanh z - log (cosh z))
      (x*(1-tanh x^2)) x := by
  have hc : cosh x ≠ 0 := (cosh_pos x).ne'
  convert! ((hasDerivAt_id x).mul (hasDerivAt_tanh x)).sub
    ((hasDerivAt_cosh x).log hc) using 1
  simp only [id_eq, one_mul, tanh_eq_sinh_div_cosh]
  ring

lemma quadraticForm_derivative_algebra {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (m w : Field n) :
    (∑ i, ∑ k, (w i * J i k * m k + m i * J i k * w k)) =
      2 * ∑ i, w i * (∑ k, J i k * m k) := by
  simp only [Finset.sum_add_distrib]
  have he : (∑ i, ∑ k, m i * J i k * w k) = ∑ i, ∑ k, w i * J i k * m k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hJ.apply k i]
    ring
  rw [he]
  simp only [← Finset.mul_sum, mul_assoc]
  ring

lemma quadratic_magnetization_hasFDerivAt {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (y : Field n) :
    HasFDerivAt (fun z => quadraticForm J (magnetization z))
      (2 • ∑ i, (spinVariance y i * (∑ k, J i k * magnetization y k)) •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  have hd := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((magnetization_hasFDerivAt y i).mul_const (J i k)).mul
        (magnetization_hasFDerivAt y k)))
  convert! hd using 1
  · ext z
    simp only [quadraticForm, Finset.sum_apply, Pi.mul_apply]
  ext v
  simp only [_root_.smul_apply, _root_.sum_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul]
  have he := quadraticForm_derivative_algebra hJ (magnetization y)
    (fun i => spinVariance y i * v i)
  calc
    _ = 2 * ∑ i, (spinVariance y i * v i) * (∑ k, J i k * magnetization y k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∑ k, ((spinVariance y i * v i) * J i k * magnetization y k +
        magnetization y i * J i k * (spinVariance y k * v k)) := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma squared_magnetization_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt (fun z => vectorSqNorm (magnetization z))
      (∑ i, (2*magnetization y i*spinVariance y i) •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  convert! (HasFDerivAt.sum (u := Finset.univ)
    (fun i _ => (magnetization_hasFDerivAt y i).pow 2)) using 1
  · ext z
    simp only [vectorSqNorm, Finset.sum_apply]
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Nat.reduceSub, pow_one]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tapPotential_hasFDerivAt {n : ℕ} (j : ℝ)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h y : Field n) :
    HasFDerivAt (tapPotential j J h)
      (∑ i, weightedTap j J h y i •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  have hsinglei (i : Fin n) :
      HasFDerivAt (fun z : Field n => z i * tanh (z i) - log (cosh (z i)))
        ((y i*(1-tanh (y i)^2)) • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i y).mul
      (magnetization_hasFDerivAt y i)).sub
      (((hasFDerivAt_apply (𝕜 := ℝ) i y).cosh).log (cosh_pos (y i)).ne')
    convert! hd using 1
    ext v
    simp only [_root_.smul_apply, _root_.sub_apply, _root_.add_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, spinVariance, magnetization,
      tanh_eq_sinh_div_cosh]
    ring
  have hsingle := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hsinglei i)
  have hext := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (magnetization_hasFDerivAt y i).const_mul (h i))
  have hquad := (quadratic_magnetization_hasFDerivAt hJ y).const_mul (1/2:ℝ)
  have hsq := (squared_magnetization_hasFDerivAt y).const_mul (j/2)
  have hfour := ((squared_magnetization_hasFDerivAt y).pow 2).const_mul (j/(4*n))
  convert! (((hsingle.sub hext).sub hquad).add hsq).sub hfour using 1
  · ext z
    simp only [tapPotential, Finset.sum_apply, Pi.sub_apply, Pi.add_apply, magnetization]
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  simp only [weightedTap, tapField, onsager, overlap, vectorSqNorm, spinVariance,
    magnetization]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma contDiff_tanh_SK {m : WithTop ℕ∞} : ContDiff ℝ m tanh := by
  have he : tanh = sinh / cosh := funext tanh_eq_sinh_div_cosh
  rw [he]
  exact contDiff_sinh.div contDiff_cosh (fun x => (cosh_pos x).ne')

lemma magnetization_contDiff {n : ℕ} {m : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ m (fun y : Field n => magnetization y i) :=
  contDiff_tanh_SK.comp (contDiff_apply ℝ ℝ i)

lemma spinVariance_contDiff {n : ℕ} {m : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ m (fun y : Field n => spinVariance y i) :=
  contDiff_const.sub ((magnetization_contDiff i).pow 2)

lemma overlap_contDiff {n : ℕ} {m : WithTop ℕ∞} :
    ContDiff ℝ m (overlap (n := n)) :=
  (ContDiff.sum (fun i _ => (magnetization_contDiff i).pow 2)).div_const _

lemma tapField_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (tapField j J h) := by
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_apply ℝ ℝ i).sub contDiff_const).add
    ((contDiff_const.mul (contDiff_const.sub overlap_contDiff)).mul
      (magnetization_contDiff i)) |>.sub
        (ContDiff.sum (fun k _ => contDiff_const.mul (magnetization_contDiff k)))

lemma weightedTap_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (weightedTap j J h) := by
  apply contDiff_pi.mpr
  intro i
  exact (spinVariance_contDiff i).mul (contDiff_pi.mp (tapField_contDiff j J h) i)

abbrev EField (n : ℕ) := EuclideanSpace ℝ (Fin n)

def tapPotentialE {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y : EField n) : ℝ := tapPotential j J h (WithLp.ofLp y)

def weightedTapE {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y : EField n) : EField n :=
  WithLp.toLp 2 (weightedTap j J h (WithLp.ofLp y))

lemma weightedTapE_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (weightedTapE j J h) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.contDiff.comp
    ((weightedTap_contDiff j J h).comp
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).contDiff)

lemma tapPotentialE_hasFDerivAt {n : ℕ} (j : ℝ)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h : Field n) (y : EField n) :
    HasFDerivAt (tapPotentialE j J h) (innerSL ℝ (weightedTapE j J h y)) y := by
  have hd := (tapPotential_hasFDerivAt j hJ h (WithLp.ofLp y)).comp y
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).hasFDerivAt
  convert! hd using 1
  ext v
  simp only [innerSL_apply_apply, weightedTapE, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, ContinuousLinearMap.comp_apply,
    _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change v i * weightedTap j J h (WithLp.ofLp y) i =
    weightedTap j J h (WithLp.ofLp y) i * v i
  ring

def weightedJacobianMap {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y : Field n) : Field n →L[ℝ] Field n :=
  ContinuousLinearMap.pi (fun i => spinVariance y i •
    ((ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ).comp
      (fieldJacobian j J y).mulVecLin.toContinuousLinearMap))

lemma weightedTap_hasFDerivAt_zero {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n)
    (hz : tapField j J h y = 0) :
    HasFDerivAt (weightedTap j J h) (weightedJacobianMap j J y) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hV := ((spinVariance_contDiff i (m := 1)).differentiable (by norm_num) y).hasFDerivAt
  have hF := hasFDerivAt_pi'.mp (tapField_hasFDerivAt j J h y) i
  have hzi : tapField j J h y i = 0 := congrFun hz i
  have hd := hV.mul hF
  simp only [hzi, zero_smul, add_zero] at hd
  convert! hd using 1

lemma weightedTapE_fderiv_zero {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y v : EField n)
    (hz : tapField j J h (WithLp.ofLp y) = 0) (i : Fin n) :
    (fderiv ℝ (weightedTapE j J h) y v) i =
      spinVariance (WithLp.ofLp y) i *
        ((fieldJacobian j J (WithLp.ofLp y)).mulVec (WithLp.ofLp v)) i := by
  let e := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hd := e.symm.hasFDerivAt.comp y
    ((weightedTap_hasFDerivAt_zero j J h (WithLp.ofLp y) hz).comp y e.hasFDerivAt)
  have he : fderiv ℝ (weightedTapE j J h) y =
      e.symm.toContinuousLinearMap.comp ((weightedJacobianMap j J (WithLp.ofLp y)).comp
        e.toContinuousLinearMap) := hd.fderiv
  rw [he]
  rfl

lemma weighted_jacobian_quadratic_form {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (∑ i, v i * (spinVariance y i * ((fieldJacobian j J y).mulVec v) i)) =
      quadraticForm (fieldHessian j J y (spinVariance y)) (sqrtVarianceMul y v) := by
  simp only [Matrix.mulVec, dotProduct, quadraticForm, sqrtVarianceMul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hi := sq_sqrt (spinVariance_pos y i).le
  calc
    _ = (sqrt (spinVariance y i) * v i) *
        (sqrt (spinVariance y i)*fieldJacobian j J y i k) * v k := by
      conv_lhs => rw [← hi]
      ring
    _ = _ := by rw [← fieldHessian_variance_intertwine]; ring

lemma weightedTapE_derivative_energy {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y v : EField n)
    (hz : tapField j J h (WithLp.ofLp y) = 0) :
    inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) =
      quadraticForm (fieldHessian j J (WithLp.ofLp y) (spinVariance (WithLp.ofLp y)))
        (sqrtVarianceMul (WithLp.ofLp y) (WithLp.ofLp v)) := by
  rw [← weighted_jacobian_quadratic_form]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedTapE_fderiv_zero j J h y v hz i]
  ring

lemma spinVariance_eq_inv_cosh_sq {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i = 1 / cosh (y i)^2 := by
  simp only [spinVariance, magnetization, tanh_eq_sinh_div_cosh]
  field_simp
  exact cosh_sq_sub_sinh_sq _

lemma spinVariance_bound_on_box {n : ℕ} (y : Field n) {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ i, |y i| ≤ R) (i : Fin n) :
    1 / cosh R^2 ≤ spinVariance y i := by
  rw [spinVariance_eq_inv_cosh_sq]
  apply one_div_le_one_div_of_le (sq_pos_of_pos (cosh_pos (y i)))
  have h : cosh (y i) ≤ cosh R := cosh_le_cosh.mpr
    (by simpa only [abs_of_nonneg hR] using hy i)
  exact pow_le_pow_left₀ (cosh_pos (y i)).le h 2

lemma tapField_shift_bound {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) (i : Fin n) :
    |y i - tapField j J h y i| ≤ |h i| + j + ∑ k, |J i k| := by
  have hm (k : Fin n) : |magnetization y k| ≤ 1 := by
    exact (abs_lt.mpr ⟨neg_one_lt_tanh _, tanh_lt_one _⟩).le
  have hB0 : 0 ≤ onsager j y := mul_nonneg hj (sub_nonneg.mpr (overlap_lt_one hn y).le)
  have hBj : onsager j y ≤ j := by
    dsimp [onsager]
    nlinarith [overlap_nonneg y]
  have hBm : |onsager j y * magnetization y i| ≤ j := by
    rw [abs_mul, abs_of_nonneg hB0]
    exact (mul_le_of_le_one_right hB0 (hm i)).trans hBj
  have hJm : |∑ k, J i k * magnetization y k| ≤ ∑ k, |J i k| := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hm k))
  have he : y i-tapField j J h y i = h i-onsager j y*magnetization y i +
      ∑ k, J i k*magnetization y k := by simp only [tapField]; ring
  rw [he]
  have hs : |h i-onsager j y*magnetization y i| ≤ |h i|+j := by
    calc
      _ ≤ |h i|+|onsager j y*magnetization y i| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (h i) (-(onsager j y*magnetization y i))
      _ ≤ _ := add_le_add_right hBm _
  exact (abs_add_le _ _).trans (add_le_add hs hJm)

lemma exists_tapBox_radius {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : Field n, ∀ i, |y i-tapField j J h y i| ≤ R := by
  let b := fun i => |h i| + j + ∑ k, |J i k|
  have hb (i : Fin n) : 0 ≤ b i := by dsimp [b]; positivity
  refine ⟨1+∑ i, b i, by positivity, fun y i => ?_⟩
  exact (tapField_shift_bound hn hj J h y i).trans
    ((Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ i)).trans (by linarith))

lemma weightedTap_step_box {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) {R ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1)
    (hbound : ∀ i, |y i-tapField j J h y i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    ∀ i, |(y-ε • weightedTap j J h y) i| ≤ R := by
  intro i
  let a := ε*spinVariance y i
  have ha0 : 0 ≤ a := mul_nonneg hε.1 (spinVariance_pos y i).le
  have ha1 : a ≤ 1 := (mul_le_mul_of_nonneg_left (spinVariance_le_one y i) hε.1).trans
    (by simpa using hε.2)
  have he : (y-ε • weightedTap j J h y) i =
      (1-a)*y i + a*(y i-tapField j J h y i) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, weightedTap, a]
    ring
  rw [he]
  calc
    _ ≤ |(1-a)*y i| + |a*(y i-tapField j J h y i)| := abs_add_le _ _
    _ = (1-a)*|y i| + a*|y i-tapField j J h y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (1-a)*R+a*R := add_le_add
      (mul_le_mul_of_nonneg_left (hy i) (sub_nonneg.mpr ha1))
      (mul_le_mul_of_nonneg_left (hbound i) ha0)
    _ = R := by ring

def fieldBoxE (n : ℕ) (R : ℝ) : Set (EField n) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' Metric.closedBall (0:Field n) R

lemma mem_fieldBoxE {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (y : EField n) :
    y ∈ fieldBoxE n R ↔ ∀ i, |y i| ≤ R := by
  simp only [fieldBoxE, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change ∀ i, |x i| ≤ R
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hR).mp hn
  · intro hy
    refine ⟨WithLp.ofLp y, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    exact hy

lemma isCompact_fieldBoxE (n : ℕ) (R : ℝ) : IsCompact (fieldBoxE n R) :=
  (isCompact_closedBall (0:Field n) R).image
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.continuous

lemma convex_fieldBoxE (n : ℕ) (R : ℝ) : Convex ℝ (fieldBoxE n R) :=
  (convex_closedBall (0:Field n) R).linear_image
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.toLinearMap

lemma nonempty_fieldBoxE (n : ℕ) {R : ℝ} (hR : 0 ≤ R) : (fieldBoxE n R).Nonempty :=
  ⟨0, (mem_fieldBoxE hR 0).mpr (fun _ => by simpa using hR)⟩

theorem lyapunov_eventually_hits {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x)
    {U : Set X} (hU : IsOpen U) (hfix : ∀ x, T x = x → x ∈ U) (x : X) :
    ∃ n : ℕ, T^[n] x ∈ U := by
  by_contra! hnever
  have hK : IsCompact Uᶜ := hU.isClosed_compl.isCompact
  have hne : Uᶜ.Nonempty := ⟨x, by simpa using hnever 0⟩
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne (hφ.sub (hφ.comp hT)).continuousOn
  let δ := φ y - φ (T y)
  have hd : 0 < δ := sub_pos.mpr (hstrict y (fun h => hy (hfix y h)))
  have hdec (n : ℕ) : δ ≤ φ (T^[n] x) - φ (T (T^[n] x)) :=
    hmin (hnever n)
  obtain ⟨m, hm⟩ := isCompact_univ.bddBelow_image hφ.continuousOn
  have hlower (z : X) : m ≤ φ z := hm ⟨z, mem_univ _, rfl⟩
  have hbound (n : ℕ) : φ (T^[n] x) ≤ φ x - (n:ℝ)*δ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have h := hdec n
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((φ x - m)/δ)
  have hn' : φ x - m < (n:ℝ)*δ := (div_lt_iff₀ hd).mp hn
  have hb := hbound n
  have hl := hlower (T^[n] x)
  linarith

theorem lyapunov_fixed_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (T : X → X) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x) : ∃ x, T x = x := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hφ.continuousOn
  refine ⟨x, by_contra fun h => ?_⟩
  exact (not_lt_of_ge (hx (mem_univ (T x)))) (hstrict x h)

section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

def attractionBasin (p : X) : Set X :=
  {x | Tendsto (fun n : ℕ => T^[n] x) atTop (𝓝 p)}

lemma mem_attractionBasin_iterate_iff (p x : X) (k : ℕ) :
    T^[k] x ∈ attractionBasin T p ↔ x ∈ attractionBasin T p := by
  simpa only [attractionBasin, mem_ofPred_eq, iterate_add_apply] using
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => T^[n] x) (l := 𝓝 p) k)

lemma fixed_mem_attractionBasin {p : X} (hp : T p = p) : p ∈ attractionBasin T p := by
  simp only [attractionBasin, mem_ofPred_eq, iterate_fixed hp]
  exact tendsto_const_nhds

end Basins
end SKGap
end
end

end OAI
