import OAI.GroupTheory.Kervaire.ScalarPhase

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireTraceCalculus
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a trace of a noncommutative power has its usual scalar form. -/
theorem hasDerivAt_trace_pow (τ : E →L[𝕜] F)
    (hτ : ∀ a b : E, τ (a * b) = τ (b * a))
    {f : 𝕜 → E} {f' : E} {x : 𝕜} (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => τ (f y ^ n)) (n • τ (f x ^ (n - 1) * f')) x := by
  have h := τ.hasFDerivAt.comp_hasDerivAt x (hf.fun_pow' n)
  apply h.congr_deriv
  rw [map_sum]
  have hs : ∀ i ∈ Finset.range n,
      τ (f x ^ (n.pred - i) * f' * f x ^ i) = τ (f x ^ (n - 1) * f') := by
    intro i hi
    rw [hτ (_ * _) _, ← mul_assoc, ← pow_add]
    have hi' := Finset.mem_range.mp hi
    have he : i + (n.pred - i) = n - 1 := by
      simp only [Nat.pred_eq_sub_one]
      omega
    rw [he]
  simp only [Finset.sum_congr rfl hs, Finset.sum_const, Finset.card_range]

section Complex
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Differentiation along the exponential unitary path, before imposing positivity. -/
theorem hasDerivAt_trace_exp_path_pow (τ : B →L[ℂ] ℂ)
    (hτ : ∀ a b : B, τ (a * b) = τ (b * a)) (U C : B) (z : ℂ) (n : ℕ) :
    HasDerivAt (fun y : ℂ => τ ((U * NormedSpace.exp (y • C)) ^ n))
      ((n : ℂ) * τ ((U * NormedSpace.exp (z • C)) ^ n * C)) z := by
  have hp := (hasDerivAt_exp_smul_const C z).const_mul U
  have h := hasDerivAt_trace_pow τ hτ hp n
  by_cases hn : n = 0
  · subst n
    simpa using h
  · apply h.congr_deriv
    rw [nsmul_eq_mul]
    congr 1
    congr 1
    rw [← mul_assoc U, ← mul_assoc, ← pow_succ]
    congr 2
    omega

end Complex

section PositiveTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

local instance : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Tracial positivity applies to a product of positive elements even when they
 do not commute. -/
theorem trace_mul_nonneg (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    {B D : A} (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ (τ (D * B)).re := by
  let S := CFC.sqrt B
  let Q := CFC.sqrt D
  have hS : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  have hQ : star Q = Q := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB
  have hQQ : Q * Q = D := CFC.sqrt_mul_sqrt_self D hD
  have hh : τ (star (Q * S) * (Q * S)) = τ (D * B) := by
    rw [star_mul, hS, hQ]
    calc
      τ (S * Q * (Q * S)) = τ (S * (Q * Q) * S) := by simp only [mul_assoc]
      _ = τ ((D * S) * S) := by rw [hQQ, mul_assoc, ht S]
      _ = τ (D * B) := by rw [mul_assoc, hSS]
  rw [← hh]
  exact hp (Q * S)

/-- The polynomial phase derivative is bounded using positivity, not commutativity
between the path generator and the functional calculus. -/
theorem trace_mul_le (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    {B C : A} (hB : 0 ≤ B) {r : ℝ} (hC : C ≤ r • (1 : A)) :
    (τ (C * B)).re ≤ r * (τ B).re := by
  have h := trace_mul_nonneg τ ht hp hB (sub_nonneg.mpr hC)
  have hs : τ (r • B) = r • τ B := (τ.restrictScalars ℝ).map_smul r B
  simpa only [sub_mul, smul_mul_assoc, one_mul, map_sub, hs,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using h

end PositiveTrace
section RealPath
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The same tracial differentiation formula for a real time parameter. -/
theorem hasDerivAt_trace_real_exp_path_pow (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (U C : A) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => τ ((U * NormedSpace.exp (y • C)) ^ n))
      ((n : ℂ) * τ ((U * NormedSpace.exp (t • C)) ^ n * C)) t := by
  have hp := (hasDerivAt_exp_smul_const C t).const_mul U
  have h := hasDerivAt_trace_pow (τ.restrictScalars ℝ) hτ hp n
  by_cases hn : n = 0
  · subst n
    simpa using h
  · apply h.congr_deriv
    change n • τ ((U * NormedSpace.exp (t • C)) ^ (n - 1) *
      (U * (NormedSpace.exp (t • C) * C))) = _
    rw [nsmul_eq_mul]
    congr 1
    congr 1
    rw [← mul_assoc U, ← mul_assoc, ← pow_succ]
    congr 2
    omega

/-- A regularized logarithm evaluated by a trace. -/
def traceLog (τ : A →L[ℂ] ℂ) (a : ℂ) (U : A) : ℂ :=
  ∑' n : ℕ, (a ^ (n + 1) / (n + 1)) * τ (U ^ (n + 1))

theorem norm_log_coeff_le (a : ℂ) (n : ℕ) :
    ‖a ^ (n + 1) / (n + 1)‖ ≤ ‖a‖ ^ (n + 1) := by
  rw [norm_div, norm_pow]
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [← Nat.cast_add_one, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos n
  exact (div_le_self (pow_nonneg (norm_nonneg a) _) hn)

omit [CompleteSpace A] in
theorem summable_traceLog [NormOneClass A] (τ : A →L[ℂ] ℂ) {a : ℂ} (ha : ‖a‖ < 1)
    {U : A} (hU : ‖U‖ ≤ 1) :
    Summable (fun n : ℕ => (a ^ (n + 1) / (n + 1)) * τ (U ^ (n + 1))) := by
  apply Summable.of_norm_bounded
    (((summable_geometric_of_norm_lt_one ha).norm.comp_injective
      (fun i j h => Nat.add_right_cancel h)).mul_right ‖τ‖)
  intro n
  simp only [norm_pow]
  rw [norm_mul]
  apply mul_le_mul (norm_log_coeff_le a n) ?_ (norm_nonneg _) (by positivity)
  calc
    ‖τ (U ^ (n + 1))‖ ≤ ‖τ‖ * ‖U ^ (n + 1)‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * 1 := by
      gcongr
      exact (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg U) hU (n+1))
    _ = ‖τ‖ := mul_one _

omit [CompleteSpace A] in
theorem norm_trace_pow_mul_le [NormOneClass A] (τ : A →L[ℂ] ℂ)
    {U : A} (hU : ‖U‖ ≤ 1) (C : A) (n : ℕ) :
    ‖τ (U ^ n * C)‖ ≤ ‖τ‖ * ‖C‖ := by
  calc
    ‖τ (U ^ n * C)‖ ≤ ‖τ‖ * ‖U ^ n * C‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * (‖U ^ n‖ * ‖C‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖τ‖ * (1 * ‖C‖) := by
      gcongr
      exact (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg U) hU n)
    _ = ‖τ‖ * ‖C‖ := by rw [one_mul]

/-- Uniform geometric bounds justify differentiating the regularized trace.
Only real time is needed, so the unitary path is uniformly bounded. -/
theorem hasDerivAt_traceLog_path [NormOneClass A] (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (U C : A)
    (hb : ∀ t : ℝ, ‖U * NormedSpace.exp (t • C)‖ ≤ 1)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => traceLog τ a (U * NormedSpace.exp (t • C)))
      (∑' n : ℕ, a ^ (n + 1) * τ ((U * NormedSpace.exp (t • C)) ^ (n + 1) * C)) t := by
  unfold traceLog
  have hs : Summable (fun n : ℕ => ‖a‖ ^ (n+1) * (‖τ‖ * ‖C‖)) :=
    ((summable_geometric_of_lt_one (norm_nonneg a) ha).comp_injective
      (show Function.Injective (fun i : ℕ => i+1) from
        fun i j h => Nat.add_right_cancel h)).mul_right _
  refine hasDerivAt_tsum
    (g := fun (n : ℕ) (x : ℝ) => (a ^ (n+1) / (n+1)) *
      τ ((U * NormedSpace.exp (x • C)) ^ (n+1)))
    (g' := fun (n : ℕ) (x : ℝ) => a ^ (n+1) *
      τ ((U * NormedSpace.exp (x • C)) ^ (n+1) * C))
    (y₀ := (0 : ℝ)) hs ?_ ?_ ?_ t
  · intro n x
    have h := (hasDerivAt_trace_real_exp_path_pow τ hτ U C x (n+1)).const_mul
      (a ^ (n+1) / (n+1))
    apply h.congr_deriv
    rw [Nat.cast_add_one, ← mul_assoc, div_mul_cancel₀]
    exact_mod_cast Nat.succ_ne_zero n
  · intro n x
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (norm_trace_pow_mul_le τ (hb x) C (n+1))
      (pow_nonneg (norm_nonneg a) _)
  · exact summable_traceLog τ ha (hb 0)

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The Hermitian part of the Cayley transform is nonnegative.  This algebraic
Neumann-series argument is valid in every C-star algebra, not just matrices. -/
theorem geometricPart_realpart_nonneg (Z : A) (hZ : ‖Z‖ < 1) :
    0 ≤ 1 + (∑' n : ℕ, Z ^ (n+1)) + star (∑' n : ℕ, Z ^ (n+1)) := by
  let P : A := ∑' n : ℕ, Z ^ n
  have hD : 0 ≤ 1 - star Z * Z := by
    apply sub_nonneg.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg Z)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg Z]
  have hZP : Z * P = P - 1 := by
    exact (geom_series_mul_shift Z hZ).trans (geom_series_succ Z hZ)
  have hpos := star_left_conjugate_nonneg hD P
  have he : star P * (1 - star Z * Z) * P = P + star P - 1 := by
    calc
      star P * (1 - star Z * Z) * P = star P * P - star (Z * P) * (Z * P) := by
        rw [star_mul]
        noncomm_ring
      _ = P + star P - 1 := by
        rw [hZP, star_sub, star_one]
        noncomm_ring
  rw [he] at hpos
  rw [geom_series_succ Z hZ, star_sub, star_one]
  convert hpos using 1
  noncomm_ring

/-- The Cayley positivity gives the exact one-sided phase derivative bound. -/
theorem geometricPart_trace_bound (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {B : A} (hB : 0 ≤ B) (Z : A) (hZ : ‖Z‖ < 1) :
    -2 * (τ ((∑' n : ℕ, Z ^ (n+1)) * B)).re ≤ (τ B).re := by
  let Q : A := ∑' n : ℕ, Z ^ (n+1)
  have hh := trace_mul_nonneg τ ht hp hB (geometricPart_realpart_nonneg Z hZ)
  have hq : τ (star Q * B) = star (τ (Q * B)) := by
    calc
      τ (star Q * B) = τ (B * star Q) := ht _ _
      _ = τ (star (Q * B)) := by rw [star_mul, hB.star_eq]
      _ = star (τ (Q * B)) := hs _
  change 0 ≤ (τ ((1 + Q + star Q) * B)).re at hh
  simp only [add_mul, one_mul, map_add, hq, Complex.add_re,
    Complex.star_def, Complex.conj_re] at hh
  change -2 * (τ (Q * B)).re ≤ (τ B).re
  linarith

end Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
/-- Summing the derivative of the logarithm produces the Cayley series inside
 the algebra. -/
theorem trace_deriv_series (τ : A →L[ℂ] ℂ) {a : ℂ} {W : A} (C : A)
    (haW : ‖a • W‖ < 1) :
    (∑' n : ℕ, a ^ (n+1) * τ (W ^ (n+1) * C)) =
      τ ((∑' n : ℕ, (a • W) ^ (n+1)) * C) := by
  let Φ : A →L[ℂ] ℂ := τ.comp ((ContinuousLinearMap.mul ℂ A).flip C)
  have hsum : Summable (fun n : ℕ => (a • W) ^ (n+1)) :=
    (summable_geometric_of_norm_lt_one haW).comp_injective
      (fun i j h => Nat.add_right_cancel h)
  have he := Φ.map_tsum hsum
  simpa [Φ, smul_pow, smul_mul_assoc] using he.symm

/-- The derivative generator has the normalization used for fractional phase. -/
def phaseVelocity (B : A) : A := ((2 * Real.pi : ℂ) * Complex.I) • B

omit [Nontrivial A] in
/-- Positive generators give a unitary path at all real times. -/
theorem exp_phaseVelocity_mem_unitary {B : A} (hB : 0 ≤ B) (t : ℝ) :
    NormedSpace.exp (t • phaseVelocity B) ∈ unitary A := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [phaseVelocity, star_smul, hB.star_eq]

/-- A smooth trace approximation to the fractional spectral phase. -/
def smoothTrace (τ : A →L[ℂ] ℂ) (a : ℂ) (U : A) : ℝ :=
  (τ 1).re / 2 - (traceLog τ a U).im / Real.pi

/-- The exact derivative of the regularized phase along a positive path. -/
theorem hasDerivAt_smoothTrace_path (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B)))
      (-2 * (τ ((∑' n : ℕ, (a • (U * NormedSpace.exp
        (t • phaseVelocity B))) ^ (n+1)) * B)).re) t := by
  have hb : ∀ t : ℝ, ‖U * NormedSpace.exp (t • phaseVelocity B)‖ ≤ 1 := by
    intro t
    exact (CStarRing.norm_of_mem_unitary ((unitary A).mul_mem hU
      (exp_phaseVelocity_mem_unitary hB t))).le
  have hn : ‖a • (U * NormedSpace.exp (t • phaseVelocity B))‖ < 1 := by
    rw [norm_smul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hb t)) ha
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_traceLog_path τ ht U (phaseVelocity B) hb ha t)
  have hd := (h.div_const Real.pi).const_sub ((τ 1).re / 2)
  apply hd.congr_deriv
  rw [trace_deriv_series τ (phaseVelocity B) hn]
  change -((τ ((∑' n : ℕ, (a • (U * NormedSpace.exp
    (t • phaseVelocity B))) ^ (n+1)) * phaseVelocity B)).im / Real.pi) = _
  have hev (T : A) : (τ (T * phaseVelocity B)).im =
      (2 * Real.pi) * (τ (T * B)).re := by
    simp [phaseVelocity, Complex.mul_im]
  rw [hev]
  field_simp

/-- The one-sided derivative estimate for the smooth regularization. -/
theorem deriv_smoothTrace_path_le (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    deriv (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B))) t ≤ (τ B).re := by
  rw [(hasDerivAt_smoothTrace_path τ ht hU hB ha t).deriv]
  apply geometricPart_trace_bound τ ht hp hs hB
  rw [norm_smul, CStarRing.norm_of_mem_unitary ((unitary A).mul_mem hU
    (exp_phaseVelocity_mem_unitary hB t)), mul_one]
  exact ha

/-- Integrating the regularized derivative bound over the unit path. -/
theorem smoothTrace_mul_exp_le (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) :
    smoothTrace τ a (U * NormedSpace.exp (phaseVelocity B)) ≤
      smoothTrace τ a U + (τ B).re := by
  have hd := fun t => hasDerivAt_smoothTrace_path τ ht hU hB ha t
  have hc : Continuous (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B))) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hh := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    hc.continuousOn (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t _ => deriv_smoothTrace_path_le τ ht hp hs hU hB ha t)
    0 (by simp) 1 (by simp) (by norm_num)
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one, one_smul, sub_zero,
    sub_le_iff_le_add, add_comm] using hh

end KervaireTraceCalculus

end

end OAI
