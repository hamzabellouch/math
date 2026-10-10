import OAI.Probability.InvariantIsing.Fields.FieldFiniteTiltDerivative

namespace OAI

/-! Joint finite-height derivative data for the scalar Ising recursion.
Only the covariance coordinates required by a finite subdivision occur. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

structure FieldFiniteFamily (n : ℕ) (I : Set (Fin n → ℝ)) where
  U : FieldCovariate n → ℝ
  X : FieldCovariate n → ℝ
  XX : FieldCovariate n → ℝ
  P : Fin n → FieldCovariate n → ℝ
  PX : Fin n → FieldCovariate n → ℝ
  PP : Fin n → Fin n → FieldCovariate n → ℝ
  KX : ℝ
  KXX : ℝ
  KP : ℝ
  KPX : ℝ
  KPP : ℝ
  kx_nonneg : 0 ≤ KX
  kxx_nonneg : 0 ≤ KXX
  kp_nonneg : 0 ≤ KP
  kpx_nonneg : 0 ≤ KPX
  kpp_nonneg : 0 ≤ KPP
  mU : Measurable U
  mX : Measurable X
  mXX : Measurable XX
  mP : ∀ i, Measurable (P i)
  mPX : ∀ i, Measurable (PX i)
  mPP : ∀ i j, Measurable (PP i j)
  bX : ∀ p, p.1 ∈ I → |X p| ≤ KX
  bXX : ∀ p, p.1 ∈ I → |XX p| ≤ KXX
  bP : ∀ i p, p.1 ∈ I → |P i p| ≤ KP
  bPX : ∀ i p, p.1 ∈ I → |PX i p| ≤ KPX
  bPP : ∀ i j p, p.1 ∈ I → |PP i j p| ≤ KPP
  derivative : ∀ p, p.1 ∈ I → HasFDerivAt U (fieldFiniteLinear (fun i => P i p) (X p)) p
  derivativeX : ∀ p, p.1 ∈ I → HasFDerivAt X (fieldFiniteLinear (fun i => PX i p) (XX p)) p
  derivativeP : ∀ i p, p.1 ∈ I → HasFDerivAt (P i)
    (fieldFiniteLinear (fun j => PP i j p) (PX i p)) p
  symmetric : ∀ i j p, p.1 ∈ I → PP i j p = PP j i p

def fieldFiniteLogCosh (n : ℕ) (I : Set (Fin n → ℝ)) : FieldFiniteFamily n I where
  U := fun p => Real.log (Real.cosh p.2)
  X := fun p => Real.tanh p.2
  XX := fun p => 1 / Real.cosh p.2 ^ 2
  P := fun _ _ => 0
  PX := fun _ _ => 0
  PP := fun _ _ _ => 0
  KX := 1
  KXX := 1
  KP := 0
  KPX := 0
  KPP := 0
  kx_nonneg := by norm_num
  kxx_nonneg := by norm_num
  kp_nonneg := by norm_num
  kpx_nonneg := by norm_num
  kpp_nonneg := by norm_num
  mU := by fun_prop
  mX := by
    have hm : Measurable Real.tanh := by
      have he : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x := by
        funext x
        exact Real.tanh_eq_sinh_div_cosh x
      rw [he]
      fun_prop
    exact hm.comp measurable_snd
  mXX := by fun_prop
  mP := fun _ => measurable_const
  mPX := fun _ => measurable_const
  mPP := fun _ _ => measurable_const
  bX := fun p _ => field_abs_tanh_le_one p.2
  bXX := fun p _ => field_tanh_second_bound p.2
  bP := fun _ _ _ => by simp
  bPX := fun _ _ _ => by simp
  bPP := fun _ _ _ _ => by simp
  derivative := fun p _ => by
    have h := ((Real.hasDerivAt_cosh p.2).log (Real.cosh_pos p.2).ne').hasFDerivAt.comp p
      hasFDerivAt_snd
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [Real.tanh_eq_sinh_div_cosh, mul_comm]
  derivativeX := fun p _ => by
    have h := (field_hasDerivAt_tanh p.2).hasFDerivAt.comp p hasFDerivAt_snd
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [mul_comm]
  derivativeP := fun _ p _ => by
    convert hasFDerivAt_const (0 : ℝ) p using 1
    apply ContinuousLinearMap.ext
    intro q
    simp
  symmetric := fun _ _ _ _ => rfl

namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma spatial_derivative (h : Fin n → ℝ) (hh : h ∈ I) (z : ℝ) :
    HasDerivAt (fun y => F.U (h, y)) (F.X (h, z)) z := by
  have hmap : HasDerivAt (fun y : ℝ => (h, y)) ((0 : Fin n → ℝ), (1 : ℝ)) z :=
    (hasDerivAt_const z h).prodMk (hasDerivAt_id z)
  have hd := (F.derivative (h, z) hh).comp_hasDerivAt z hmap
  simpa [Function.comp_def] using hd

lemma spatial_mean_derivative (h : Fin n → ℝ) (hh : h ∈ I) (z : ℝ) :
    HasDerivAt (fun y => F.X (h, y)) (F.XX (h, z)) z := by
  have hmap : HasDerivAt (fun y : ℝ => (h, y)) ((0 : Fin n → ℝ), (1 : ℝ)) z :=
    (hasDerivAt_const z h).prodMk (hasDerivAt_id z)
  have hd := (F.derivativeX (h, z) hh).comp_hasDerivAt z hmap
  simpa [Function.comp_def] using hd

lemma growth (h : Fin n → ℝ) (hh : h ∈ I) : HasLinearGrowth (fun y => F.U (h, y)) :=
  field_spatial_linearGrowth F.kx_nonneg (fun y => F.bX (h, y) hh) (F.spatial_derivative h hh)

end FieldFiniteFamily

def fieldFiniteVariance {n : ℕ} (a : ℝ) (v h : Fin n → ℝ) : ℝ :=
  a + ∑ i, v i * h i

def fieldFiniteSlope {n : ℕ} (a : ℝ) (v h : Fin n → ℝ) (i : Fin n) : ℝ :=
  v i / (2 * Real.sqrt (fieldFiniteVariance a v h))

def fieldFiniteCurvature {n : ℕ} (a : ℝ) (v h : Fin n → ℝ) (i j : Fin n) : ℝ :=
  -(v i / 2) * (fieldFiniteVariance a v h)⁻¹ * fieldFiniteSlope a v h j

lemma fieldFiniteCurvature_symmetric {n : ℕ} (a : ℝ) (v h : Fin n → ℝ)
    (i j : Fin n) : fieldFiniteCurvature a v h i j = fieldFiniteCurvature a v h j i := by
  unfold fieldFiniteCurvature fieldFiniteSlope
  ring

end InvariantIsing

end

end OAI
