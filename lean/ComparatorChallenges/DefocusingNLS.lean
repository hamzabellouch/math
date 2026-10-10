import Mathlib

namespace OAI

/-! # Stable self-similar blowup on the twelve-dimensional torus

Theorem 1.1 and Corollary 1.2 of OpenAI, *Stable self-similar blowup for a
supercritical defocusing Schrödinger equation on the torus* (September 2026).
The Sobolev space is represented by its weighted square-summable Fourier
coefficients. The maximal flow is the union of classical interaction solutions.
-/

noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexConjugate ContDiff

attribute [local instance 2000] instPolynormableSpace
  TopologicalSpace.PseudoMetrizableSpace.regularSpace

namespace DefocusingNLS

noncomputable def frequencyLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 12)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis)

instance : DiscreteTopology frequencyLattice := by
  unfold frequencyLattice
  infer_instance

instance : IsZLattice ℝ frequencyLattice := by
  unfold frequencyLattice
  infer_instance

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def complexGaussian (v : ℝ≥0) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
    Complex.equivRealProdCLM.symm

instance complexGaussian_isProbabilityMeasure (v : ℝ≥0) :
    IsProbabilityMeasure (complexGaussian v) := by
  unfold complexGaussian
  infer_instance

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def fourierGaussianLaw : Measure (frequencyLattice → ℂ) :=
  Measure.infinitePi (fun _ : frequencyLattice => complexGaussian (1 / 2))

noncomputable def sobolevVariance (k α : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k - α)

noncomputable def weightedGaussianCoefficient (k α : ℝ)
    (g : frequencyLattice → ℂ) (n : frequencyLattice) : ℂ :=
  Real.sqrt (sobolevVariance k α n) • g n

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

abbrev FourierL2 := lp (fun _ : frequencyLattice => ℂ) (2 : ℝ≥0∞)

instance : MeasurableSpace FourierL2 := borel FourierL2
instance : BorelSpace FourierL2 := ⟨rfl⟩

noncomputable def weightedGaussianVector (k α : ℝ)
    (g : frequencyLattice → ℂ) : FourierL2 :=
  ∑' n, lp.single 2 n (weightedGaussianCoefficient k α g n)

noncomputable def sobolevFourierCoefficient (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) : ℂ :=
  (1 + ‖n‖ ^ 2) ^ (-k / 2) • f n

noncomputable def weightedGaussianLaw (k α : ℝ) : Measure FourierL2 :=
  fourierGaussianLaw.map (weightedGaussianVector k α)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

abbrev SchrodingerTorus := Fin 12 → AddCircle (2 * Real.pi)

instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

noncomputable def frequencyCoordinates (n : frequencyLattice) : Fin 12 → ℤ :=
  ((EuclideanSpace.basisFun (Fin 12) ℝ).toBasis.restrictScalars ℤ).repr n

noncomputable def torusCharacter (n : frequencyLattice) : C(SchrodingerTorus, ℂ) where
  toFun x := ∏ j : Fin 12, fourier (frequencyCoordinates n j) (x j)
  continuous_toFun := by fun_prop

noncomputable def sobolevTorusTerm (k : ℝ) (f : FourierL2) (n : frequencyLattice) :
    C(SchrodingerTorus, ℂ) :=
  sobolevFourierCoefficient k f n • torusCharacter n

noncomputable def sobolevTorusFunction (k : ℝ) (f : FourierL2) : C(SchrodingerTorus, ℂ) :=
  ∑' n, sobolevTorusTerm k f n

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def sobolevProductWeight (k : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k / 2)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def sobolevProductCoefficient (k : ℝ) (f g : FourierL2)
    (n : frequencyLattice) : ℂ :=
  ∑' m, sobolevFourierCoefficient k f m * sobolevFourierCoefficient k g (n - m)

noncomputable def sobolevProduct (k : ℝ) (_hk : 6 < k) (f g : FourierL2) : FourierL2 :=
  ⟨fun n => (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f g n,
    by sorry⟩

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def fourierConjugate (f : FourierL2) : FourierL2 :=
  ⟨fun n => conj (f (-n)), by
    apply memℓp_gen
    simpa only [Complex.norm_conj, Function.comp_def, Equiv.neg_apply] using
      (Equiv.neg frequencyLattice).summable_iff.mpr
        ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def sobolevOddPower (k : ℝ) (hk : 6 < k) : ℕ → FourierL2 → FourierL2
  | 0, f => f
  | m + 1, f => sobolevProduct k hk
      (sobolevProduct k hk (sobolevOddPower k hk m f) (fourierConjugate f)) f

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def schrodingerMultiplier (t : ℝ) (n : frequencyLattice) : ℂ :=
  Complex.exp (-Complex.I * ((t * ‖n‖ ^ 2 : ℝ) : ℂ))

noncomputable def schrodingerFlow (t : ℝ) : FourierL2 →ₗᵢ[ℂ] FourierL2 where
  toFun f := ⟨fun n => schrodingerMultiplier t n * f n, by
    apply (lp.memℓp f).mono'
    intro n
    simp only [norm_mul, schrodingerMultiplier, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero,
      sub_zero, Real.exp_zero, one_mul]
    exact le_rfl⟩
  map_add' f g := by
    ext n
    change schrodingerMultiplier t n * (f n + g n) =
      schrodingerMultiplier t n * f n + schrodingerMultiplier t n * g n
    exact mul_add _ _ _
  map_smul' c f := by ext n; simp [mul_left_comm]
  norm_map' f := by
    have hm (n : frequencyLattice) : ‖schrodingerMultiplier t n‖ = 1 := by
      simp only [schrodingerMultiplier, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
        Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]
    apply le_antisymm
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖schrodingerMultiplier t n * f n‖ ≤ ‖f n‖
      rw [norm_mul, hm, one_mul]
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖f n‖ ≤ ‖schrodingerMultiplier t n * f n‖
      rw [norm_mul, hm, one_mul]


run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def fourierContraction (m : frequencyLattice → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1) : FourierL2 →L[ℂ] FourierL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => m n * f n, (lp.memℓp f).mono' (by
        intro n
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f n)))⟩
      map_add' := by
        intro f g
        ext n
        change m n * (f n + g n) = m n * f n + m n * g n
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        ext n
        change m n * (c * f n) = c * (m n * f n)
        ring }
    1 (by
      intro f
      simp only [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖m n * f n‖ ≤ ‖f n‖
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f n)))

noncomputable def lowerSobolevInclusion : FourierL2 →L[ℂ] FourierL2 :=
  fourierContraction (fun n => (((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ)) (by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _)))

noncomputable def lowerSobolevGenerator : FourierL2 →L[ℂ] FourierL2 :=
  fourierContraction (fun n => -Complex.I * (((‖n‖ ^ 2 / (1 + ‖n‖ ^ 2)) : ℝ) : ℂ)) (by
    intro n
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith [sq_nonneg ‖n‖]))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def schrodingerInteractionField (k : ℝ) (hk : 6 < k) (m : ℕ)
    (t : ℝ) (f : FourierL2) : FourierL2 :=
  (-Complex.I) • schrodingerFlow (-t) (sobolevOddPower k hk m (schrodingerFlow t f))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

structure SobolevInteractionPatch (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) where
  left : ℝ
  right : ℝ
  left_neg : left < 0
  right_pos : 0 < right
  curve : ℝ → FourierL2
  initial : curve 0 = f₀
  solves : ∀ t ∈ Ioo left right,
    HasDerivAt curve (schrodingerInteractionField k hk m t (curve t)) t

def maximalSobolevInteractionDomain (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) : Set ℝ :=
  ⋃ P : SobolevInteractionPatch k hk m f₀, Ioo P.left P.right

noncomputable def maximalSobolevInteractionFlow (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) (t : ℝ) : FourierL2 := by
  classical
  exact if ht : t ∈ maximalSobolevInteractionDomain k hk m f₀ then
    (Classical.choose (mem_iUnion.mp ht)).curve t
  else 0

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def maximalSobolevSchrodingerFlow (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) (t : ℝ) : FourierL2 :=
  schrodingerFlow t (maximalSobolevInteractionFlow k hk m f₀ t)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def IsClassicalDefocusingFlow (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) : Prop :=
  let u := maximalSobolevSchrodingerFlow k hk m f
  let D := maximalSobolevInteractionDomain k hk m f
  u 0 = f ∧ ContinuousOn u D ∧
    ContDiffOn ℝ 1 (fun t => lowerSobolevInclusion (u t)) D ∧
    ∀ t ∈ D, HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) - Complex.I • lowerSobolevInclusion
        (sobolevOddPower k hk m (u t))) t

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def HasFiniteTimeSelfSimilarBlowup (k : ℝ) (hk : 6 < k) (m : ℕ)
    (a : ℝ) (f : FourierL2) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ x : SchrodingerTorus, ∃ c : ℝ, 0 < c ∧
    Ico 0 T ⊆ maximalSobolevInteractionDomain k hk m f ∧
    BddAbove (maximalSobolevInteractionDomain k hk m f) ∧
    sSup (maximalSobolevInteractionDomain k hk m f) = T ∧
    Tendsto (fun t => (T - t) ^ a *
      ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k hk m f t) x‖)
      (𝓝[<] T) (𝓝 c) ∧
    ¬ ContinuousWithinAt (maximalSobolevSchrodingerFlow k hk m f) (Iio T) T

attribute [local irreducible] HasFiniteTimeSelfSimilarBlowup IsClassicalDefocusingFlow
  maximalSobolevInteractionDomain

/-- Theorem 1.1: arbitrarily large odd powers admit a nonempty open family of
classical solutions with finite-time self-similar blowup on the twelve-torus. -/
theorem stable_blowup (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧ ∀ f ∈ U,
        IsClassicalDefocusingFlow k (by linarith) ((p - 1) / 2) f ∧
        HasFiniteTimeSelfSimilarBlowup k (by linarith) ((p - 1) / 2)
          (1 / ((p : ℝ) - 1)) f := by
  sorry

/-- Corollary 1.2: for every permitted Gaussian Fourier decay exponent,
the same open blowup family has positive Gaussian probability. -/
theorem gaussian_blowup (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧
      (∀ f ∈ U, IsClassicalDefocusingFlow k (by linarith) ((p - 1) / 2) f ∧
        HasFiniteTimeSelfSimilarBlowup k (by linarith) ((p - 1) / 2)
          (1 / ((p : ℝ) - 1)) f) ∧
      ∀ α : ℝ, (k : ℝ) + 6 < α →
        (∀ᵐ g ∂fourierGaussianLaw, Memℓp (weightedGaussianCoefficient k α g) 2) ∧
        (∀ᵐ g ∂fourierGaussianLaw, ∀ n,
          sobolevFourierCoefficient k (weightedGaussianVector k α g) n =
            (1 + ‖n‖ ^ 2) ^ (-α / 2) • g n) ∧
        0 < weightedGaussianLaw k α U := by
  sorry

/-- In particular, Gaussian data are not almost surely globally continuable. -/
theorem gaussian_not_almost_sure_global (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∀ α : ℝ, (k : ℝ) + 6 < α →
        ¬ ∀ᵐ f ∂weightedGaussianLaw k α,
          maximalSobolevInteractionDomain k (by linarith) ((p - 1) / 2) f = univ := by
  sorry

end DefocusingNLS

end

end OAI
