import OAI.Probability.InvariantIsing.Cavity.CavityFactorBound
import OAI.Probability.InvariantIsing.Cavity.CavitySoftCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffNormalizer

namespace OAI

/-! Bounded continuous cutoffs of the actual cavity factor. The radius
cutoff equals one on the inner ball and vanishes outside the next ball. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFactorSize {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  cavityMatrixMass K + cavityMatrixMass L + cavityMatrixMass C

lemma cavityFactorSize_nonneg {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ cavityFactorSize K L C := add_nonneg
      (add_nonneg (cavityMatrixMass_nonneg K) (cavityMatrixMass_nonneg L)) (cavityMatrixMass_nonneg C)

lemma continuous_cavityLogFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    Continuous (fun y : EuclideanSpace ℝ (Fin d) => cavityLogFactor K L C y ε) := by
  unfold cavityLogFactor cavityQuadratic
  fun_prop

def cavityCappedFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) (T : ℝ) :
    EuclideanSpace ℝ (Fin d) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => Real.exp (min (cavityLogFactor K L C y ε) T))
    (Real.continuous_exp.comp ((continuous_cavityLogFactor K L C ε).min continuous_const)) (Real.exp T)
    (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (min_le_right _ _))

def cavityContinuousFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : Spin n) (B : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (cavityLogFactor K L C y ε) * cavityRadialCutoff B ‖y‖

lemma continuous_cavityContinuousFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) (B : ℝ) :
    Continuous (cavityContinuousFactor K L C ε B) :=
  (Real.continuous_exp.comp (continuous_cavityLogFactor K L C ε)).mul
    ((continuous_cavityRadialCutoff B).comp continuous_norm)

lemma cavityContinuousFactor_nonneg {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : Spin n) (B : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ cavityContinuousFactor K L C ε B y :=
  mul_nonneg (Real.exp_pos _).le (cavityRadialCutoff_mem B ‖y‖).1

lemma cavityContinuousFactor_le {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : Spin n) {B : ℝ} (_hB : 0 ≤ B) (y : EuclideanSpace ℝ (Fin d)) :
    cavityContinuousFactor K L C ε B y ≤
      Real.exp (cavityFactorSize K L C * (1 + (B + 1)^2)) := by
  by_cases hy : B + 1 ≤ ‖y‖
  · simp only [cavityContinuousFactor, cavityRadialCutoff_eq_zero hy, mul_zero]
    exact (Real.exp_pos _).le
  · have hn : ‖y‖^2 ≤ (B + 1)^2 := pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hy) 2
    have hg := (le_abs_self (cavityLogFactor K L C y ε)).trans (cavity_logFactor_growth K L C y ε)
    have hs := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hn) (cavityFactorSize_nonneg K L C)
    change Real.exp (cavityLogFactor K L C y ε) * cavityRadialCutoff B ‖y‖ ≤ _
    calc
      _ ≤ Real.exp (cavityLogFactor K L C y ε) * 1 :=
        mul_le_mul_of_nonneg_left (cavityRadialCutoff_mem B ‖y‖).2 (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact Real.exp_le_exp.mpr (hg.trans hs)

def cavityBoundedFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : Spin n) {B : ℝ} (hB : 0 ≤ B) : EuclideanSpace ℝ (Fin d) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cavityContinuousFactor K L C ε B)
    (continuous_cavityContinuousFactor K L C ε B)
    (Real.exp (cavityFactorSize K L C * (1 + (B + 1)^2))) (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityContinuousFactor_nonneg K L C ε B y)]
      exact cavityContinuousFactor_le K L C ε hB y)

lemma cavityContinuousFactor_lower_on_ball {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : Spin n) {B : ℝ} (_hB : 0 ≤ B) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ B) :
    Real.exp (-cavityFactorSize K L C * (1 + B^2)) ≤ cavityContinuousFactor K L C ε B y := by
  have hg := (abs_le.mp (cavity_logFactor_growth K L C y ε)).1
  have hn : ‖y‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hs := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hn) (cavityFactorSize_nonneg K L C)
  rw [cavityContinuousFactor, cavityRadialCutoff_eq_one hy, mul_one]
  apply Real.exp_le_exp.mpr
  change -(cavityFactorSize K L C * (1 + ‖y‖^2)) ≤ _ at hg
  linarith

theorem cavity_continuous_factor_normalizer_lower {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {d n : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n)
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y) {B : ℝ} (hB : 0 ≤ B) :
    Real.exp (-cavityFactorSize K L C * (1 + B^2)) * (1 - ν.real {x | B < ‖Y x‖}) ≤
      cavityWeightNormalizer ν (fun x => cavityContinuousFactor K L C ε B (Y x)) := by
  let s := {x | ‖Y x‖ ≤ B}
  let w := fun x => cavityContinuousFactor K L C ε B (Y x)
  have hs : MeasurableSet s := measurableSet_le hY.norm measurable_const
  have hw : Measurable w := (continuous_cavityContinuousFactor K L C ε B).measurable.comp hY
  have hi : Integrable w ν := integrable_of_measurable_abs_le hw (fun x => by
    rw [abs_of_nonneg (cavityContinuousFactor_nonneg K L C ε B (Y x))]
    exact cavityContinuousFactor_le K L C ε hB (Y x))
  have hl := cavity_cutoff_normalizer_lower ν s hs w hw (Real.exp_pos _).le
    (fun x hx => ⟨cavityContinuousFactor_lower_on_ball K L C ε hB (Y x) hx,
      cavityContinuousFactor_le K L C ε hB (Y x)⟩)
  have hu : cavityWeightNormalizer ν (s.indicator w) ≤ cavityWeightNormalizer ν w := by
    apply integral_mono (hi.indicator hs) hi
    intro x
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx, le_refl]
    · rw [indicator_of_notMem hx]
      exact cavityContinuousFactor_nonneg K L C ε B (Y x)
  have he : sᶜ = {x | B < ‖Y x‖} := by
    ext x
    change (¬ ‖Y x‖ ≤ B) ↔ B < ‖Y x‖
    exact not_le
  simpa only [he] using hl.trans hu

abbrev CavityFactorBlocks (d n : ℕ) :=
  Matrix (Fin d) (Fin d) ℝ × (Matrix (Fin d) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)

lemma continuous_cavityJointLogFactor {d n : ℕ} (ε : Spin n) :
    Continuous (fun p : CavityFactorBlocks d n × EuclideanSpace ℝ (Fin d) =>
      cavityLogFactor p.1.1 p.1.2.1 p.1.2.2 p.2 ε) := by
  unfold cavityLogFactor cavityQuadratic
  fun_prop

def cavityJointCappedFactor {d n : ℕ} (ε : Spin n) (T : ℝ) :
    CavityFactorBlocks d n × EuclideanSpace ℝ (Fin d) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => Real.exp (min (cavityLogFactor p.1.1 p.1.2.1 p.1.2.2 p.2 ε) T))
    (Real.continuous_exp.comp ((continuous_cavityJointLogFactor ε).min continuous_const)) (Real.exp T)
    (fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (min_le_right _ _))

def cavityJointCutoffFactor {d n : ℕ} (ε : Spin n) (T B : ℝ) :
    CavityFactorBlocks d n × EuclideanSpace ℝ (Fin d) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => cavityJointCappedFactor ε T p * cavityRadialCutoff B ‖p.2‖)
    ((cavityJointCappedFactor ε T).continuous.mul
      ((continuous_cavityRadialCutoff B).comp continuous_snd.norm)) (Real.exp T)
    (fun p => by
      change |Real.exp (min (cavityLogFactor p.1.1 p.1.2.1 p.1.2.2 p.2 ε) T) *
        cavityRadialCutoff B ‖p.2‖| ≤ _
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (cavityRadialCutoff_mem B ‖p.2‖).1)]
      exact (mul_le_mul_of_nonneg_left (cavityRadialCutoff_mem B ‖p.2‖).2
        (Real.exp_pos _).le).trans (by
          rw [mul_one]
          exact Real.exp_le_exp.mpr (min_le_right _ _)))

lemma cavityJointCutoffFactor_eq {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n)
    (B T D : ℝ) (hD : cavityFactorSize K L C ≤ D) (hT : D * (1 + (B + 1)^2) ≤ T)
    (y : EuclideanSpace ℝ (Fin d)) :
    cavityJointCutoffFactor ε T B ((K, L, C), y) = cavityContinuousFactor K L C ε B y := by
  change Real.exp (min (cavityLogFactor K L C y ε) T) * cavityRadialCutoff B ‖y‖ = _
  by_cases hy : B + 1 ≤ ‖y‖
  · simp only [cavityContinuousFactor, cavityRadialCutoff_eq_zero hy, mul_zero]
  · have hn : ‖y‖^2 ≤ (B + 1)^2 := pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hy) 2
    have he := (le_abs_self (cavityLogFactor K L C y ε)).trans (cavity_logFactor_growth K L C y ε)
    have hs := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hn)
      (cavityFactorSize_nonneg K L C)
    have hb := mul_le_mul_of_nonneg_right hD (show 0 ≤ 1 + (B + 1)^2 by positivity)
    rw [min_eq_left (he.trans (hs.trans (hb.trans hT)))]
    rfl

end InvariantIsing

end

end OAI
