import OAI.Analysis.RCDHeat.ExistingAnalytic
import Mathlib.Analysis.InnerProductSpace.Positive

namespace OAI

/-!
# Gram operators of Sobolev coordinate columns

These operators use the canonical carré du champ of the Cheeger energy.
The change-of-coordinates formula is therefore an identity for the actual
energy, rather than an assumption about an auxiliary matrix field.
-/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Linear combinations of the scalar coordinate functions. -/
def sobolevColumnMap {n : ℕ} (u : Fin n → SobolevSpace μ hQ) :
    Euclidean n →L[ℝ] SobolevSpace μ hQ :=
  ∑ a, (EuclideanSpace.proj a).smulRight (u a)

omit [BorelSpace X] [ProperSpace X] in
theorem sobolevColumnMap_apply {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (v : Euclidean n) : sobolevColumnMap μ hQ u v = ∑ a, v a • u a := by
  simp [sobolevColumnMap]

omit [BorelSpace X] [ProperSpace X] in
theorem sobolevColumnMap_single {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (a : Fin n) :
    sobolevColumnMap μ hQ u (EuclideanSpace.single a 1) = u a := by
  classical
  simp [sobolevColumnMap_apply, PiLp.single_apply]

variable (U : E →L[ℝ] SobolevSpace μ hQ)
  {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
  (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C : ℝ))

/-- The weighted mean energy as a continuous symmetric bilinear form. -/
def sobolevGramForm : E →L[ℝ] E →L[ℝ] ℝ :=
  (weightedGammaCLM μ hQ hw hb).bilinearComp U U

omit [CompleteSpace E] in
theorem sobolevGramForm_apply (v z : E) :
    sobolevGramForm μ hQ U hw hb v z =
      ∫ x, w x * localGamma μ hQ (U v) (U z) x ∂μ := rfl

/-- Riesz representation of the weighted Sobolev Gram form. -/
def sobolevGram : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (sobolevGramForm μ hQ U hw hb)

theorem sobolevGram_inner (v z : E) :
    ⟪sobolevGram μ hQ U hw hb v, z⟫_ℝ =
      weightedGamma μ hQ w (U v) (U z) := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

theorem sobolevGram_energy (v : E) :
    ⟪v, sobolevGram μ hQ U hw hb v⟫_ℝ =
      ∫ x, w x * (SobolevSpace.minimalSlope μ hQ (U v) x) ^ 2 ∂μ := by
  rw [real_inner_comm, sobolevGram_inner, weightedGamma_self]

theorem sobolevGram_isSymmetric : (sobolevGram μ hQ U hw hb).IsSymmetric := by
  intro v z
  change ⟪sobolevGram μ hQ U hw hb v, z⟫_ℝ = ⟪v, sobolevGram μ hQ U hw hb z⟫_ℝ
  calc
    _ = weightedGamma μ hQ w (U v) (U z) := sobolevGram_inner μ hQ U hw hb v z
    _ = weightedGamma μ hQ w (U z) (U v) := weightedGamma_comm μ hQ w (U v) (U z)
    _ = ⟪sobolevGram μ hQ U hw hb z, v⟫_ℝ := (sobolevGram_inner μ hQ U hw hb z v).symm
    _ = _ := real_inner_comm _ _

theorem sobolevGram_isPositive (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x) :
    (sobolevGram μ hQ U hw hb).IsPositive := by
  refine ⟨sobolevGram_isSymmetric μ hQ U hw hb, fun v => ?_⟩
  change 0 ≤ ⟪sobolevGram μ hQ U hw hb v, v⟫_ℝ
  rw [sobolevGram_inner, weightedGamma_self]
  apply integral_nonneg_of_ae
  filter_upwards [hwpos] with x hx
  exact mul_nonneg hx (sq_nonneg _)

/-- Changing the coordinate columns conjugates their actual Gram operator. -/
theorem sobolevGram_comp (A : E →L[ℝ] E) :
    sobolevGram μ hQ (U.comp A) hw hb =
      A.adjoint.comp ((sobolevGram μ hQ U hw hb).comp A) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro z
  rw [sobolevGram_inner]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, sobolevGram_inner]

/-- Pointwise comparison of weights gives comparison of every Gram energy. -/
theorem sobolevGram_energy_mono {w' : X → ℝ}
    (hw' : AEStronglyMeasurable w' μ) {C' : ℝ≥0}
    (hb' : ∀ᵐ x ∂μ, ‖w' x‖ ≤ (C' : ℝ))
    (hle : ∀ᵐ x ∂μ, w x ≤ w' x) (v : E) :
    ⟪v, sobolevGram μ hQ U hw hb v⟫_ℝ ≤
      ⟪v, sobolevGram μ hQ U hw' hb' v⟫_ℝ := by
  rw [sobolevGram_energy, sobolevGram_energy]
  have hi := localGamma_memL1 μ hQ (U v) (U v)
  have hself := localGamma_self μ hQ (U v)
  apply integral_mono_ae
  · exact (hi.bdd_mul hw hb).congr (by
      filter_upwards [hself] with x hx
      rw [hx])
  · exact (hi.bdd_mul hw' hb').congr (by
      filter_upwards [hself] with x hx
      rw [hx])
  · filter_upwards [hle] with x hx
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- The Gram average on a measurable set, with its actual reference measure. -/
def sobolevMeanGram (s : Set X) (hs : MeasurableSet s) : E →L[ℝ] E :=
  (μ.real s)⁻¹ • sobolevGram μ hQ U
    (w := s.indicator fun _ => (1 : ℝ))
    ((measurable_const.indicator hs).aestronglyMeasurable)
    (C := 1) (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ s <;> simp [hx])

theorem sobolevMeanGram_energy (s : Set X) (hs : MeasurableSet s) (v : E) :
    ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ =
      (μ.real s)⁻¹ * ∫ x in s,
        (SobolevSpace.minimalSlope μ hQ (U v) x) ^ 2 ∂μ := by
  simp only [sobolevMeanGram, smul_apply, inner_smul_right,
    sobolevGram_energy]
  congr 1
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ s <;> simp [hx]

theorem sobolevMeanGram_inner (s : Set X) (hs : MeasurableSet s) (v z : E) :
    ⟪sobolevMeanGram μ hQ U s hs v, z⟫_ℝ =
      (μ.real s)⁻¹ * ∫ x in s, localGamma μ hQ (U v) (U z) x ∂μ := by
  simp only [sobolevMeanGram, smul_apply, real_inner_smul_left,
    sobolevGram_inner, weightedGamma]
  congr 1
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ s <;> simp [hx]

theorem sobolevMeanGram_column_entry {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hs : MeasurableSet s) (a b : Fin n) :
    ⟪sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) s hs
        (EuclideanSpace.single a 1), EuclideanSpace.single b 1⟫_ℝ =
      (μ.real s)⁻¹ * ∫ x in s, localGamma μ hQ (u a) (u b) x ∂μ := by
  rw [sobolevMeanGram_inner, sobolevColumnMap_single, sobolevColumnMap_single]

theorem sobolevMeanGram_isPositive (s : Set X) (hs : MeasurableSet s) :
    (sobolevMeanGram μ hQ U s hs).IsPositive := by
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg
  · apply sobolevGram_isPositive
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ s <;> simp [hx]
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg

theorem sobolevMeanGram_comp (s : Set X) (hs : MeasurableSet s)
    (A : E →L[ℝ] E) :
    sobolevMeanGram μ hQ (U.comp A) s hs =
      A.adjoint.comp ((sobolevMeanGram μ hQ U s hs).comp A) := by
  ext v
  simp only [sobolevMeanGram, sobolevGram_comp, smul_apply,
    ContinuousLinearMap.comp_apply, map_smul]

end RegularPointCoordinates

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Local harmonicity is tested against the existing zero-boundary Sobolev
space, using the canonical Dirichlet energy. -/
def IsSobolevHarmonicOn (Ω : Set X) (f : SobolevSpace μ hQ) : Prop :=
  ∀ φ : SobolevSpace μ hQ, φ ∈ SobolevSpace.dirichlet μ hQ Ω →
    energyForm μ hQ f φ = 0

omit [BorelSpace X] [ProperSpace X] in
theorem IsSobolevHarmonicOn.add {Ω : Set X} {f g : SobolevSpace μ hQ}
    (hf : IsSobolevHarmonicOn μ hQ Ω f) (hg : IsSobolevHarmonicOn μ hQ Ω g) :
    IsSobolevHarmonicOn μ hQ Ω (f + g) := by
  intro φ hφ
  rw [energyForm_add_left, hf φ hφ, hg φ hφ, add_zero]

omit [BorelSpace X] [ProperSpace X] in
theorem IsSobolevHarmonicOn.smul {Ω : Set X} {f : SobolevSpace μ hQ}
    (hf : IsSobolevHarmonicOn μ hQ Ω f) (c : ℝ) :
    IsSobolevHarmonicOn μ hQ Ω (c • f) := by
  intro φ hφ
  rw [energyForm_smul_left, hf φ hφ, mul_zero]

omit [BorelSpace X] [ProperSpace X] in
theorem IsSobolevHarmonicOn.linearCombination {Ω : Set X} {n : ℕ}
    {u : Fin n → SobolevSpace μ hQ}
    (hu : ∀ a, IsSobolevHarmonicOn μ hQ Ω (u a)) (v : Euclidean n) :
    IsSobolevHarmonicOn μ hQ Ω (sobolevColumnMap μ hQ u v) := by
  classical
  rw [sobolevColumnMap_apply]
  have hs (s : Finset (Fin n)) :
      IsSobolevHarmonicOn μ hQ Ω (∑ a ∈ s, v a • u a) := by
    induction s using Finset.induction_on with
    | empty =>
      intro φ _
      simp [energyForm]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IsSobolevHarmonicOn.add μ hQ
        (IsSobolevHarmonicOn.smul μ hQ (hu a) (v a)) ih
  exact hs Finset.univ

end RegularPointCoordinates

end

end OAI
