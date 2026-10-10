import OAI.Probability.FreeIsing.Conditioning.FiniteBayesCondExp
import OAI.Probability.FreeIsing.Gaussian.BinaryFusion
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := trivial

local instance : Nonempty IsingSpin := ⟨.neg⟩

theorem binaryFusion_likelihood_nonneg {u v : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (a : IsingSpin) :
    0 ≤ (1 + spinSign a * u) * (1 + spinSign a * v) := by
  rcases abs_le.mp hu with ⟨hu₁, hu₂⟩
  rcases abs_le.mp hv with ⟨hv₁, hv₂⟩
  cases a <;> simp only [spinSign_neg, spinSign_pos, neg_one_mul, one_mul] <;>
    apply mul_nonneg <;> linarith

theorem binaryFusion_likelihood_sum {u v : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    (∑ a : IsingSpin, ENNReal.ofReal (1 / 2 : ℝ) *
      ENNReal.ofReal ((1 + spinSign a * u) * (1 + spinSign a * v))) =
        ENNReal.ofReal (1 + u * v) := by
  simp_rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [sum_isingSpin, ← ENNReal.ofReal_add
    (mul_nonneg (by norm_num) (binaryFusion_likelihood_nonneg hu hv .neg))
    (mul_nonneg (by norm_num) (binaryFusion_likelihood_nonneg hu hv .pos))]
  congr 1
  simp only [spinSign_neg, spinSign_pos]
  ring

theorem posterior_spinMean_eq_binaryFusion
    {X : Type*} [MeasurableSpace X]
    (π : Measure IsingSpin) [IsProbabilityMeasure π]
    (hπ : ∀ a, π {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel IsingSpin X) [IsFiniteKernel κ]
    (u v : X → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hu₁ : ∀ᵐ x ∂ν, |u x| < 1) (hv₁ : ∀ᵐ x ∂ν, |v x| < 1)
    (hκ : ∀ a, κ a = ν.withDensity
      (fun x => ENNReal.ofReal ((1 + spinSign a * u x) * (1 + spinSign a * v x)))) :
    ∀ᵐ x ∂κ ∘ₘ π,
      (∫ a, spinSign a ∂(posterior κ π) x) = binaryFusion (u x) (v x) := by
  let L : IsingSpin → X → ℝ≥0∞ := fun a x =>
    ENNReal.ofReal ((1 + spinSign a * u x) * (1 + spinSign a * v x))
  have hL (a : IsingSpin) : Measurable (L a) :=
    ((measurable_const.add (measurable_const.mul hu)).mul
      (measurable_const.add (measurable_const.mul hv))).ennreal_ofReal
  have hpos : ∀ᵐ x ∂ν, (∑ a, π {a} * L a x) ≠ 0 := by
    filter_upwards [hu₁, hv₁] with x hux hvx
    simp only [L, hπ]
    rw [binaryFusion_likelihood_sum hux.le hvx.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (binaryFusion_denominator_pos hux hvx))
  have hfinite : ∀ᵐ x ∂ν, (∑ a, π {a} * L a x) ≠ ∞ := by
    apply ae_of_all
    intro x
    exact ENNReal.sum_ne_top.mpr (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top)
  have hpost := finite_posterior_singletons π ν κ L hL hκ hpos hfinite
  have hac : κ ∘ₘ π ≪ ν := by
    rw [finite_observation_law_density π ν κ L hL hκ]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [hpost, hac.ae_le hu₁, hac.ae_le hv₁] with x hx hux hvx
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, hx, hπ, L,
    binaryFusion_likelihood_sum hux.le hvx.le, smul_eq_mul,
    ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal (binaryFusion_denominator_pos hux hvx).le]
  simp_rw [ENNReal.toReal_ofReal (binaryFusion_likelihood_nonneg hux.le hvx.le _)]
  rw [sum_isingSpin]
  simp only [spinSign_neg, spinSign_pos]
  unfold binaryFusion
  ring

theorem condExp_spin_eq_binaryFusion_of_likelihood
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (π : Measure IsingSpin) [IsProbabilityMeasure π]
    (hπ : ∀ a, π {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel IsingSpin X) [IsFiniteKernel κ]
    (S : Ω → IsingSpin) (Y : Ω → X) (hS : Measurable S) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (S ω, Y ω)) = π ⊗ₘ κ)
    (u v : X → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hu₁ : ∀ᵐ x ∂ν, |u x| < 1) (hv₁ : ∀ᵐ x ∂ν, |v x| < 1)
    (hκ : ∀ a, κ a = ν.withDensity
      (fun x => ENNReal.ofReal ((1 + spinSign a * u x) * (1 + spinSign a * v x)))) :
    μ[fun ω => spinSign (S ω) | (inferInstance : MeasurableSpace X).comap Y]
      =ᵐ[μ] fun ω => binaryFusion (u (Y ω)) (v (Y ω)) := by
  exact FiniteBayes.condExp_state_eq_of_posterior_integral μ π κ S Y hS hY hlaw
    spinSign (fun x => binaryFusion (u x) (v x))
    (posterior_spinMean_eq_binaryFusion π hπ ν κ u v hu hv hu₁ hv₁ hκ)

end Problem367

end

end OAI
