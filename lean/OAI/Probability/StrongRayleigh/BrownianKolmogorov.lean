import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have he (t : ℝ) :
      HasDerivAt (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2))
        ((v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have h1 : deriv (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t
    exact (he t).deriv
  have h2 : deriv (fun t : ℝ => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => ((v : ℝ) + (v : ℝ)^2 * t^2) * Real.exp ((v : ℝ) * t^2 / 2) := by
    ext t
    convert! (((hasDerivAt_id t).const_mul (v : ℝ)).mul (he t)).deriv using 1
    simp only [id_eq]
    ring
  have h3 : deriv (fun t : ℝ => ((v : ℝ) + (v : ℝ)^2 * t^2) *
        Real.exp ((v : ℝ) * t^2 / 2)) =
      fun t => (3 * (v : ℝ)^2 * t + (v : ℝ)^3 * t^3) *
        Real.exp ((v : ℝ) * t^2 / 2) := by
    ext t
    convert! (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ)^2)).const_add
      (v : ℝ)).mul (he t)).deriv using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have h4 : deriv (fun t : ℝ => (3 * (v : ℝ)^2 * t + (v : ℝ)^3 * t^3) *
        Real.exp ((v : ℝ) * t^2 / 2)) 0 = 3 * (v : ℝ)^2 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul (3 * (v : ℝ)^2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ)^3))).mul (he 0)
    convert! h.deriv using 1
    norm_num

  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero (by simp)]
      rfl
    _ = 3 * (v : ℝ)^2 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rw [iteratedDeriv_succ', h1, iteratedDeriv_succ', h2,
        iteratedDeriv_succ', h3, iteratedDeriv_one]
      exact h4

theorem integral_abs_pow_four_of_hasLaw {Ω : Type u_1} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, |X ω| ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 := by
  have heven : Even (4 : ℕ) := by decide
  simp_rw [heven.pow_abs]
  have h := hX.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  simpa only [Function.comp_def, integral_pow_four_gaussianReal] using h

theorem integrable_abs_pow_four_of_hasLaw {Ω : Type u_2} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) :
    Integrable (fun ω => |X ω| ^ 4) P := by
  have hLp : MemLp X (4 : ℕ) P := hX.hasGaussianLaw.memLp (by norm_num)
  simpa only [Real.norm_eq_abs] using hLp.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)

theorem lintegral_edist_pow_four_of_increment_law {Ω : Type u_3} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {v : ℝ≥0}
    (hXY : HasLaw (X - Y) (gaussianReal 0 v) P) :
    (∫⁻ ω, edist (X ω) (Y ω) ^ (4 : ℕ) ∂P) =
      ENNReal.ofReal (3 * (v : ℝ) ^ 2) := by
  simp_rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _) 4]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    exact integral_abs_pow_four_of_hasLaw hXY
  · exact integrable_abs_pow_four_of_hasLaw hXY
  · exact ae_of_all _ (fun _ => by positivity)

theorem preBrownian_integral_abs_sub_pow_four {Ω : Type u_4} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) :
    (∫ ω, |B s ω - B t ω| ^ 4 ∂P) = 3 * |(s : ℝ) - (t : ℝ)| ^ 2 := by
  convert! integral_abs_pow_four_of_hasLaw (hB.hasLaw_sub s t) using 1

theorem isKolmogorovProcess_of_gaussian_increments
    {T : Type u_5} {Ω : Type u_6} [PseudoMetricSpace T] [MeasurableSpace Ω]
    {P : Measure Ω} {X : T → Ω → ℝ}
    (hXm : ∀ t, Measurable (X t))
    (hX : ∀ s t, HasLaw (X s - X t) (gaussianReal 0 (nndist s t)) P) :
    IsKolmogorovProcess X P 4 2 3 := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hXm (fun s t => ?_) (by norm_num)
    (by norm_num)
  have h := lintegral_edist_pow_four_of_increment_law (hX s t)
  convert! h.le using 1 <;>
    simp [edist_dist, ENNReal.ofReal_mul,
      ENNReal.ofReal_pow, dist_nonneg]

theorem isAEKolmogorovProcess_of_gaussian_increments
    {T : Type u_7} {Ω : Type u_8} [PseudoMetricSpace T] [MeasurableSpace Ω]
    {P : Measure Ω} {X : T → Ω → ℝ}
    (hXm : ∀ t, AEMeasurable (X t) P)
    (hX : ∀ s t, HasLaw (X s - X t) (gaussianReal 0 (nndist s t)) P) :
    IsAEKolmogorovProcess X P 4 2 3 := by
  let Y : T → Ω → ℝ := fun t => AEMeasurable.mk (X t) (hXm t)
  refine ⟨Y, isKolmogorovProcess_of_gaussian_increments
    (fun t => (hXm t).measurable_mk) (fun s t => ?_), fun t => (hXm t).ae_eq_mk⟩
  apply (hX s t).congr
  filter_upwards [(hXm s).ae_eq_mk, (hXm t).ae_eq_mk] with ω hs ht
  change Y s ω - Y t ω = X s ω - X t ω
  exact congrArg₂ (· - ·) hs.symm ht.symm

theorem preBrownian_isAEKolmogorovProcess {Ω : Type u_9} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsAEKolmogorovProcess B P 4 2 3 := by
  apply isAEKolmogorovProcess_of_gaussian_increments hB.aemeasurable
  intro s t
  convert! hB.hasLaw_sub s t using 1

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
