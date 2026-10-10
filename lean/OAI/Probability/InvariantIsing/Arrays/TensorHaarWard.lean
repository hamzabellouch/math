import OAI.Probability.InvariantIsing.Arrays.TensorCoefficientDerivative

namespace OAI

/-! Finite Gaussian/Haar Ward identities. The Gaussian correction is
proved from integration by parts, while Haar invariance is differentiated
on genuine determinant-one plane rotations. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

def finiteGibbsVariation (w H O dH dO : S → ℝ) : ℝ :=
  gibbsAverage w H dO + gibbsAverage w H (fun x => O x * dH x) -
    gibbsAverage w H O * gibbsAverage w H dH

lemma measurable_finiteGibbsVariation {Ω : Type*} [MeasurableSpace Ω]
    (w : S → ℝ) (H O dH dO : Ω → S → ℝ)
    (hH : ∀ x, Measurable (fun ω => H ω x))
    (hO : ∀ x, Measurable (fun ω => O ω x))
    (hdH : ∀ x, Measurable (fun ω => dH ω x))
    (hdO : ∀ x, Measurable (fun ω => dO ω x)) :
    Measurable (fun ω => finiteGibbsVariation w (H ω) (O ω) (dH ω) (dO ω)) :=
  ((measurable_gibbsAverage w H dO hH hdO).add
    (measurable_gibbsAverage w H (fun ω x => O ω x * dH ω x) hH
      (fun x => (hO x).mul (hdH x)))).sub
    ((measurable_gibbsAverage w H O hH hO).mul (measurable_gibbsAverage w H dH hH hdH))

lemma finiteGibbsVariation_add_H (w H O A Y dO : S → ℝ) :
    finiteGibbsVariation w H O (fun x => A x + Y x) dO =
      finiteGibbsVariation w H O A dO +
        (gibbsAverage w H (fun x => O x * Y x) -
          gibbsAverage w H O * gibbsAverage w H Y) := by
  simp only [finiteGibbsVariation, gibbsAverage, mul_add, Finset.sum_add_distrib]
  ring

lemma integrable_gaussian_finiteGibbsVariation {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O A dO : S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => finiteGibbsVariation w (fun x => H x + linearGaussian C g x) O A dO)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  simp only [finiteGibbsVariation, gibbsAverage_mul_gibbsAverage]
  exact ((integrable_gaussian_gibbs_test hw H dO C).add
    (integrable_gaussian_gibbs_test hw H (fun x => O x * A x) C)).sub
    (integrable_gaussian_pair_test hw H (fun x y => O x * A y) C)

/-- Pointwise averaging of the normalized Gibbs rotation derivative over
finite Gaussian marks leaves precisely its explicit covariance correction. -/
lemma integral_gaussian_finiteGibbsVariation {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O A dO : S → ℝ) (D C : S → Fin (d + 1) → ℝ) :
    (∫ g, finiteGibbsVariation w (fun x => H x + linearGaussian C g x) O
      (fun x => A x + linearGaussian D g x) dO
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      (∫ g, finiteGibbsVariation w (fun x => H x + linearGaussian C g x) O A dO
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection w (fun x => H x + linearGaussian C g x) O (gaussianCross D C)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  simp_rw [finiteGibbsVariation_add_H]
  have hadd := integral_add (integrable_gaussian_finiteGibbsVariation hw H O A dO C)
    ((integrable_gaussian_gibbs_linear_test hw H O D C).sub
      (integrable_gaussian_gibbs_linear_product hw H O D C))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, gaussian_gibbs_covariance_insertion hw]

omit [Fintype S] in
lemma abs_linearGaussian_le {d : ℕ} (A : S → Fin d → ℝ) (g : Fin d → ℝ)
    (cap : Fin d → ℝ) (hA : ∀ x a, |A x a| ≤ cap a) (x : S) :
    |linearGaussian A g x| ≤ ∑ a, cap a * |g a| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hA x a) (abs_nonneg _)

/-- A finite-prior Haar Ward identity with Gaussian coefficient tensors.
The assumptions are elementary measurability, derivatives and finite
bounds; the covariance correction is derived, not postulated. -/
theorem integral_special_gaussian_gibbs_rotation_identity {N d : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    {w : S → ℝ} (hw : GibbsReference w)
    (H O : SpecialOrthogonal N → S → ℝ) (C : SpecialOrthogonal N → S → Fin (d + 1) → ℝ)
    (hHm : ∀ x, Measurable (fun U => H U x))
    (hOm : ∀ x, Measurable (fun U => O U x))
    (hCm : ∀ x a, Measurable (fun U => C U x a))
    (dH dO : ℝ → SpecialOrthogonal N → S → ℝ)
    (dC : ℝ → SpecialOrthogonal N → S → Fin (d + 1) → ℝ)
    (hdHm : ∀ x, Measurable (fun U => dH 0 U x))
    (hdOm : ∀ x, Measurable (fun U => dO 0 U x))
    (hdCm : ∀ x a, Measurable (fun U => dC 0 U x a))
    (hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      HasDerivAt (fun s => H (R s * U) x) (dH t U x) t)
    (hOd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      HasDerivAt (fun s => O (R s * U) x) (dO t U x) t)
    (hCd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x a,
      HasDerivAt (fun s => C (R s * U) x a) (dC t U x a) t)
    (K L M : ℝ) (cap : Fin (d + 1) → ℝ) (hK : 0 ≤ K)
    (hOb : ∀ U x, |O U x| ≤ K)
    (hdHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x, |dH t U x| ≤ L)
    (hdOb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x, |dO t U x| ≤ M)
    (hdCb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x a, |dC t U x a| ≤ cap a) :
    (∫ U, (∫ g, finiteGibbsVariation w (fun x => H U x + linearGaussian (C U) g x)
        (O U) (dH 0 U) (dO 0 U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection w (fun x => H U x + linearGaussian (C U) g x)
        (O U) (gaussianCross (dC 0 U) (C U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) ∂μ) = 0 := by
  let γ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  let Lg := fun g : Fin (d + 1) → ℝ => L + ∑ a, cap a * |g a|
  let V := fun (U : SpecialOrthogonal N) (g : Fin (d + 1) → ℝ) =>
    finiteGibbsVariation w (fun x => H U x + linearGaussian (C U) g x) (O U)
      (fun x => dH 0 U x + linearGaussian (dC 0 U) g x) (dO 0 U)
  have hHg (g : Fin (d + 1) → ℝ) (x : S) :
      Measurable (fun U => H U x + linearGaussian (C U) g x) :=
    (hHm x).add (Finset.measurable_sum _ fun a _ => (hCm x a).mul_const _)
  have hdHg (g : Fin (d + 1) → ℝ) (x : S) :
      Measurable (fun U => dH 0 U x + linearGaussian (dC 0 U) g x) :=
    (hdHm x).add (Finset.measurable_sum _ fun a _ => (hdCm x a).mul_const _)
  have hgb (g : Fin (d + 1) → ℝ) (U : SpecialOrthogonal N) (t : ℝ)
      (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (x : S) :
      |dH t U x + linearGaussian (dC t U) g x| ≤ Lg g :=
    (abs_add_le _ _).trans (add_le_add (hdHb U t ht x)
      (abs_linearGaussian_le (dC t U) g cap (hdCb U t ht) x))
  have hz (g : Fin (d + 1) → ℝ) : (∫ U, V U g ∂μ) = 0 := by
    exact integral_special_gibbs_rotation_identity μ R hR hw
      (fun U x => H U x + linearGaussian (C U) g x) O
      (hHg g) hOm (fun t U x => dH t U x + linearGaussian (dC t U) g x) dO
      (hdHg g) hdOm
      (fun U t ht x => (hHd U t ht x).add
        (HasDerivAt.fun_sum fun a _ => (hCd U t ht x a).mul_const (g a)))
      hOd K (Lg g) M hK hOb (fun U t ht x => hgb g U t ht x) hdOb
  have hmV : Measurable (Function.uncurry V) :=
    measurable_finiteGibbsVariation w _ _ _ _
      (fun x => ((hHm x).comp measurable_fst).add
        (Finset.measurable_sum _ fun a _ => ((hCm x a).comp measurable_fst).mul
          ((measurable_pi_apply a).comp measurable_snd)))
      (fun x => (hOm x).comp measurable_fst)
      (fun x => ((hdHm x).comp measurable_fst).add
        (Finset.measurable_sum _ fun a _ => ((hdCm x a).comp measurable_fst).mul
          ((measurable_pi_apply a).comp measurable_snd)))
      (fun x => (hdOm x).comp measurable_fst)
  have hiL : Integrable Lg γ := (integrable_const L).add
    (integrable_finsetSum _ fun a _ =>
      (((measurePreserving_eval (fun _ : Fin (d + 1) => gaussianReal 0 1) a).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).abs.const_mul (cap a)))
  have hiB : Integrable (fun g => M + 2 * K * Lg g) γ :=
    (integrable_const M).add (hiL.const_mul (2 * K))
  have hiV : Integrable (Function.uncurry V) (μ.prod γ) :=
    (hiB.comp_snd μ).mono' hmV.aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact abs_gibbsVariation_le hw _ _ _ _ hK (hOb p.1)
        (fun x => hgb p.2 p.1 0 (by norm_num) x) (hdOb p.1 0 (by norm_num)))
  have he : (∫ U, ∫ g, V U g ∂γ ∂μ) = 0 := by
    rw [integral_integral_swap hiV]
    simp only [hz, integral_zero]
  convert he using 1
  congr 1
  funext U
  exact (integral_gaussian_finiteGibbsVariation hw (H U) (O U) (dH 0 U) (dO 0 U)
    (dC 0 U) (C U)).symm

end InvariantIsing

end

end OAI
