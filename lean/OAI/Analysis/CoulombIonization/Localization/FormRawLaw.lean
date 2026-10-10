import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.SobolevVector
import OAI.Analysis.CoulombIonization.RadialBounds.StripAveraging

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombRadialAveraging

def formRawDensity {N : ℕ} (ψ : FormVector N) (x : Configuration N) : ℝ :=
  ∑ s : Spins N, ‖ψ.value s x‖^2

lemma formRawDensity_nonneg {N : ℕ} (ψ : FormVector N) (x : Configuration N) :
    0 ≤ formRawDensity ψ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma formRawDensity_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    Integrable (formRawDensity ψ) :=
  integrable_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)

lemma formRawDensity_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    ∫ x, formRawDensity ψ x = formMass ψ :=
  integral_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)

def formRawLaw {N : ℕ} (ψ : FormVector N) : Measure (Configuration N) :=
  volume.withDensity (fun x => ENNReal.ofReal (formRawDensity ψ x))

lemma formRawLaw_univ {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    formRawLaw ψ univ = ENNReal.ofReal (formMass ψ) := by
  rw [formRawLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (formRawDensity_integrable hψ)
    (ae_of_all _ (formRawDensity_nonneg ψ))).symm.trans
      (congrArg ENNReal.ofReal (formRawDensity_integral hψ))

lemma formRawLaw_finite {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    IsFiniteMeasure (formRawLaw ψ) := by
  constructor
  rw [formRawLaw_univ hψ]
  exact ENNReal.ofReal_lt_top

lemma formRawLaw_probability {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) : IsProbabilityMeasure (formRawLaw ψ) := by
  constructor
  rw [formRawLaw_univ hψ,hm,ENNReal.ofReal_one]

lemma formRawLaw_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (g : Configuration N → ℝ) :
    (∫ x, g x ∂formRawLaw ψ) = ∫ x, formRawDensity ψ x*g x := by
  rw [formRawLaw,integral_withDensity_eq_integral_toReal_smul₀
    (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (formRawDensity_nonneg ψ _),smul_eq_mul]

lemma formRawLaw_integral_eq_spin_sum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (∫ x, g x ∂formRawLaw ψ) = ∑ s : Spins N, ∫ x, g x*‖ψ.value s x‖^2 := by
  rw [formRawLaw_integral hψ]
  have hi (s : Spins N) : Integrable (fun x => g x*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable (ae_of_all _ hB)
  simp only [formRawDensity,Finset.sum_mul]
  simp_rw [mul_comm (‖ψ.value _ _‖^2)]
  exact integral_finsetSum _ (fun s _ => hi s)

def rawBallCount {N : ℕ} (y : Space) (R : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if ‖x i-y‖ < R then 1 else 0

def rawStripCount {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) : ℝ :=
  slidingCount (fun i => ‖x i-y‖) (7*b) b t

lemma rawBallCount_nonneg {N : ℕ} (y : Space) (R : ℝ) (x : Configuration N) :
    0 ≤ rawBallCount y R x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma rawBallCount_le {N : ℕ} (y : Space) (R : ℝ) (x : Configuration N) :
    rawBallCount y R x ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma configuration_distance_measurable {N : ℕ} (y : Space) (i : Fin N) :
    Measurable (fun x : Configuration N => ‖x i-y‖) := by
  exact (((continuous_apply i).sub continuous_const).norm :
    Continuous (fun x : Configuration N => ‖x i-y‖)).measurable

lemma rawBallCount_measurable {N : ℕ} (y : Space) (R : ℝ) :
    Measurable (rawBallCount (N := N) y R) := by
  apply Finset.measurable_sum; intro i _
  exact Measurable.ite (measurableSet_lt (configuration_distance_measurable y i)
    measurable_const) measurable_const measurable_const

lemma rawBallCount_sq_integrable {N : ℕ} (y : Space) (R : ℝ)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Integrable (fun x => rawBallCount y R x^2) μ := by
  apply Integrable.of_bound ((rawBallCount_measurable y R).pow_const 2).aestronglyMeasurable
    ((N:ℝ)^2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _) 2)

lemma rawStripCount_eq_card {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) :
    rawStripCount y t b x =
      ((Finset.univ.filter (fun i => t-7*b ≤ ‖x i-y‖ ∧ ‖x i-y‖ ≤ t+b)).card:ℝ) := by
  classical
  unfold rawStripCount slidingCount
  have he (i : Fin N) : slidingBit (7*b) b ‖x i-y‖ t =
      if t-7*b ≤ ‖x i-y‖ ∧ ‖x i-y‖ ≤ t+b then (1:ℝ) else 0 := by
    unfold slidingBit
    congr 1
    apply propext
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp_rw [he]
  simp only [Finset.sum_boole]

lemma upperCount_le_rawBallCount {N : ℕ} (y : Space) {R S : ℝ} (hRS : R < S)
    (x : Configuration N) : upperCount (fun i => ‖x i-y‖) R ≤ rawBallCount y S x := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h₁ h₂ <;> try norm_num
  exact False.elim (h₂ (lt_of_le_of_lt h₁ hRS))

theorem radial_raw_radius_selection {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a) :
    ∃ t ∈ Icc (5*a) (6*a),
      (∫ x, rawStripCount y t b x^2 ∂formRawLaw ψ) ≤
        (8*b/a)*(∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ) := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  have hd (i : Fin N) : Measurable (fun x : Configuration N => ‖x i-y‖) :=
    configuration_distance_measurable y i
  obtain ⟨t,ht,hh⟩ := exists_radius_expected_square hd (formRawLaw ψ)
    (lo := 5*a) (hi := 6*a) (l := 7*b) (r := b) (by linarith) (by linarith)
  refine ⟨t,ht,?_⟩
  have he : (7*b+b)/(6*a-5*a) = 8*b/a := by congr 1 <;> ring
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) ha.le)
  apply integral_mono (upperCount_sq_integrable hd (6*a+b)) (rawBallCount_sq_integrable y (7*a) _)
  intro x
  exact pow_le_pow_left₀ (upperCount_nonneg _ _)
    (upperCount_le_rawBallCount y (by linarith) x) 2

end CoulombAtom

end

end OAI
