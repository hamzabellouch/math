import OAI.MeasureTheory.Falconer.Slicing.GaussianBox
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap

namespace OAI

/-! # Positive Gaussian mass in a bounded coordinate slab -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussian_lower_volume_bounded (S : Set (Space n)) (hS : MeasurableSet S)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x ∈ S, ‖x‖ ≤ B) :
    ENNReal.ofReal (gaussianVolumeNormalization n*Real.exp (-(1/2:ℝ)*B^2))*volume S ≤
      stdGaussian (Space n) S := by
  rw [← normalizedGaussianLebesgue_eq_standard,normalizedGaussianLebesgue,
    Measure.smul_apply,smul_eq_mul,gaussianLebesgue,withDensity_apply _ hS,
    ENNReal.ofReal_mul (by unfold gaussianVolumeNormalization; positivity)]
  rw [mul_assoc]
  apply mul_le_mul_right
  rw [← setLIntegral_const]
  apply setLIntegral_mono' hS
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := hbound x hx
  nlinarith [norm_nonneg x]

def coordinateSlabBox (c : Space (n+1)) (r ρ : ℝ) : Set (Space (n+1)) :=
  {x | |x 0| ≤ r ∧ ∀ i : Fin n, |x i.succ-c i.succ| ≤ ρ}

theorem coordinateSlabBox_measurable (c : Space (n+1)) (r ρ : ℝ) :
    MeasurableSet (coordinateSlabBox c r ρ) := by
  simp only [coordinateSlabBox,ofPred_and,ofPred_forall]
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    (MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const))

theorem coordinateSlabBox_volume (c : Space (n+1)) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    volume (coordinateSlabBox c r ρ) = ENNReal.ofReal ((2*r)*(2*ρ)^n) := by
  rw [← (PiLp.volume_preserving_toLp (Fin (n+1))).measure_preimage
    (coordinateSlabBox_measurable c r ρ).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin (n+1) → ℝ)) ⁻¹' coordinateSlabBox c r ρ =
      Set.pi univ (Fin.cases (Icc (-r) r)
        (fun i : Fin n => Icc (c i.succ-ρ) (c i.succ+ρ))) := by
    ext x
    simp only [mem_preimage,coordinateSlabBox,mem_ofPred_eq,mem_pi,mem_univ,true_implies,
      Fin.forall_fin_succ,Fin.cases_zero,Fin.cases_succ,mem_Icc,abs_le]
    constructor
    · rintro ⟨hx,ht⟩
      exact ⟨hx,fun i => by have hh := ht i; constructor <;> linarith [hh.1,hh.2]⟩
    · rintro ⟨hx,ht⟩
      exact ⟨hx,fun i => by have hh := ht i; constructor <;> linarith [hh.1,hh.2]⟩
  rw [he,volume_pi_pi,Fin.prod_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.volume_Icc,sub_neg_eq_add,
    ← two_mul,show ∀ a : ℝ, a+ρ-(a-ρ) = 2*ρ by intro a; ring,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*ρ),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]

theorem coordinateSlabBox_distance (c : Space (n+1)) {r ρ : ℝ}
    (hrρ : r ≤ ρ) (hc : |c 0| ≤ ρ) {x : Space (n+1)}
    (hx : x ∈ coordinateSlabBox c r ρ) : ‖x-c‖ ≤ (n+1:ℝ)*(2*ρ) := by
  rw [show (n+1:ℝ) = ((n+1:ℕ):ℝ) by norm_cast]
  apply coordinate_norm_le_card_mul
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |x 0-c 0| ≤ 2*ρ
    calc
      _ ≤ |x 0|+|c 0| := abs_sub _ _
      _ ≤ 2*ρ := by linarith [hx.1]
  · change |x j.succ-c j.succ| ≤ 2*ρ
    have hnonneg : 0 ≤ ρ := (abs_nonneg _).trans hc
    exact (hx.2 j).trans (by linarith)

end Falconer

end OAI
