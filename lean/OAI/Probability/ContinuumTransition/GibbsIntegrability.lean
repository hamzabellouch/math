import OAI.Probability.ContinuumTransition.LabelConvolution

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem volume_latticeCell_le_one (z : Lattice) : volume (latticeCell z) ≤ 1 := by
  let a : Space := WithLp.toLp 2 (fun k => ((z k : ℝ)+1/2)/4)
  have hsub : latticeCell z ⊆ (fun x : Space => x+(-a)) ⁻¹' cube 1 := by
    intro x hx k
    have he : ⌊4*x k⌋ = z k := congrFun hx k
    have hlo := Int.floor_le (4*x k)
    have hhi := Int.lt_floor_add_one (4*x k)
    rw [he] at hlo hhi
    change -(1 : ℝ)/2 ≤ x k-a k ∧ x k-a k ≤ 1/2
    dsimp only [a]
    constructor <;> linarith
  have hp := (measurePreserving_add_right volume (-a)).measure_preimage (measurableSet_cube 1).nullMeasurableSet
  have hv : volume ((fun x : Space => x+(-a)) ⁻¹' cube 1) = 1 := by
    rw [hp, volume_cube]
    norm_num
  exact (measure_mono hsub).trans_eq hv

theorem real_volume_cropped_cell_le_one (D : Set Space) (z : Lattice) :
    volume.real (D ∩ latticeCell z) ≤ 1 := by
  have hh := (measure_mono (inter_subset_right : D ∩ latticeCell z ⊆ latticeCell z)).trans
    (volume_latticeCell_le_one z)
  simpa only [Measure.real, ENNReal.toReal_one] using ENNReal.toReal_mono (by norm_num) hh

theorem gibbsFamily_term_zero (V : Space → Space → ℝ) (β h : ℝ) (D : Set Space) :
    familyTerm (gibbsFamily V β h) D 0 = 1 := by
  have hf : gibbsFamily V β h (Fin 0) = fun _ => 1 := by
    funext x
    simp only [gibbsFamily, ite_eq_left (Function.injective_of_subsingleton x),
      gibbsEnergy, Fintype.card_fin, Nat.cast_zero, mul_zero, Finset.univ_eq_empty,
      Finset.sum_empty, zero_div, sub_zero, Real.exp_zero]
  dsimp only [familyTerm, familyIntegral]
  rw [hf, setIntegral_const, Measure.real, volume_generalConfigurations]
  norm_num

theorem grandIntegral_gibbs_pos (V : Space → Space → ℝ) (β h : ℝ) (D : Set Space)
    (hs : Summable (familyTerm (gibbsFamily V β h) D)) :
    0 < grandIntegral (gibbsFamily V β h) D := by
  have hh := hs.le_tsum 0 (fun n _ => familyTerm_nonneg _ D (gibbsFamily_nonneg V β h) n)
  rw [gibbsFamily_term_zero] at hh
  exact lt_of_lt_of_le zero_lt_one hh

theorem physical_gibbs_moment_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) (z : Lattice)
    {c : ℝ} (hc : c ≤ β*(t^2/8)/4) :
    GrandFinite (momentFamily
      (gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h) (latticeCell z) c) D := by
  have hm : Measurable (Function.uncurry (fun x y : Space => physicalProfile t σ R ‖x-y‖)) :=
    (measurable_physicalProfile t hσ hR hs).comp ((measurable_fst.sub measurable_snd).norm)
  apply GrandFinite.of_bound _ hDfin
    (fun ι _ => measurable_momentFamily _ (measurableSet_latticeCell z) c (measurable_gibbsFamily hm β h ι))
    (momentFamily_nonneg _ (gibbsFamily_nonneg _ β h) _ _)
  intro ι _ x
  apply gibbs_moment_stable_bound _ β h (t^2/2) c _ x
  have he := mul_le_mul_of_nonneg_left (physical_gibbs_moment_energy ht hσ hR hs hsmall x z) hβ
  have hcc := mul_le_mul_of_nonneg_right hc (sq_nonneg (occupation (latticeCell z) x))
  nlinarith only [he, hcc]

theorem physical_gibbs_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) :
    GrandFinite (gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h) D := by
  have h0 : (0 : ℝ) ≤ β*(t^2/8)/4 := by positivity
  have hh := physical_gibbs_moment_finite ht hβ hσ hR hs hsmall hDfin h (fun _ => 0) h0
  have he : momentFamily (gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h)
      (latticeCell (fun _ => 0)) 0 = gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h := by
    funext ι inst x
    simp only [momentFamily, zero_mul, Real.exp_zero, mul_one]
  rw [he] at hh
  exact hh

end ContinuumTemperature
end

end OAI
