import OAI.Analysis.FiniteFactor.Coupling.VectorBayes

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The interval in which the unconditioned partner crosses an eligible threshold. -/
def crossingPartner (right : Bool) (u : ℝ) : Set ℝ :=
  if right then Set.Iio u else Set.Ici u

theorem crossingPartner_measurable (right : Bool) (u : ℝ) : MeasurableSet (crossingPartner right u) := by
  cases right
  · exact measurableSet_Ici
  · exact measurableSet_Iio

theorem posterior_noncrossing_le_exp (p : CouplingParameters) (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    p.posteriorKernel right t (crossingPartner right u)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(p.rho w / 10))) := by
  have hlo := p.posteriorLaw_crossing_lower right w ht hu heligible
  change ENNReal.ofReal (p.rho w / 10) ≤ p.posteriorKernel right t (crossingPartner right u) at hlo
  rw [measure_compl (crossingPartner_measurable right u) (measure_ne_top _ _), measure_univ]
  calc
    1 - p.posteriorKernel right t (crossingPartner right u) ≤ 1 - ENNReal.ofReal (p.rho w / 10) :=
      tsub_le_tsub_left hlo 1
    _ = ENNReal.ofReal (1 - p.rho w / 10) := by rw [ENNReal.ofReal_sub 1 (div_nonneg (p.rho_nonneg w) (by norm_num)), ENNReal.ofReal_one]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (-(p.rho w / 10))])

/-- Simultaneous noncrossing of any fixed eligible coordinates, conditional on
the entire endpoint vector. The exponent is the sum of their actual biases. -/
theorem vectorPosterior_noncrossing_le_exp {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (x u : ι → ℝ) (I : Finset ι)
    (hx : ∀ i ∈ I, x i ∈ Set.Ico 0 1)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (heligible : ∀ i ∈ I, if right i then u i ≤ x i else x i < u i) :
    vectorPosterior p right x (Set.pi (I : Set ι) (fun i => (crossingPartner (right i) (u i))ᶜ)) ≤
      ENNReal.ofReal (Real.exp (-(∑ i ∈ I, (p i).rho (w i) / 10))) := by
  rw [vectorPosterior_independence _ _ _ _ _ (fun i _ => (crossingPartner_measurable (right i) (u i)).compl)]
  calc
    _ ≤ ∏ i ∈ I, ENNReal.ofReal (Real.exp (-((p i).rho (w i) / 10))) := by
      apply Finset.prod_le_prod
      intro i hi
      exact (p i).posterior_noncrossing_le_exp (right i) (w i) (hx i hi) (hu i hi) (heligible i hi)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
      simp only [Finset.sum_neg_distrib]

theorem vectorPosterior_noncrossing_source_bound {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (x u : ι → ℝ) (I : Finset ι) (m ρ L : ℝ)
    (hx : ∀ i ∈ I, x i ∈ Set.Ico 0 1)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (heligible : ∀ i ∈ I, if right i then u i ≤ x i else x i < u i)
    (hρ : ∀ i ∈ I, (p i).rho (w i) = ρ)
    (hρ0 : 0 ≤ ρ) (hcard : m / 40 ≤ (I.card : ℝ)) (hL : L ≤ m*ρ) :
    vectorPosterior p right x (Set.pi (I : Set ι) (fun i => (crossingPartner (right i) (u i))ᶜ)) ≤
      ENNReal.ofReal (Real.exp (-L/400)) := by
  apply (vectorPosterior_noncrossing_le_exp p right w x u I hx hu heligible).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he : (∑ i ∈ I, (p i).rho (w i)/10) = I.card * (ρ/10) := by
    calc
      _ = ∑ i ∈ I, ρ/10 := Finset.sum_congr rfl (fun i hi => by rw [hρ i hi])
      _ = _ := by simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hcard hρ0
  nlinarith

end CouplingParameters
end
end FiniteFactor

end OAI
