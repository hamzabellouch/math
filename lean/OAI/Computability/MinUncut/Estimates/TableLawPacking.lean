import Mathlib
import OAI.Computability.MinUncut.Analysis.LiteralGaussian

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

def sourceTable (σ η : ℝ) (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    ScoreIndex m n → Bool := fun s => if s.1 then query (c+σ•g) (η•l) s.2 else query c 0 s.2

lemma sourceTable_packed (σ η : ℝ) (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    sourceTable σ η c g l=thresholdTable (scoreFamily σ η) (packEquiv (c,g,l)) := by
  funext s
  exact (scoreFamily_packed σ η s (c,g,l)).symm

lemma table_integral_pack (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    (∫ c, ∫ g, ∫ l, F (sourceTable σ η c g l) ∂gauss (Code m n)
      ∂gauss (Point m n) ∂gauss (Point m n))=
      ∫ x, F (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) := by
  have ht := tableTest_integrable (scoreFamily σ η) F hF
  have hp := pack_preserving (X := Point m n) (C := Code m n)
  have hi : Integrable (fun p : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      F (thresholdTable (scoreFamily σ η) (packEquiv p))) (productLaw (Point m n) (Code m n)) :=
    hp.integrable_comp_of_integrable ht
  rw [← hp.integral_comp packEquiv.measurableEmbedding (fun x => F (thresholdTable (scoreFamily σ η) x))]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with c hc
  rw [integral_prod _ hc]
  apply integral_congr_ae
  filter_upwards [] with g
  apply integral_congr_ae
  filter_upwards [] with l
  rw [sourceTable_packed]

lemma sourceTest_integrable (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    Integrable (fun p : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      F (sourceTable σ η p.1 p.2.1 p.2.2)) (productLaw (Point m n) (Code m n)) := by
  simp_rw [sourceTable_packed]
  exact (pack_preserving (X := Point m n) (C := Code m n)).integrable_comp_of_integrable
    (tableTest_integrable (scoreFamily σ η) F hF)

lemma sourceTest_inner_integrable (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) (c : Point m n → ℝ) :
    Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      F (sourceTable σ η c p.1 p.2)) ((gauss (Point m n)).prod (gauss (Code m n))) := by
  simp_rw [sourceTable_packed]
  apply Integrable.of_bound
    (((measurable_of_countable F).comp (thresholdTable_measurable (scoreFamily σ η))).comp
      (packEquiv.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1
  filter_upwards [] with p
  simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (hF _).1]
    using (hF (thresholdTable (scoreFamily σ η) (packEquiv (c,p)))).2

lemma sourceTest_outer_integrable (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    Integrable (fun c => ∫ g, ∫ l, F (sourceTable σ η c g l) ∂gauss (Code m n)
      ∂gauss (Point m n)) (gauss (Point m n)) := by
  have hi := (sourceTest_integrable σ η F hF).integral_prod_left
  have he (c : Point m n → ℝ) := integral_prod
    (fun p : (Point m n → ℝ) × (Code m n → ℝ) => F (sourceTable σ η c p.1 p.2))
    (sourceTest_inner_integrable σ η F hF c)
  change Integrable (fun c => ∫ p : (Point m n → ℝ) × (Code m n → ℝ),
    F (sourceTable σ η c p.1 p.2) ∂(gauss (Point m n)).prod (gauss (Code m n)))
    (gauss (Point m n)) at hi
  simpa only [he] using hi

lemma table_integral_product (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    (∫ c, ∫ p : (Point m n → ℝ) × (Code m n → ℝ), F (sourceTable σ η c p.1 p.2)
      ∂(gauss (Point m n)).prod (gauss (Code m n)) ∂gauss (Point m n))=
      ∫ x, F (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) := by
  rw [← table_integral_pack σ η F hF]
  apply integral_congr_ae
  filter_upwards [] with c
  exact integral_prod _ (sourceTest_inner_integrable σ η F hF c)

end MinUncut.FiniteGaussian

end
end

end OAI
