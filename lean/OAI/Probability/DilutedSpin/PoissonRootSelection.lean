import OAI.Probability.DilutedSpin.PoissonReplacement
import OAI.Probability.DilutedSpin.PoissonSiteThinning

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
lemma successCountAt_le {p k : ℕ} [NeZero p] (s : Fin p) (a : Fin k → Fin p) :
    successCountAt s a≤k := by
  unfold successCountAt
  apply (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) =>
    show (if a i=s then 1 else 0)≤1 by split_ifs <;> omega)).trans_eq
  simp

lemma integral_poisson_rootSelection (r : ℝ≥0) (N : ℕ) [NeZero N] (s : Fin N)
    (f : ℕ → ℝ) {B D : ℝ} (hD : 0≤D) (hf : ∀ n,|f n|≤B+D*n) :
    (∫ k,∫ c,f (selectedCount k (rootMap (fun a => decide (a=s)) k c))
      ∂rootLaw k (fun _ => finiteUniform (Fin N)) ∂poissonMeasure r)=
      ∫ n,f n ∂poissonMeasure (r/N) := by
  let ν := fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin N))
  have hi : Integrable (fun z : (k : ℕ) × (Fin k → Fin N) => f (successCountAt s z.2))
      (familyLaw (poissonMeasure r) ν) := by
    apply familyLaw_integrable_bound (poissonMeasure r) ν
      (fun k (a : Fin k → Fin N) => f (successCountAt s a)) (fun _ => measurable_of_countable _)
      ((integrable_const B).add ((poisson_integrable_count r).const_mul D))
    intro k a
    exact (hf _).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (show (successCountAt s a:ℝ)≤k by exact_mod_cast successCountAt_le s a) hD) B)
  rw [←map_poisson_successCountAt r N s,
    integral_map (measurable_sigmaUncurry (fun k => measurable_of_countable
      (fun a : Fin k → Fin N => successCountAt s a))).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable,
    integral_familyLaw (poissonMeasure r) ν (fun k (a : Fin k → Fin N) => f (successCountAt s a))
      (fun _ => measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [] with k
  simp_rw [selectedCount_eq_successCountAt]
  exact integral_rootArray_eq_pi _ k (fun c => f (successCountAt s c))

end DilutedSpinGlass

end

end OAI
