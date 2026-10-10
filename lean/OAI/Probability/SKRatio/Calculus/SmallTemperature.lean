import Mathlib
import OAI.Probability.SKRatio.Gaussian.GaussianEvents
import OAI.Probability.SKRatio.Variational.UniformDrift

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma rowControl_le {n : ℕ} (J : Interaction n) (k : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i, ∑ j, |J i j|^k ≤ B) : rowControl J k ≤ B := by
  change ((Finset.univ.sup (fun i => ∑ j, ‖J i j‖₊^k) : NNReal) : ℝ) ≤ B
  apply (NNReal.coe_le_coe (r₂ := ⟨B,hB⟩)).mpr
  apply Finset.sup_le
  intro i _
  have hh : ((∑ j, ‖J i j‖₊^k : NNReal) : ℝ) ≤ B := by
    simpa only [NNReal.coe_sum,NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs] using h i
  exact hh

lemma R3_le_entry_times_row {n : ℕ} (J : Interaction n) {δ B : ℝ}
    (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (he : ∀ i j, |J i j| ≤ δ) (hrow : ∀ i, ∑ j, J i j^2 ≤ B) :
    R3 J ≤ δ*B := by
  apply rowControl_le J 3 (mul_nonneg hδ hB)
  intro i
  calc
    _ ≤ ∑ j, δ*(J i j)^2 := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |J i j| *(J i j)^2 := by rw [pow_succ,sq_abs];ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (he i j) (sq_nonneg _)
    _ = δ*(∑ j, J i j^2) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow i) hδ

theorem uniform_gradient_small_temperature {β δ : ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 7/20) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/10000)
    {n : ℕ} (g : Disorder n) (hg : g ∈ Gaussian.matrixGood β δ n)
    (f : Observables n) (r : ℝ) (y : Spin n) :
    deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
      generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
        -(1/10:ℝ)*unweightedGradient (semigroup (coupling g) r f) y := by
  have hb2 : β^2 ≤ 49/400 := by
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hβsmall)]
  have hrow (i : Fin n) : ∑ j, coupling g i j^2 ≤ 1 := (hg.2.2 i).trans (by linarith)
  apply gradient_dissipation_small_norm (coupling g) (coupling_symm g) (coupling_diag g)
  · intro i j
    exact (hg.2.1 i j).trans (by linarith)
  · exact hg.1.trans (by linarith)
  · apply rowControl_le _ 2 (by norm_num)
    intro i
    simpa only [sq_abs] using (hg.2.2 i).trans (by linarith : β^2+δ ≤ 49/400+1/10000)
  · exact (R3_le_entry_times_row (coupling g) hδ (by norm_num : (0:ℝ) ≤ 1)
      hg.2.1 hrow).trans (by simpa only [mul_one] using hδsmall)

end SKRatio.Calculus

namespace SKRatio
open Calculus

theorem ratio_cutoff_small_temperature (β ε η : ℝ)
    (hβ0 : 0 ≤ β) (hβsmall : β ≤ 7/20)
    (hε0 : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  obtain ⟨δ,γ,hd,hγ,hgap⟩ := Fields.exists_uniform_gap_tolerance hβ0 (by linarith : β < 1/2)
  let d := min δ (1/10000:ℝ)
  have hdp : 0 < d := lt_min hd (by norm_num)
  have hdδ : d ≤ δ := min_le_left _ _
  have hds : d ≤ 1/10000 := min_le_right _ _
  let G := Gaussian.matrixGood β d
  have hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ 1 := by
    intro n g hg
    exact hg.1.trans (by linarith)
  have hgp (n : ℕ) (g : Disorder n) (hg : g ∈ G n) (f : Observables n) :
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f := by
    have h := (hgap n g (hg.1.trans (by linarith))
      (fun i j => (hg.2.1 i j).trans hdδ)
      (fun i => (hg.2.2 i).trans (by linarith)) 1 ⟨by norm_num,le_rfl⟩ 0).1 f
    simpa only [one_smul,Fields.variance_eq_finiteLaw,Fields.dirichlet_zero_eq_stationaryEnergy] using h
  apply ratio_cutoff_of_uniform_gradient β ε η hε0 (by linarith) hη G
    (by norm_num : (0:ℝ) < 1/10) hγ (by norm_num : (0:ℝ) < 1)
    (Gaussian.matrixGood_probability hβ0 hdp) hnorm hgp
  intro n g hg f r y
  exact uniform_gradient_small_temperature hβ0 hβsmall hdp.le hds g hg f r y

end SKRatio

end
end

end OAI
