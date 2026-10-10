import Mathlib
import OAI.Probability.SKRatio.Gaussian.GaussianEvents
import OAI.Probability.SKRatio.Entropy.GibbsObservation
import OAI.Probability.SKRatio.FiniteChain.StaticReduction

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
attribute [local instance] Classical.propDecidable
open Calculus

theorem functional_inequalities_high_probability {β : ℝ}
    (hβ : 0 ≤ β) (hβhalf : β < 1/2) :
    ∃ δ ρ χ : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < χ ∧
      Tendsto (fun n : ℕ => disorderLaw β n (matrixGood β δ n)ᶜ) atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ g ∈ matrixGood β δ n,
        euclideanOpNorm (coupling g) ≤ 2 ∧
        (∀ f : Observables n, ρ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f) ∧
        (∀ f : Observables n, (∀ x, 0 < f x) →
          χ*FiniteLaw.entropy (mass g 0) f ≤
            -stationaryInner g (generator (coupling g) f) (fun x => log (f x))) := by
  obtain ⟨δ,ρ,hd,hr,hgap⟩ := Fields.exists_uniform_gap_tolerance hβ hβhalf
  let d := min δ 1
  have hdp : 0 < d := lt_min hd zero_lt_one
  have hdδ : d ≤ δ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  refine ⟨d,ρ,exp (-16/ρ),hdp,hr,exp_pos _,matrixGood_probability hβ hdp,?_⟩
  intro n g hg
  have hnorm : euclideanOpNorm (coupling g) ≤ 2 := hg.1.trans (by linarith)
  have hboth := hgap n g (hg.1.trans (by linarith))
    (fun i j => (hg.2.1 i j).trans hdδ) (fun i => (hg.2.2 i).trans (by linarith))
  refine ⟨hnorm,?_,?_⟩
  · intro f
    have hh := (hboth 1 ⟨by norm_num,le_rfl⟩ 0).1 f
    simpa only [one_smul,Fields.variance_eq_finiteLaw,
      Fields.dirichlet_zero_eq_stationaryEnergy] using hh
  · intro f hf
    exact Observation.zero_field_mlsi g hnorm hr (fun s hs h => (hboth s hs h).2) f hf

theorem ratio_cutoff_of_typical_gradient (β ε η : ℝ)
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n)) (bad : ∀ n, Disorder n → Set (Spin n))
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hsmall : ∀ n, ∀ g ∈ G n, FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ bad n g then 1 else 0) ≤ exp (-κ*n))
    (hgradient : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ y,
      (∑ i, 2*halfDiff i f y*halfDiff i (generator (coupling g) f) y) -
        generator (coupling g) (unweightedGradient f) y ≤
          (-κ + if y ∈ bad n g then A else 0)*unweightedGradient f y) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  classical
  obtain ⟨δ,ρ,χ,hd,hr,hχ,hprob,hfun⟩ := functional_inequalities_high_probability hβ hβhalf
  let F := fun n => G n ∩ matrixGood β δ n
  have hF : Tendsto (fun n => disorderLaw β n (F n)ᶜ) atTop (𝓝 0) := by
    have hb (n : ℕ) : disorderLaw β n (F n)ᶜ ≤
        disorderLaw β n (G n)ᶜ + disorderLaw β n (matrixGood β δ n)ᶜ := by
      dsimp [F]
      rw [Set.compl_inter]
      exact measure_union_le _ _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hG.add hprob)
      (fun n => bot_le) hb
  apply ratio_cutoff_of_static_inputs β ε η hε (by linarith) hη F bad hκ hA hχ hr
    (by norm_num : (0:ℝ)<2) hF
  · intro n g hg
    exact (hfun n g hg.2).1
  · intro n g hg
    exact (hfun n g hg.2).2.1
  · intro n g hg f hf _
    exact (hfun n g hg.2).2.2 f hf
  · intro n g hg
    exact hsmall n g hg.1
  · intro n g hg
    exact hgradient n g hg.1

end SKRatio.Gaussian

end
end

end OAI
