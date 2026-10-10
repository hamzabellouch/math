import OAI.Probability.DilutedSpin.AveragedEnergyRoot

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma integrable_energyRoot_all (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (μ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    Integrable (fun z : ((RootPath Y N) × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
      energyRoot Q m field factor z.1.1 z.1.2 z.2)
      (((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s)).prod μ) := by
  have hc : Integrable (fun a : Sigma (RootPath I) => (a.1:ℝ)) (compoundRootLaw ν s) :=
    familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s
  have hb := ((hμ.norm.comp_snd ((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s))).add
    (integrable_const (H*N))).add (((hc.comp_snd (rootLaw N (fun _ => ξ))).comp_fst μ).const_mul D)
  apply hb.mono' (((measurable_energyRoot Q m field hhm factor).comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq,Function.comp_apply] using energyRoot_bound Q m hm field factor hh hf z.1.1 z.1.2 z.2)

lemma integral_averagedEnergyRoot (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (μ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    (∫ h,∫ a,∫ E,energyRoot Q m field factor h a E ∂μ
      ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ)) =
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor E ∂μ := by
  have hi := integrable_energyRoot_all ξ ν s μ hμ Q m hm field hhm factor hh hf
  rw [← integral_prod _ hi.integral_prod_left,integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [hi.swap.prod_right_ae] with E hE
  exact integral_prod _ hE

end DilutedSpinGlass.PhysicalRoot

end

end OAI
