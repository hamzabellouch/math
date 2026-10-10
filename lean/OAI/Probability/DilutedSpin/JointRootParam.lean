import OAI.Probability.DilutedSpin.RegularDepth

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y U : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] [MeasurableSpace U] {M : ℕ}

/-- Joint measurability through both random counts, with an external parameter. -/
theorem measurable_packRoot_param
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → U → ℝ}
    (hF : ∀ k n, Measurable (fun z : ((RootPath Y M × RootPath X k) × RootPath I n) × U => F z.1.1.1 k z.1.1.2 n z.1.2 z.2)) :
    Measurable (fun z : FullRootState Y X I M × U => packRoot (fun h k x n y => F h k x n y z.2) z.1) := by
  have hn (k : ℕ) : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × Sigma (RootPath I) =>
      F z.1.1.1 k z.1.1.2 z.2.1 z.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × RootPath X k) × U) n y => F z.1.1 k z.1.2 n y z.2)
      (fun n => (hF k n).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  have hk : Measurable (fun z : ((RootPath Y M × Sigma (RootPath I)) × U) × Sigma (RootPath X) =>
      F z.1.1.1 z.2.1 z.2.2 z.1.1.2.1 z.1.1.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × Sigma (RootPath I)) × U) k x => F z.1.1 k x z.1.2.1 z.1.2.2 z.2)
      (fun k => (hn k).comp (((measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd).prodMk measurable_fst.fst.snd))
  exact hk.comp (((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd).prodMk measurable_fst.snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

omit [MeasurableSpace U] in
theorem fullRoot_count_memLp :
    MemLp (fun z : FullRootState Y X I M => (z.2.2.1 : ℝ)) 2 (fullRootLaw ξ μ ν r s) := by
  exact ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)

omit [MeasurableSpace U] in
theorem fullRoot_count_mean :
    (∫ z : FullRootState Y X I M, (z.2.2.1 : ℝ) ∂fullRootLaw ξ μ ν r s) = s := by
  change (∫ z, (fun w : Sigma (RootPath X) × Sigma (RootPath I) => (w.2.1:ℝ)) z.2
    ∂(rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))) = _
  rw [integral_fun_snd (fun w : Sigma (RootPath X) × Sigma (RootPath I) => (w.2.1:ℝ)),
    integral_fun_snd (fun w : Sigma (RootPath I) => (w.1:ℝ))]
  simp only [probReal_univ,one_smul]
  exact familyPoisson_count_mean (fun n => rootLaw n (fun _ => ν)) s

end DilutedSpinGlass
end

end

end OAI
