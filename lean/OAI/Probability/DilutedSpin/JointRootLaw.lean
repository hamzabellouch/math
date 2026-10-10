import OAI.Probability.DilutedSpin.HeterogeneousFullVariance

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The actual independent Poisson container of iid root labels. -/
noncomputable def compoundRootLaw {X : Type} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ≥0) : Measure (Sigma (RootPath X)) :=
  familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))

instance compoundRootLaw_prob {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (r : ℝ≥0) : IsProbabilityMeasure (compoundRootLaw μ r) := by
  unfold compoundRootLaw
  infer_instance

theorem measurable_prodSigma {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    {f : A → (i : I) → X i → Y}
    (hf : ∀ i, Measurable (fun z : A × X i => f z.1 i z.2)) :
    Measurable (fun z : A × Sigma X => f z.1 z.2.1 z.2.2) := by
  exact (measurable_sigmaProd (f := fun i x a => f a i x) (fun i => (hf i).comp measurable_swap)).comp measurable_swap

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

abbrev FullRootState (Y X I : Type) (M : ℕ) :=
  RootPath Y M × (Sigma (RootPath X) × Sigma (RootPath I))

noncomputable def fullRootLaw (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I)
    (r s : ℝ≥0) : Measure (FullRootState Y X I M) :=
  (rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))

instance fullRootLaw_prob (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0) : IsProbabilityMeasure (fullRootLaw ξ μ ν r s) := by
  unfold fullRootLaw
  infer_instance

noncomputable def packRoot (F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ)
    (z : FullRootState Y X I M) : ℝ := F z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_memLp_linear
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*k+D*n) :
    MemLp (packRoot F) 2 (fullRootLaw ξ μ ν r s) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : MemLp (fun z : FullRootState Y X I M => B+C*z.2.1.1+D*z.2.2.1) 2
      (fullRootLaw ξ μ ν r s) := (memLp_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))

/-- Quadratic envelopes allow both the pressure and its square to be passed
through the two independent compound laws, without any count cut-off. -/
theorem fullRoot_integrable_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (packRoot F) (fullRootLaw ξ μ ν r s) := by
  have hk := (((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := (((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : Integrable (fun z : FullRootState Y X I M => B+C*(z.2.1.1:ℝ)^2+D*(z.2.2.1:ℝ)^2)
      (fullRootLaw ξ μ ν r s) := (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))


theorem twoCompound_integrable_quadratic
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2))
    {B C D : ℝ} (hb : ∀ k x n y, |F k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2)
      ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)
  have he : Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      B+C*(z.1.1:ℝ)^2+D*(z.2.1:ℝ)^2) ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) :=
    (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' hF.aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using hb z.1.1 z.1.2 z.2.1 z.2.2))

/-- Exact Fubini identity for the full root law, with all count-dependent
root spaces and all physical fields retained. -/
theorem integral_fullRootLaw_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, F h k x n y
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hm := measurable_packRoot hF
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hF hb)]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  have hhm : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) := hm.comp (measurable_const.prodMk measurable_id)
  have hhi := twoCompound_integrable_quadratic μ ν r s hhm (hb h)
  change (∫ z, F h z.1.1 z.1.2 z.2.1 z.2.2 ∂(compoundRootLaw μ r).prod (compoundRootLaw ν s)) = _
  rw [integral_prod _ hhi]
  have hg (k : ℕ) : Measurable (fun x : RootPath X k =>
      ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s) := by
    have hh : Measurable (fun z : RootPath X k × Sigma (RootPath I) => F h k z.1 z.2.1 z.2.2) :=
      hhm.comp (((measurable_sigmaMk k).comp measurable_fst).prodMk measurable_snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  change (∫ z : Sigma (RootPath X), ∫ w : Sigma (RootPath I),
    F h z.1 z.2 w.1 w.2 ∂compoundRootLaw ν s
      ∂familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))) = _
  rw [integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k x => ∫ z : Sigma (RootPath I), F h k x z.1 z.2 ∂compoundRootLaw ν s)
      hg hhi.integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hfm (n : ℕ) : Measurable (F h k x n) :=
    (hF k n).comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  exact integral_familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
    (F h k x) hfm
    (familyLaw_integrable_bound (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
      (F h k x) hfm
      ((integrable_const (B+C*(k:ℝ)^2)).add ((poisson_integrable_count_sq s).const_mul D))
      (hb h k x))

end DilutedSpinGlass
end

end

end OAI
