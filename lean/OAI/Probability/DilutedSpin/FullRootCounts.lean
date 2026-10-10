import OAI.Probability.DilutedSpin.CompoundMoment
import OAI.Probability.DilutedSpin.CompoundSuperposition
import OAI.Probability.DilutedSpin.RandomInsertion

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory SizeCoupling
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] {M : ℕ}

lemma integral_twoCompound_counts
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : RootPath X k × RootPath I n => F k z.1 n z.2))
    {B C D : ℝ} (hb : ∀ k x n a,|F k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,F z.1.1 z.1.2 z.2.1 z.2.2 ∂(compoundRootLaw μ r).prod (compoundRootLaw ν s)) =
      ∫ k : ℕ,∫ n : ℕ,∫ a,∫ x,F k x n a ∂rootLaw k (fun _ => μ)
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂poissonMeasure r := by
  have hm : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F z.1.1 z.1.2 z.2.1 z.2.2) := by
    exact measurable_sigmaProd (f := fun k x (a : Sigma (RootPath I)) => F k x a.1 a.2)
      (fun k => measurable_prodSigma (f := fun x n a => F k x n a) (hf k))
  have hi := twoCompound_integrable_quadratic μ ν r s hm hb
  rw [integral_prod _ hi]
  have hg (k : ℕ) : Measurable (fun x : RootPath X k => ∫ a : Sigma (RootPath I),
      F k x a.1 a.2 ∂compoundRootLaw ν s) := by
    exact (measurable_prodSigma (hf k)).stronglyMeasurable.integral_prod_right'.measurable
  change (∫ z : Sigma (RootPath X),∫ a : Sigma (RootPath I),F z.1 z.2 a.1 a.2
    ∂compoundRootLaw ν s ∂familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))) = _
  rw [integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k x => ∫ a : Sigma (RootPath I),F k x a.1 a.2 ∂compoundRootLaw ν s) hg hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with k
  have he (x : RootPath X k) :
      (∫ a : Sigma (RootPath I),F k x a.1 a.2 ∂compoundRootLaw ν s)=
        ∫ n : ℕ,∫ a,F k x n a ∂rootLaw n (fun _ => ν) ∂poissonMeasure s := by
    have hfm (n : ℕ) : Measurable (F k x n) := (hf k n).comp (measurable_const.prodMk measurable_id)
    exact integral_familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))
      (F k x) hfm (familyLaw_integrable_bound _ _ _ hfm
        ((integrable_const (B+C*(k:ℝ)^2)).add ((poisson_integrable_count_sq s).const_mul D)) (hb k x))
  simp_rw [he]
  have hgm : Measurable (fun z : RootPath X k × ℕ =>
      ∫ a,F k z.1 z.2 a ∂rootLaw z.2 (fun _ => ν)) := by
    apply measurable_from_prod_countable_left
    intro n
    exact ((hf k n).stronglyMeasurable.integral_prod_right' (ν := rootLaw n (fun _ => ν))).measurable
  have hbi : Integrable (fun z : RootPath X k × ℕ => B+C*(k:ℝ)^2+D*(z.2:ℝ)^2)
      ((rootLaw k (fun _ => μ)).prod (poissonMeasure s)) :=
    (integrable_const (B+C*(k:ℝ)^2)).add
      (((poisson_integrable_count_sq s).const_mul D).comp_snd (rootLaw k (fun _ => μ)))
  have hgi : Integrable (fun z : RootPath X k × ℕ => ∫ a,F k z.1 z.2 a ∂rootLaw z.2 (fun _ => ν))
      ((rootLaw k (fun _ => μ)).prod (poissonMeasure s)) :=
    hbi.mono' hgm.aestronglyMeasurable (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hb k z.1 z.2)))
  rw [integral_integral_swap hgi]
  apply integral_congr_ae
  filter_upwards [] with n
  exact integral_integral_swap (Integrable.of_bound (hf k n).aestronglyMeasurable
    (B+C*(k:ℝ)^2+D*(n:ℝ)^2) (ae_of_all _ (fun z => by
      change |F k z.1 n z.2| ≤ _
      exact hb k z.1 n z.2)))

lemma integral_fullRootLaw_counts
    (ξ : Fin M → Measure Y) [∀ i,IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n a,|F h k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ k : ℕ,∫ n : ℕ,∫ a,∫ x,∫ h,F h k x n a ∂rootLaw M ξ
        ∂rootLaw k (fun _ => μ) ∂rootLaw n (fun _ => ν)
        ∂poissonMeasure s ∂poissonMeasure r := by
  have hi := fullRoot_integrable_quadratic ξ μ ν r s hf hb
  rw [fullRootLaw,integral_prod_symm _ hi]
  apply integral_twoCompound_counts μ ν r s
    (F := fun k x n a => ∫ h,F h k x n a ∂rootLaw M ξ) (B := B) (C := C) (D := D)
  · intro k n
    have hh : Measurable (fun z : (RootPath X k × RootPath I n) × RootPath Y M =>
        F z.2 k z.1.1 n z.1.2) :=
      (hf k n).comp ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  · intro k x n a
    exact abs_integral_le_const _ (fun h => hb h k x n a)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

lemma summable_measure_real_mul {X : Type} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ) :
    Summable (fun x => μ.real {x} * f x) := by
  rw [← Measure.sum_smul_dirac μ] at hf
  have he := (hasSum_integral_measure hf).summable
  simpa only [integral_smul_measure,integral_dirac,ENNReal.smul_def,smul_eq_mul,measureReal_def] using he

lemma poisson_mixture_double_limit (r : ℝ≥0) (f : ℕ → ℕ → ℕ → ℝ)
    {B C : ℝ} (hf : ∀ k L n,0≤f k L n) (hb : ∀ k L n,f k L n≤B+C*k)
    (hlim : ∀ k,Tendsto (fun L => limsup (f k L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (fun n => ∫ k,f k L n ∂poissonMeasure r) atTop) atTop (𝓝 0) := by
  have hi (L n : ℕ) : Integrable (fun k => f k L n) (poissonMeasure r) :=
    poisson_integrable_linear r (fun k => by rw [abs_of_nonneg (hf k L n)]; exact hb k L n)
  have he (L n : ℕ) : (∫ k,f k L n ∂poissonMeasure r)=
      ∑' k,(poissonMeasure r).real {k}*f k L n := by
    simpa only [smul_eq_mul] using integral_countable (hi L n)
  simp_rw [he]
  exact mixture_double_limit f (fun k => (poissonMeasure r).real {k}) (fun k => B+C*k)
    (fun _ => measureReal_nonneg) hf hb
    (summable_measure_real_mul _ ((integrable_const B).add ((poisson_integrable_count r).const_mul C))) hlim

end DilutedSpinGlass

end

end OAI
