import OAI.Analysis.IrrationalRotation.Sampling.ProductInfiniteSamplingMoments
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import OAI.Analysis.IrrationalRotation.Model.ProductBase
import OAI.Analysis.IrrationalRotation.Sampling.UniformIntervalPhase

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductSampling

theorem measurePreserving_all_representatives :
    MeasurePreserving (fun x : ProductModel.Base => fun i => circleRepresentative (x i))
      ProductModel.baseMeasure
      (Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Ico (0 : ℝ) 1))) := by
  have hr : Measurable circleRepresentative :=
    CocycleSupport.measurePreserving_circleRepresentative.measurable
  refine ⟨by fun_prop, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure)).map
      (fun x i => circleRepresentative (x i)) = _
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => circleMeasure) (fun _ => hr)]
  congr 1
  funext i
  exact CocycleSupport.measurePreserving_circleRepresentative.map_eq

theorem integral_iterated_all_representatives
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (F : Ω → (ℕ → ℝ) → ℝ)
    (hF : Integrable (fun p : Ω × (ℕ → ℝ) => F p.1 p.2)
      (μ.prod (Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Ico (0 : ℝ) 1))))) :
    (∫ a, ∫ x : ProductModel.Base, F a (fun i => circleRepresentative (x i))
      ∂ProductModel.baseMeasure ∂μ) =
      ∫ a, ∫ x, F a x
        ∂Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Ico (0 : ℝ) 1)) ∂μ := by
  let : IsProbabilityMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ico]⟩
  have hmp := (MeasurePreserving.id μ).prod measurePreserving_all_representatives
  have hpull := hmp.integrable_comp_of_integrable hF
  change Integrable (fun p : Ω × ProductModel.Base =>
    F p.1 (fun i => circleRepresentative (p.2 i))) _ at hpull
  rw [← integral_prod _ hpull, ← integral_prod _ hF]
  have hm := hF.aestronglyMeasurable
  rw [← hmp.map_eq] at hm
  simpa only [hmp.map_eq, Prod.map_fst, Prod.map_snd, id_eq] using
    (integral_map hmp.measurable.aemeasurable hm).symm

theorem expected_source_real_prefix_error_le
    {ι : Type*} (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (D : Finset ℕ) (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℕ → ℝ → ℝ → ℝ) (z : ℕ → ℝ → ℝ)
    (hv : ∀ n, ∀ i ∈ D,
      MemLp (fun p : ℝ × ℝ => v n i p.1 p.2) 2
        ((UniformIntervalPhase.lambdaLaw (S i)).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1))))
    (hz : ∀ i ∈ D, MemLp (z i) 2 (volume.restrict (Set.Ico (0 : ℝ) 1)))
    {B K ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i ∈ D,
      (∫ x, (z i x) ^ 2 ∂volume.restrict (Set.Ico (0 : ℝ) 1)) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i ∈ D,
      (∫ p : ℝ × ℝ, (v n i p.1 p.2) ^ 2
        ∂(UniformIntervalPhase.lambdaLaw (S i)).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1))) ≤ K)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i ∈ D,
      |(∫ p : ℝ × ℝ, v n i p.1 p.2 * v m i p.1 p.2
        ∂(UniformIntervalPhase.lambdaLaw (S i)).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1))) -
        (∫ x, (z i x) ^ 2 ∂volume.restrict (Set.Ico (0 : ℝ) 1))| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i ∈ D,
      |(∫ p : ℝ × ℝ, v n i p.1 p.2 * z i p.2
        ∂(UniformIntervalPhase.lambdaLaw (S i)).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1))) -
        (∫ x, (z i x) ^ 2 ∂volume.restrict (Set.Ico (0 : ℝ) 1))| ≤ ε) :
    (∫ θ, ∫ x : ProductModel.Base,
      ((s.card : ℝ)⁻¹ *
        (∑ n ∈ s, ∏ i ∈ D, v n i (θ i) (circleRepresentative (x i))) -
        ∏ i ∈ D, z i (circleRepresentative (x i))) ^ 2 ∂ProductModel.baseMeasure
        ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
          (Set.Icc (1 / S i) (2 / S i)))) ≤
      K ^ D.card / (s.card : ℝ) +
        3 * ((D.card : ℝ) * ε * (B + ε) ^ (D.card - 1)) := by
  let μ : ℕ → Measure ℝ := fun i => UniformIntervalPhase.lambdaLaw (S i)
  let ν : ℕ → Measure ℝ := fun _ => volume.restrict (Set.Ico (0 : ℝ) 1)
  let : IsProbabilityMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ico]⟩
  let (i : ℕ) : IsProbabilityMeasure (μ i) :=
    UniformIntervalPhase.lambdaLaw_probability (S i) (hS i)
  let : ∀ i, IsProbabilityMeasure (ν i) := fun _ => inferInstance
  let F : (ℕ → ℝ) → (ℕ → ℝ) → ℝ := fun a b =>
    ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i : D, v n i (a i) (b i)) -
      ∏ i : D, z i (b i)) ^ 2
  have hfinite := integrable_average_coordinate_error_sq
    (fun i : D => μ i) (fun i : D => ν i) s
    (fun n i => v n i) (fun i => z i)
    (fun n i => hv n i i.property) (fun i => hz i i.property)
  have hmp := (measurePreserving_finset_restrict μ D).prod
    (measurePreserving_finset_restrict ν D)
  have hF := hmp.integrable_comp_of_integrable hfinite
  change Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => F p.1 p.2) _ at hF
  have heq := integral_iterated_all_representatives (Measure.infinitePi μ) F hF
  have hbound := expected_integral_infinite_average_products_sub_sq_le μ ν D s hs
    (fun n i => v n i) (fun i => z i)
    (fun n i => hv n i i.property) (fun i => hz i i.property) hB hε
    (fun i => hbase i i.property) (fun n hn i => hdiag n hn i i.property)
    (fun n hn m hm hnm i => hoff n hn m hm hnm i i.property)
    (fun n hn i => hcross n hn i i.property)
  have hμ : μ = (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / S i) (2 / S i))) :=
    funext (fun i => UniformIntervalPhase.lambdaLaw_eq_cond (S i) (hS i))
  have hprod (a b : ℕ → ℝ) (n : ι) :=
    Finset.prod_coe_sort D (fun i => v n i (a i) (b i))
  have hzprod (b : ℕ → ℝ) := Finset.prod_coe_sort D (fun i => z i (b i))
  simpa only [F, hμ, hprod, hzprod] using heq.trans_le hbound

end Invariant233.ProductSampling

end

end OAI
