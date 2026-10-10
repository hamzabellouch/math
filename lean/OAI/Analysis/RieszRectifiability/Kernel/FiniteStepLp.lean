import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteStepMoments

namespace OAI

/-!
# Finite-step functions in L²

Finite-step functions on finite measures belong to L². Products are represented on
intersections of cells, expressing squared distances through cell masses and mixed moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem finiteStep_memLp (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) (a : ι → ℝ) :
    MemLp (finiteStep s a) 2 μ := by
  classical
  exact memLp_finsetSum _ (fun i _ => (memLp_const (a i)).indicator (hs i))

omit [MeasurableSpace X] in
theorem finiteStep_mul (s : ι → Set X) (t : κ → Set X)
    (a : ι → ℝ) (b : κ → ℝ) :
    finiteStep s a * finiteStep t b =
      finiteStep (fun p : ι × κ => s p.1 ∩ t p.2) (fun p => a p.1 * b p.2) := by
  classical
  funext x
  simp only [Pi.mul_apply, finiteStep, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : x ∈ s i <;> by_cases hy : x ∈ t j <;> simp [hx, hy]

theorem integral_finiteStep_mul (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (t : κ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ j, MeasurableSet (t j))
    (a : ι → ℝ) (b : κ → ℝ) :
    (∫ x, finiteStep s a x * finiteStep t b x ∂μ) =
      ∑ i, ∑ j, μ.real (s i ∩ t j) * (a i * b j) := by
  change (∫ x, (finiteStep s a * finiteStep t b) x ∂μ) = _
  rw [finiteStep_mul s t a b]
  rw [integral_finiteStep μ (fun p : ι × κ => s p.1 ∩ t p.2)
    (fun p => (hs p.1).inter (ht p.2))]
  exact Fintype.sum_prod_type _

theorem toLp_norm_sq_eq_integral (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem toLp_dist_sq_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [dist_eq_norm]
  have heq : hf.toLp f - hg.toLp g = (hf.sub hg).toLp (f - g) := by
    exact (MemLp.toLp_sub hf hg).symm
  rw [heq, toLp_norm_sq_eq_integral]
  rfl

theorem finiteStep_cross_distance_tendsto (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (s : ι → Set X) (t : κ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hds : Pairwise (Disjoint on s)) (hdt : Pairwise (Disjoint on t))
    (a : ι → ℝ) (b : κ → ℝ)
    (hms : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (ν.real (s i))))
    (hmt : ∀ i, Tendsto (fun j => (μ j).real (t i)) atTop (𝓝 (ν.real (t i))))
    (hmst : ∀ i k, Tendsto (fun j => (μ j).real (s i ∩ t k))
      atTop (𝓝 (ν.real (s i ∩ t k)))) :
    Tendsto (fun j => ∫ x, (finiteStep s a x - finiteStep t b x) ^ 2 ∂μ j)
      atTop (𝓝 (∫ x, (finiteStep s a x - finiteStep t b x) ^ 2 ∂ν)) := by
  have hformula (ρ : Measure X) [IsFiniteMeasure ρ] :
      (∫ x, (finiteStep s a x - finiteStep t b x) ^ 2 ∂ρ) =
        (∑ i, ρ.real (s i) * a i ^ 2) -
        2 * (∑ i, ∑ k, ρ.real (s i ∩ t k) * (a i * b k)) +
        (∑ k, ρ.real (t k) * b k ^ 2) := by
    have hprod : MemLp (fun x => finiteStep s a x * finiteStep t b x) 1 ρ :=
      (finiteStep_memLp ρ s hs a).mul (finiteStep_memLp ρ t ht b)
    rw [integral_squared_difference ρ _ _
      (finiteStep_memLp ρ s hs a).integrable_sq
      (memLp_one_iff_integrable.mp hprod)
      (finiteStep_memLp ρ t ht b).integrable_sq,
      integral_finiteStep_sq ρ s hs hds, integral_finiteStep_sq ρ t ht hdt,
      integral_finiteStep_mul ρ s t hs ht]
  simp_rw [hformula]
  exact ((tendsto_finsetSum _ fun i _ => (hms i).mul_const _).sub
    ((tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun k _ => (hmst i k).mul_const _).const_mul 2)).add
    (tendsto_finsetSum _ fun k _ => (hmt k).mul_const _)

end

end RieszRectifiability

end OAI
