import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeApproximation

namespace OAI

/-! Finite amplitude approximations also converge in L1. Null levels
can be deleted without changing their almost-everywhere values. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudeApprox_integrable (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hf1 : Integrable f mu) (I : Finset ℤ) :
    Integrable (amplitudeApprox f I) mu := by
  rw [amplitudeApprox_eq_indicator]
  exact hf1.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hfm.norm i))

omit [MeasurableSpace X] in
theorem amplitudeApprox_norm_le (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) (x : X) :
    ‖amplitudeApprox f I x‖≤‖f x‖ := by
  rw [amplitudeApprox_eq_indicator]
  by_cases hx : x∈⋃ i∈I, amplitudeLevel f i
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx,norm_zero]
    exact norm_nonneg _

theorem amplitudeApprox_l1_tendsto (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hf1 : Integrable f mu) :
    Tendsto (fun n : ℕ => ∫ x, ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖ ∂mu)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ:=mu) (fun x => ‖f x‖)
    (F:=fun n x => ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖) (f:=fun _ => (0:ℝ))
    (fun n => (((amplitudeApprox_measurable hfm _).sub hfm).norm).aestronglyMeasurable)
    hf1.norm
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact amplitudeApprox_sub_norm_le f _ x))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [amplitudeApprox_eventually_eq f x] with n hn
      simp only [hn,sub_self,norm_zero]))
  simpa only [integral_zero] using h

theorem amplitudePiece_zero_ae (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hf2 : MemLp f 2 mu) (i : ℤ) (hi : mu.real (amplitudeLevel f i)=0) :
    amplitudePiece f i=ᵐ[mu] 0 := by
  have hz := (measureReal_eq_zero_iff (amplitudeLevel_finite mu hf2 i)).mp hi
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
  exact amplitudePiece_supported f i x hx

theorem amplitudeApprox_positive_filter_ae (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hf2 : MemLp f 2 mu) (I : Finset ℤ) :
    amplitudeApprox f (I.filter (fun i => 0<mu.real (amplitudeLevel f i)))=ᵐ[mu]
      amplitudeApprox f I := by
  classical
  unfold amplitudeApprox
  rw [Finset.sum_filter]
  apply eventuallyEq_sum
  intro i _
  by_cases hi : 0<mu.real (amplitudeLevel f i)
  · exact Filter.Eventually.of_forall (fun _ => by simp only [hi,ite_true])
  · have hz : mu.real (amplitudeLevel f i)=0 := le_antisymm (le_of_not_gt hi) measureReal_nonneg
    filter_upwards [amplitudePiece_zero_ae mu f hf2 i hz] with x hx
    simp only [hi,ite_false,Pi.zero_apply,Pi.smul_apply,hx,smul_zero]

theorem amplitudeApprox_positive_l1_tendsto (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hf1 : Integrable f mu) (hf2 : MemLp f 2 mu) :
    Tendsto (fun n : ℕ => ∫ x, ‖amplitudeApprox f
      ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<mu.real (amplitudeLevel f i))) x-f x‖ ∂mu)
      atTop (𝓝 0) := by
  have heq (n : ℕ) : (∫ x, ‖amplitudeApprox f
      ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<mu.real (amplitudeLevel f i))) x-f x‖ ∂mu)=
      ∫ x, ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖ ∂mu := by
    apply integral_congr_ae
    filter_upwards [amplitudeApprox_positive_filter_ae mu f hf2 (Finset.Icc (-(n:ℤ)) n)] with x hx
    rw [hx]
  simp_rw [heq]
  exact amplitudeApprox_l1_tendsto mu f hfm hf1

 theorem amplitudeApprox_positive_tendsto_ae (mu : Measure X) (f : X → EuclideanSpace ℂ κ)
    (hf2 : MemLp f 2 mu) :
    ∀ᵐ x ∂mu, Tendsto (fun n : ℕ => amplitudeApprox f
      ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<mu.real (amplitudeLevel f i))) x)
      atTop (𝓝 (f x)) := by
  have ha : ∀ᵐ x ∂mu, ∀ n : ℕ, amplitudeApprox f
      ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<mu.real (amplitudeLevel f i))) x=
      amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x :=
    ae_all_iff.mpr (fun n => amplitudeApprox_positive_filter_ae mu f hf2 _)
  filter_upwards [ha] with x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [amplitudeApprox_eventually_eq f x] with n hn
  rw [hx n,hn]

omit [MeasurableSpace X] in
theorem amplitudeApprox_coordinate_norm_le (f : X → EuclideanSpace ℂ κ)
    (I : Finset ℤ) (x : X) (k : κ) : ‖amplitudeApprox f I x k‖≤‖f x k‖ := by
  rw [amplitudeApprox_eq_indicator]
  by_cases hx : x∈⋃ i∈I, amplitudeLevel f i
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    simp only [WithLp.ofLp_zero,Pi.zero_apply,norm_zero,norm_nonneg]

end LipschitzHilbert

end

end OAI
