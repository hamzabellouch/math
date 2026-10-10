import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedSelfConsistency

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma markedTimeLaw_geometry {K : ℝ} (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hs : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, (Q i j).1 = (Q j i).1)
    (hd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).1.val = 1)
    (hu : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j l,
      min (Q i j).1.val (Q i l).1.val ≤ (Q j l).1.val) :
    ∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l := by
  let e : BulkPairRange K → Time := fun p => nonnegativeSpinTime p.1
  have hc : Continuous e := nonnegativeSpinTime_continuous.comp continuous_fst
  have hmeas : MeasurableSet {Q : CompactArray Time |
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l} := by
    simp only [Set.ofPred_and,Set.ofPred_forall]
    exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter
      ((MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun l =>
        measurableSet_le (by fun_prop) (by fun_prop)))
  exact (ae_map_iff (compactMapArray_continuous hc).measurable.aemeasurable hmeas).mpr (by
  filter_upwards [hs,hd,hu] with Q hS hD hU
  refine ⟨fun i j => congrArg nonnegativeSpinTime (hS i j),?_,?_⟩
  · intro i
    apply Subtype.ext
    change max (Q i i).1.val 0 = 1
    rw [hD i]; norm_num
  · intro i j l
    change min (max (Q i j).1.val 0) (max (Q i l).1.val 0) ≤ max (Q j l).1.val 0
    rw [←max_min_distrib_right]
    exact max_le_max (hU i j l) le_rfl)

theorem bulk_marked_time_inputs (M : ℕ → ℕ) (g : Jet3) (v : ℕ → ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1 ≤ v n p)
    (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ → ℕ) (hs : StrictMono s) (K : ℝ)
    (hK : ∀ n, (M (s n) : ℝ) / (s n+1 : ℕ) * ‖g.d1‖^2 ≤ K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    (∀ n (i : Fin n) (F : CompactBlock Time n →ᵇ ℝ) (a : Time →ᵇ ℝ),
      compactGGDefect (markedTimeLaw K μ) n i F a = 0) ∧
    (∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l) ∧
    (∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=Time) e)
      (markedTimeLaw K μ : Measure _) (markedTimeLaw K μ : Measure _)) := by
  have hp := bulkMarkedArray_limit_overlap M g v s K hK hlim
  have hgeom := bulk_limit_geometry M g.f v hv hd hs hp
  have hex e := compact_exchangeability_limit hlim e
    (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)) g (v (s n)) K (hK n) e)
  have hmarked := marked_overlap_geometry K μ hex hgeom.1 hgeom.2.1
  refine ⟨?_,?_,?_⟩
  · rw [markedTimeLaw_factor]
    exact compactMapLaw_gg nonnegativeSpinTime nonnegativeSpinTime_continuous _
      (bulk_limit_gg M g.f v hv hd hs hp)
  · apply markedTimeLaw_geometry μ hmarked.1 _ hmarked.2.1
    exact ae_of_ae_map (compactMapArray_continuous (show Continuous
      (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable
      (bulkGibbsArray_limit_diagonal g.f M v s hp)
  · exact fun e => compactMapLaw_exchangeable _ _ μ e (hex e)



lemma bulkB_diagonal_nonneg (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x : NormalizedSpin N) : 0 ≤ bulkB N M f a x x := by
  unfold bulkB
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _index _ => mul_self_nonneg _)

lemma bulkB_add_diagonal_bound (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x y : NormalizedSpin N) :
    2 * bulkB N M f a x y ≤ bulkB N M f a x x + bulkB N M f a y y := by
  let u j := f.d1 (∑ i, a j i * x.val i)
  let v j := f.d1 (∑ i, a j i * y.val i)
  have h : ∑ j, (2 * (u j * v j)) ≤ ∑ j, (u j * u j + v j * v j) := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (u j - v j)]
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (N:ℝ)⁻¹)
  simpa only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_assoc,mul_left_comm,
    u,v,bulkB] using hh

lemma bulkMarkedArray_closed_full (n M : ℕ) (f : Jet3) (v : ℕ → ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2 ≤ K) {F : Set (CompactArray (BulkPairRange K))}
    (hF : IsClosed F)
    (hfull : ∀ a : BulkDisorder (n+1) M, ∀ x : ℕ → NormalizedSpin (n+1),
      bulkMarkedArray n M f K hK (a,x) ∈ F) :
    bulkMarkedArrayLaw n M f v K hK F = 1 := by
  have hp : bulkMarkedArray n M f K hK ⁻¹' F = univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.1 a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (bulkMarkedArray n M f K hK) _) F = 1
  rw [Measure.map_apply (bulkMarkedArray_measurable _ _ _ _ _) hF.measurableSet,hp]
  exact measure_univ

theorem bulkMarkedArray_limit_mark_geometry (M : ℕ → ℕ) (f : Jet3) (v : ℕ → ℕ → ℝ)
    (s : ℕ → ℕ) (K : ℝ) (hK : ∀ n, (M (s n):ℝ)/(s n+1:ℕ)*‖f.d1‖^2 ≤ K)
    {μ : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, 0 ≤ (Q i i).2.val) ∧
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j,
      2*(Q i j).2.val ≤ (Q i i).2.val + (Q j j).2.val) := by
  constructor
  · apply ae_all_iff.mpr
    intro i
    have hc : IsClosed {Q : CompactArray (BulkPairRange K) | 0 ≤ (Q i i).2.val} :=
      isClosed_le continuous_const (by fun_prop)
    apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
    have h := weak_limit_closed_full hlim hc (fun n => bulkMarkedArray_closed_full
      (s n) (M (s n)) f (v (s n)) K (hK n) hc
      (fun _disorder _spins => bulkB_diagonal_nonneg _ _ _ _ _))
    simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,h,ENNReal.coe_one]
  · apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    have hc : IsClosed {Q : CompactArray (BulkPairRange K) |
      2*(Q i j).2.val ≤ (Q i i).2.val + (Q j j).2.val} := isClosed_le (by fun_prop) (by fun_prop)
    apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
    have h := weak_limit_closed_full hlim hc (fun n => bulkMarkedArray_closed_full
      (s n) (M (s n)) f (v (s n)) K (hK n) hc
      (fun _disorder _spins => bulkB_add_diagonal_bound _ _ _ _ _ _))
    simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,h,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy

end

end OAI
