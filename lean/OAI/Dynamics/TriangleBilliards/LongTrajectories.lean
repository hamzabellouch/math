import OAI.Dynamics.TriangleBilliards.ClearanceSmoothing

namespace OAI

universe uA uH

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open scoped NNReal

namespace FlightChain

lemma dist_point_succ {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) :
    dist (c.point n) (c.point (n + 1)) = c.time (n + 1) - c.time n := by
  rw [dist_comm, dist_eq_norm, c.flight, add_sub_cancel_left,
    norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr (c.increasing (by omega)))]

lemma dist_point_le {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {n m : ℤ} (hnm : n ≤ m) : dist (c.point n) (c.point m) ≤ c.time m - c.time n := by
  induction m, hnm using Int.leInduction with
  | base => simp only [dist_self, sub_self, le_refl]
  | succ m hnm ih =>
    calc
      dist (c.point n) (c.point (m + 1)) ≤
        dist (c.point n) (c.point m) + dist (c.point m) (c.point (m + 1)) := dist_triangle _ _ _
      _ ≤ c.time m - c.time n + (c.time (m + 1) - c.time m) :=
        add_le_add ih (c.dist_point_succ m).le
      _ = c.time (m + 1) - c.time n := by ring

lemma position_dist_le {Q : Triangle} {z : Phase} (c : FlightChain Q z) (s t : ℝ) :
    dist (c.at s).1 (c.at t).1 ≤ dist s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, dist_comm s t]
    exact this t s (le_of_not_ge hst)
  obtain ⟨n, hn⟩ := c.exists_flight s
  obtain ⟨m, hm⟩ := c.exists_flight t
  have hnm : n ≤ m := by
    by_contra h
    have hh := c.increasing.monotone (show m + 1 ≤ n by omega)
    linarith [hn.1, hm.2]
  rcases hnm.eq_or_lt with he | hnm
  · subst m
    rw [c.unit_speed_on_flight hn hm]
    exact le_refl _
  · have hsn : dist (c.at s).1 (c.point (n + 1)) = c.time (n + 1) - s := by
      rw [c.at_of_flight hn, c.flight, dist_eq_norm, add_sub_add_left_eq_sub,
        ← sub_smul, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs]
      have hh : (s - c.time n) - (c.time (n + 1) - c.time n) = s - c.time (n + 1) := by ring
      rw [hh, abs_of_neg (sub_neg.mpr hn.2)]
      ring
    have hmt : dist (c.point m) (c.at t).1 = t - c.time m := by
      rw [c.at_of_flight hm, dist_comm, dist_eq_norm, add_sub_cancel_left,
        norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hm.1)]
    calc
      dist (c.at s).1 (c.at t).1 ≤
        dist (c.at s).1 (c.point (n + 1)) + dist (c.point (n + 1)) (c.at t).1 :=
        dist_triangle _ _ _
      _ ≤ dist (c.at s).1 (c.point (n + 1)) +
        (dist (c.point (n + 1)) (c.point m) + dist (c.point m) (c.at t).1) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ (c.time (n + 1) - s) +
        ((c.time m - c.time (n + 1)) + (t - c.time m)) := by
        rw [hsn, hmt]
        gcongr
        exact c.dist_point_le (by omega)
      _ = dist s t := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]; ring

end FlightChain

lemma billiard_position_lipschitz (Q : Triangle) (z : Phase) :
    LipschitzWith 1 (fun t => (billiardFlow Q t z).1) := by
  classical
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  by_cases h : Nonempty (FlightChain Q z)
  · simpa only [billiardFlow, dite_eq_left h, NNReal.coe_one, one_mul] using
      (Classical.choice h).position_dist_le s t
  · simp only [billiardFlow, dite_eq_right h, dist_self, NNReal.coe_one, one_mul]
    exact dist_nonneg

namespace Triangle

lemma clearance_flow_lipschitz (Q : Triangle) (z : Phase) :
    LipschitzWith 1 (fun t => Q.clearance (billiardFlow Q t z).1) := by
  simpa only [mul_one, Function.comp_def] using Q.clearance_lipschitz.comp (billiard_position_lipschitz Q z)

end Triangle

end TriangularBilliards

namespace TriangularBilliards
open scoped Topology

/-- A finite measurable subset of the good set. Sampling one
extra endpoint keeps all sample times simple multiples of the mesh width. -/
def goodMesh (Q : Triangle) (L ε T : ℝ) : Set DoublePhase :=
  {z | ∀ k : Fin (Nat.ceil (T / ε) + 1),
    (L + 1) * ε < Q.clearance (doubleFlow Q ((k : ℕ) * ε) z).1.1}

lemma goodMesh_measurable (Q : Triangle) (L ε T : ℝ) :
    MeasurableSet (goodMesh Q L ε T) := by
  simp only [goodMesh, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt measurable_const
    (Q.clearance_lipschitz.continuous.measurable.comp
      (measurable_doubleFlow_time Q _).fst.fst)

lemma goodMesh_clearance {Q : Triangle} {L ε T : ℝ} (hε : 0 < ε)
    {z : DoublePhase} (hz : z ∈ goodMesh Q L ε T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    L * ε < Q.clearance (doubleFlow Q t z).1.1 := by
  let k : Fin (Nat.ceil (T / ε) + 1) :=
    ⟨Nat.floor (t / ε), by
      have h := (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hε.le)).trans
        (Nat.floor_le_ceil (T / ε))
      omega⟩
  have hk0 : (k : ℕ) * ε ≤ t := by
    have h := Nat.floor_le (div_nonneg ht.1 hε.le)
    exact (le_div_iff₀ hε).mp h
  have hk1 : t - (k : ℕ) * ε < ε := by
    have h := (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (t / ε))
    dsimp [k]
    nlinarith
  have hd := (Q.clearance_flow_lipschitz z.1).dist_le_mul ((k : ℕ) * ε) t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
  rw [abs_of_nonpos (sub_nonpos.mpr hk0)] at hd
  have hh := hz k
  change (L + 1) * ε < Q.clearance (billiardFlow Q ((k : ℕ) * ε) z.1).1 at hh
  change L * ε < Q.clearance (billiardFlow Q t z.1).1
  have he := le_abs_self (Q.clearance (billiardFlow Q ((k : ℕ) * ε) z.1).1 -
    Q.clearance (billiardFlow Q t z.1).1)
  nlinarith

lemma badMesh_measure_bound (Q : Triangle) (L ε T : ℝ) :
    doubleMeasure Q (goodMesh Q L ε T)ᶜ ≤
      (Nat.ceil (T / ε) + 1 : ℕ) * ((volume Q.table)⁻¹ *
        (3 * (ENNReal.ofReal ((L + 1) * ε)) ^ 2 * (NNReal.pi : ℝ≥0∞))) := by
  classical
  have he : (goodMesh Q L ε T)ᶜ =
      ⋃ k : Fin (Nat.ceil (T / ε) + 1),
        doubleFlow Q ((k : ℕ) * ε) ⁻¹' unsafeSet Q ((L + 1) * ε) := by
    ext z
    simp only [goodMesh, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt,
      mem_iUnion, Set.mem_preimage, unsafeSet]
  rw [he]
  calc
    _ ≤ ∑' k : Fin (Nat.ceil (T / ε) + 1),
        doubleMeasure Q (doubleFlow Q ((k : ℕ) * ε) ⁻¹' unsafeSet Q ((L + 1) * ε)) :=
      measure_iUnion_le _
    _ = ∑' _k : Fin (Nat.ceil (T / ε) + 1),
        doubleMeasure Q (unsafeSet Q ((L + 1) * ε)) := by
      congr 1
      funext k
      exact (measurePreserving_doubleFlow Q _).measure_preimage
        (unsafeSet_measurable Q _).nullMeasurableSet
    _ ≤ ∑' _k : Fin (Nat.ceil (T / ε) + 1),
        ((volume Q.table)⁻¹ * (3 * (ENNReal.ofReal ((L + 1) * ε)) ^ 2 *
          (NNReal.pi : ℝ≥0∞))) :=
      ENNReal.tsum_le_tsum (fun _ => unsafeSet_measure_bound Q _)
    _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

end TriangularBilliards
namespace TriangularBilliards.Analysis.HilbertFlow
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : HilbertFlow H)

lemma negativeAverage_mem_convex {C : Set H} (hc : Convex ℝ C) (hclosed : IsClosed C)
    {T : ℝ} (hT : 0 < T) {u : H} (hu : ∀ t ∈ Set.Icc (-T) 0, W.act t u ∈ C) :
    W.negativeAverage T u ∈ C := by
  have hm : ∀ᵐ t ∂volume.restrict (Set.Ioc (-T) 0), W.act t u ∈ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hu t ⟨ht.1.le,ht.2⟩
  have h := hc.set_average_mem hclosed
    (μ := volume) (t := Set.Ioc (-T) 0)
    (by simpa only [Real.volume_Ioc, sub_neg_eq_add, zero_add, ne_eq, ENNReal.ofReal_eq_zero, not_le] using hT)
    (by simp) hm (W.intervalIntegrable u (-T) 0).1
  rw [MeasureTheory.average_eq, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_neg_eq_add, zero_add, ENNReal.toReal_ofReal hT.le] at h
  change (T⁻¹ : ℝ) • W.timeIntegral (-T) 0 u ∈ C
  rwa [timeIntegral_apply, intervalIntegral.integral_of_le (by linarith : -T ≤ 0)]

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards.Analysis
open MeasureTheory Set Filter
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

/-- Measurable functions with values almost everywhere in prescribed closed
convex fibers form a closed convex subset of the actual L² space. -/
lemma isClosed_ae_mem (C : A → Set ℂ) (hc : ∀ z, IsClosed (C z)) :
    IsClosed {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, u z ∈ C z} := by
  apply IsSeqClosed.isClosed
  intro u v hu hv
  obtain ⟨φ,_,hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hu, hφ] with z hz hlim
  exact (hc z).mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hz (φ n))

lemma convex_ae_mem (C : A → Set ℂ) (hc : ∀ z, Convex ℝ (C z)) :
    Convex ℝ {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, u z ∈ C z} := by
  intro u hu v hv a b ha hb hab
  filter_upwards [hu,hv,Lp.coeFn_smul a u,Lp.coeFn_smul b v,
    Lp.coeFn_add (a • u) (b • v)] with z h1 h2 h3 h4 h5
  simp only [Pi.add_apply, Pi.smul_apply] at h3 h4 h5
  rw [h5,h3,h4]
  exact hc z h1 h2 ha hb hab

lemma isClosed_ae_bounded (H : ℝ) :
    IsClosed {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, ‖u z‖ ≤ H} := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    isClosed_ae_mem (μ := μ) (fun _ => Metric.closedBall (0 : ℂ) H) (fun _ => Metric.isClosed_closedBall)

lemma convex_ae_bounded (H : ℝ) :
    Convex ℝ {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, ‖u z‖ ≤ H} := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    convex_ae_mem (μ := μ) (fun _ => Metric.closedBall (0 : ℂ) H) (fun _ => convex_closedBall _ _)

lemma isClosed_ae_zero_on (E : Set A) :
    IsClosed {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, z ∈ E → u z = 0} := by
  classical
  convert isClosed_ae_mem (μ := μ) (fun z => if z ∈ E then {0} else Set.univ)
    (fun z => by split <;> simp) using 1
  ext u
  simp only [mem_ofPred_eq]
  apply eventually_congr
  filter_upwards with z
  by_cases hz : z ∈ E <;> simp [hz]

lemma convex_ae_zero_on (E : Set A) :
    Convex ℝ {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, z ∈ E → u z = 0} := by
  classical
  convert convex_ae_mem (μ := μ) (fun z => if z ∈ E then {0} else Set.univ)
    (fun z => by split; exact convex_singleton 0; exact convex_univ) using 1
  ext u
  simp only [mem_ofPred_eq]
  apply eventually_congr
  filter_upwards with z
  by_cases hz : z ∈ E <;> simp [hz]

end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis
open MeasureTheory Filter Set
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

lemma restrictL2_ae_bounded {E : Set A} (hE : MeasurableSet E)
    {u : Lp ℂ 2 μ} {H : ℝ} (hH : 0 ≤ H) (hu : ∀ᵐ z ∂μ, ‖u z‖ ≤ H) :
    ∀ᵐ z ∂μ, ‖restrictL2 E hE u z‖ ≤ H := by
  filter_upwards [hu,restrictL2_coe E hE u] with z hz he
  rw [he]
  by_cases h : z ∈ E
  · simpa only [indicator_of_mem h] using hz
  · simpa only [indicator_of_notMem h, norm_zero] using hH

lemma restrictL2_sub_self (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ) :
    restrictL2 E hE u - u = -restrictL2 Eᶜ hE.compl u := by
  apply Lp.ext
  filter_upwards [restrictL2_coe E hE u,restrictL2_coe Eᶜ hE.compl u,
    Lp.coeFn_sub (restrictL2 E hE u) u,Lp.coeFn_neg (restrictL2 Eᶜ hE.compl u)] with z h1 h2 h3 h4
  simp only [Pi.sub_apply,Pi.neg_apply] at h3 h4
  rw [h3,h4,h1,h2]
  by_cases hz : z ∈ E <;> simp [hz]
end TriangularBilliards.Analysis

end
end
end
end
end
end
end
end
end
end

end OAI
