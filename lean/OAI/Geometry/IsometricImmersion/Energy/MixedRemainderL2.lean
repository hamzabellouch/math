import OAI.Geometry.IsometricImmersion.Estimates.MixedRemainderFactors

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def mixedRemainderL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (k : ℕ) : ℝ≥0∞ :=
  firstJetPairL2Budget C H +
    ∑ c : OrderedFinpartition k, chainWordL2Budget C B H V k ⟨c.length, c.partSize⟩

theorem mixedRemainderL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (k : ℕ) : mixedRemainderL2Budget C B H V k < (⊤ : ℝ≥0∞) := by
  unfold mixedRemainderL2Budget
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · unfold firstJetPairL2Budget
    finiteness
  · exact ENNReal.sum_lt_top.mpr (fun c _ =>
      chainWordL2Budget_lt_top C B H hVfinite k ⟨c.length, c.partSize⟩)

theorem mixedFaaRemainder_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (hk : 0 < k) (v : Fin k → Coord) :
    ContinuousOn (mixedFaaRemainder g z hk v) U :=
  (((heightPFirst_contDiffOn hg hU hz hyy 0).continuousOn.mul
      (fullJet_fixed_input_continuousOn (partial_contDiffOn hz hU 0) hU k v)).add
    ((heightPFirst_contDiffOn hg hU hz hyy 1).continuousOn.mul
      (fullJet_fixed_input_continuousOn (partial_contDiffOn hz hU 1) hU k v))).add
    (continuousOn_finsetSum (Finset.univ.erase (fullBlockPartition k hk))
      (fun c _ => mixedFaaTerm_continuousOn hg hU hz hyy v c))

theorem mixed_product_eLpNorm_two
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length (by omega))
    (r : Fin c.length → Fin 6) :
    eLpNorm (fun p => ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p)
      2 (volume.restrict V) ≤ chainProductL2Budget B H V ds.length := by
  classical
  have hB0 : 0 ≤ B := by linarith
  have hprod : AEStronglyMeasurable
      (fun point => ∏ index, mixedFaaFactor z (coordinateDirections ds) c r index point)
      (volume.restrict V) :=
    ((continuousOn_finsetProd Finset.univ
      (fun index _ => mixedFaaFactor_continuousOn hU hz (coordinateDirections ds) c r index)).mono
        hVU).aestronglyMeasurable (μ := volume) hV
  by_cases hh : ∃ j, ds.length ≤ c.partSize j + stateBaseOrder (r j)
  · obtain ⟨j, hj⟩ := hh
    have hlo : ∀ i ∈ (Finset.univ : Finset (Fin c.length)).erase j,
        ∀ p ∈ V, ‖mixedFaaFactor z (coordinateDirections ds) c r i p‖ ≤ B := by
      intro i hi p hp
      have ho : c.partSize i + stateBaseOrder (r i) ≤ ds.length - 1 := by
        by_contra hn
        have he := mixed_high_factor_unique (i := i) (j := j) hds c r (by omega) hj
        exact (Finset.mem_erase.mp hi).1 he
      exact mixedBlock_low_norm_bound hU hz hVU ds hB hlow c i (r i) ho hp
    have hjL := mixedBlock_high_eLpNorm_bound hU hz hV hVU ds (by omega)
      hheight c hc j (r j) hj
    have hcard : ((Finset.univ : Finset (Fin c.length)).erase j).card ≤ ds.length := by
      have he : ((Finset.univ : Finset (Fin c.length)).erase j).card ≤ c.length := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin c.length)))
      exact he.trans c.length_le
    exact (finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (mixedFaaFactor z (coordinateDirections ds) c r) (Finset.mem_univ j) hB0 hV hlo hprod).trans
      (mul_le_mul' (enorm_pow_mono_of_one_le hB hcard)
        (hjL.trans (le_add_of_nonneg_right (by positivity))))
  · have hlo : ∀ i ∈ (Finset.univ : Finset (Fin c.length)),
        ∀ p ∈ V, ‖mixedFaaFactor z (coordinateDirections ds) c r i p‖ ≤ B := by
      intro i _ p hp
      have ho : c.partSize i + stateBaseOrder (r i) ≤ ds.length - 1 := by
        have hn : ¬ ds.length ≤ c.partSize i + stateBaseOrder (r i) := fun h => hh ⟨i, h⟩
        omega
      exact mixedBlock_low_norm_bound hU hz hVU ds hB hlow c i (r i) ho hp
    have hb := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (mixedFaaFactor z (coordinateDirections ds) c r) hB0 hV hlo hprod
    have hb' : eLpNorm (fun p => ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p)
        2 (volume.restrict V) ≤ ‖B ^ c.length‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hb
    exact hb'.trans (mul_le_mul' (enorm_pow_mono_of_one_le hB c.length_le)
      (le_add_of_nonneg_left (by positivity)))

theorem mixedFaaTerm_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length (by omega)) :
    eLpNorm (mixedFaaTerm g z (coordinateDirections ds) c) 2 (volume.restrict V) ≤
      chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩ := by
  classical
  have hcoeff (r : Fin c.length → Fin 6) (p : Coord) (hp : p ∈ V) :
      |coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p| ≤ C :=
    (coordinateChainCoefficient_abs_le_full_derivative g z ⟨c.length, c.partSize⟩ r p).trans
      (hP c.length c.length_le p hp)
  have hm (r : Fin c.length → Fin 6) : AEStronglyMeasurable
      (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p) (volume.restrict V) :=
    (((coordinateChainCoefficient_continuousOn hg hU hz hyy ⟨c.length, c.partSize⟩ r).mul
      (continuousOn_finsetProd Finset.univ
        (fun j _ => mixedFaaFactor_continuousOn hU hz (coordinateDirections ds) c r j))).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hterm (r : Fin c.length → Fin 6) :
      eLpNorm (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p) 2 (volume.restrict V) ≤
        ‖C‖ₑ * chainProductL2Budget B H V ds.length :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (hcoeff r) (hm r)).trans
      (mul_le_mul' le_rfl (mixed_product_eLpNorm_two hU hz hV hVU ds hds hB hlow hheight c hc r))
  have he : mixedFaaTerm g z (coordinateDirections ds) c = fun p =>
      ∑ r : Fin c.length → Fin 6,
        coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
          ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p :=
    funext (mixedFaaTerm_scalar_expansion g z (coordinateDirections ds) c)
  rw [he]
  exact finite_sum_eLpNorm_two Finset.univ _
    (fun _ => ‖C‖ₑ * chainProductL2Budget B H V ds.length)
    (fun r _ => hm r) (fun r _ => hterm r)

theorem mixedFaaRemainder_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) :
    eLpNorm (mixedFaaRemainder g z (by omega) (coordinateDirections ds)) 2 (volume.restrict V) ≤
      mixedRemainderL2Budget C B H V ds.length := by
  classical
  let s := (Finset.univ : Finset (OrderedFinpartition ds.length)).erase (fullBlockPartition ds.length (by omega))
  let f0 : Coord → ℝ := fun p => heightPFirst g z 0 p * iteratedCoordPartial (ds ++ [0]) z p
  let f1 : Coord → ℝ := fun p => heightPFirst g z 1 p * iteratedCoordPartial (ds ++ [1]) z p
  let fs : Coord → ℝ := fun p => ∑ c ∈ s, mixedFaaTerm g z (coordinateDirections ds) c p
  have hfirst (i : Fin 2) (p : Coord) (hp : p ∈ V) : |heightPFirst g z i p| ≤ C :=
    (heightPFirst_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp)) i).trans
      (hP 1 (by omega) p hp)
  have hm0 : AEStronglyMeasurable f0 (volume.restrict V) :=
    (((heightPFirst_contDiffOn hg hU hz hyy 0).continuousOn.mul
      (orderedPartial_contDiffOn hz hU (ds ++ [0])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hm1 : AEStronglyMeasurable f1 (volume.restrict V) :=
    (((heightPFirst_contDiffOn hg hU hz hyy 1).continuousOn.mul
      (orderedPartial_contDiffOn hz hU (ds ++ [1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hb0 : eLpNorm f0 2 (volume.restrict V) ≤ ‖C‖ₑ * (H : ℝ≥0∞) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
      (f := iteratedCoordPartial (ds ++ [0]) z) hV hC (hfirst 0) hm0).trans
      (mul_le_mul' le_rfl (hheight (ds ++ [0]) (by simp)))
  have hb1 : eLpNorm f1 2 (volume.restrict V) ≤ ‖C‖ₑ * (H : ℝ≥0∞) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
      (f := iteratedCoordPartial (ds ++ [1]) z) hV hC (hfirst 1) hm1).trans
      (mul_le_mul' le_rfl (hheight (ds ++ [1]) (by simp)))
  have hbs : eLpNorm fs 2 (volume.restrict V) ≤
      ∑ c : OrderedFinpartition ds.length, chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩ := by
    have hsum := finite_sum_eLpNorm_two s (fun c => mixedFaaTerm g z (coordinateDirections ds) c)
      (fun c => chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩)
      (fun c _ => ((mixedFaaTerm_continuousOn hg hU hz hyy (coordinateDirections ds) c).mono hVU).aestronglyMeasurable (μ := volume) hV)
      (fun c hc => mixedFaaTerm_eLpNorm_two hg hU hz hyy hV hVU ds hds hC hB hP hlow hheight c
        (Finset.mem_erase.mp hc).1)
    exact hsum.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have he : mixedFaaRemainder g z (by omega) (coordinateDirections ds) =ᵐ[volume.restrict V]
      (fun p => f0 p + f1 p + fs p) := by
    filter_upwards [ae_restrict_mem hV] with p hp
    exact mixedFaaRemainder_coordinate_eq hU hz (hVU hp) ds (by omega)
  rw [eLpNorm_congr_ae he]
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add ((eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add hb0 hb1)) hbs)

theorem mixedFaaRemainder_memLp_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) :
    MemLp (mixedFaaRemainder g z (by omega) (coordinateDirections ds)) 2 (volume.restrict V) := by
  exact (mixedFaaRemainder_eLpNorm_two hg hU hz hyy hV hVU ds hds hC hB hP hlow hheight).trans_lt
    (mixedRemainderL2Budget_lt_top C B H hVfinite ds.length)

end SmoothLocal.HighEquation

end

end OAI
