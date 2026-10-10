import OAI.Geometry.IsometricImmersion.Darboux.MixedDarbouxElimination
import OAI.Geometry.IsometricImmersion.Metrics.RemainderCoefficientBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem fullJet_fixed_input_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (n : ℕ) (v : Fin n → Coord) :
    ContinuousOn (fun p => iteratedFDeriv ℝ n f p v) U := by
  intro p hp
  have hD := ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).continuousAt
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Coord) E v).continuous.continuousAt
    (x := iteratedFDeriv ℝ n f p)
  exact (hev.comp hD).continuousWithinAt

theorem mixedFaaFactor_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k)
    (r : Fin c.length → Fin 6) (j : Fin c.length) :
    ContinuousOn (mixedFaaFactor z v c r j) U :=
  (ContinuousLinearMap.proj (r j) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (fullJet_fixed_input_continuousOn (solutionJet_contDiffOn hU hz) hU (c.partSize j) (v ∘ c.emb j))

theorem mixedFaaTerm_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) :
    ContinuousOn (mixedFaaTerm g z v c) U := by
  have hm (r : Fin c.length → Fin 6) : ContinuousOn
      (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z v c r j p) U :=
    (coordinateChainCoefficient_continuousOn hg hU hz hyy ⟨c.length, c.partSize⟩ r).mul
      (continuousOn_finsetProd Finset.univ
        (fun index _ => mixedFaaFactor_continuousOn hU hz v c r index))
  exact (continuousOn_finsetSum Finset.univ (fun indices _ => hm indices)).congr
    (fun point _ => mixedFaaTerm_scalar_expansion g z v c point)

theorem fullJet_coordinate_projection_abs_le_one {n : ℕ} (hn : 0 < n)
    (d : Fin n → Fin 2) (i : Fin 2) (p : Coord) :
    |iteratedFDeriv ℝ n (fun q : Coord => q i) p (fun j => Pi.single (d j) (1 : ℝ))| ≤ 1 := by
  by_cases hn1 : n = 1
  · subst n
    change |iteratedFDeriv ℝ 1 (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) p _| ≤ 1
    rw [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.proj_apply, Pi.single_apply]
    split_ifs <;> norm_num
  · change |iteratedFDeriv ℝ n (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) p _| ≤ 1
    rw [fullJet_linear_zero _ (by omega)]
    norm_num

theorem mixedBlock_spatial_abs_le_one
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (c : OrderedFinpartition ds.length) (j : Fin c.length) (i : Fin 2) :
    |(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) (if i = 0 then 0 else 1)| ≤ 1 := by
  rw [mixedFaaFactor_spatial_slot hU hz hp]
  have hd : (coordinateDirections ds ∘ c.emb j) = fun a => Pi.single (ds.get (c.emb j a)) (1 : ℝ) := by
    funext a
    exact coordinateDirections_apply ds (c.emb j a)
  rw [hd]
  exact fullJet_coordinate_projection_abs_le_one (c.partSize_pos j) _ i p

theorem mixed_high_factor_unique {k : ℕ} (hk : 5 ≤ k)
    (c : OrderedFinpartition k) (r : Fin c.length → Fin 6) {i j : Fin c.length}
    (hi : k ≤ c.partSize i + stateBaseOrder (r i))
    (hj : k ≤ c.partSize j + stateBaseOrder (r j)) : i = j := by
  by_contra hij
  have hb := ordered_two_partSizes_le c hij
  have hbi := stateBaseOrder_le_two (r i)
  have hbj := stateBaseOrder_le_two (r j)
  omega

theorem mixedBlock_low_norm_bound
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hVU : V ⊆ U)
    (ds : List (Fin 2)) {B : ℝ} (hB : 1 ≤ B)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (c : OrderedFinpartition ds.length) (j : Fin c.length) (a : Fin 6)
    (horder : c.partSize j + stateBaseOrder a ≤ ds.length - 1)
    {p : Coord} (hp : p ∈ V) :
    ‖(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) a‖ ≤ B := by
  have hh (i : Fin 4) (hi : c.partSize j + heightStateBaseOrder i ≤ ds.length - 1) :
      |(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)| ≤ B := by
    rw [mixed_coordinate_height_factor_eq_word hU hz (hVU hp)]
    exact hlow _ (by simpa [mixedBlockWord, heightStateSuffix_length] using hi) p hp
  fin_cases a
  · simpa [Real.norm_eq_abs] using (mixedBlock_spatial_abs_le_one hU hz (hVU hp) ds c j 0).trans hB
  · simpa [Real.norm_eq_abs] using (mixedBlock_spatial_abs_le_one hU hz (hVU hp) ds c j 1).trans hB
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 0
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 1
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 2
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 3
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)

theorem mixedBlock_high_eLpNorm_bound
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 0 < ds.length) {H : ℝ≥0}
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length hds)
    (j : Fin c.length) (a : Fin 6)
    (hhigh : ds.length ≤ c.partSize j + stateBaseOrder a) :
    eLpNorm (fun p => (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) a) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  have hn := ordered_nonfull_partSize_le hds c hc j
  have hh (i : Fin 4) : eLpNorm (fun p =>
      (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)) 2 (volume.restrict V) ≤
      (H : ℝ≥0∞) := by
    have he : (fun p => (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)) =ᵐ[volume.restrict V]
        iteratedCoordPartial (mixedBlockWord ds c j ++ heightStateSuffix i) z := by
      filter_upwards [ae_restrict_mem hV] with p hp
      exact mixed_coordinate_height_factor_eq_word hU hz (hVU hp) ds c j i
    rw [eLpNorm_congr_ae he]
    exact hheight _ (mixed_nonfull_height_word_length ds hds c hc j i)
  fin_cases a
  · norm_num [stateBaseOrder] at hhigh
    omega
  · norm_num [stateBaseOrder] at hhigh
    omega
  · simpa [heightComponentIndex] using hh 0
  · simpa [heightComponentIndex] using hh 1
  · simpa [heightComponentIndex] using hh 2
  · simpa [heightComponentIndex] using hh 3

theorem heightPFirst_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    |heightPFirst g z i p| ≤ ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single (gradientStateIndex i) (1 : ℝ))
  simpa only [sixVariableP_gradient_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

end SmoothLocal.HighEquation

end

end OAI
