import OAI.Geometry.IsometricImmersion.Calculus.MixedCoordinateCalculus
import OAI.Geometry.IsometricImmersion.Estimates.ActualRemainderFactors

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def mixedFaaTerm (g : MetricField) (z : Coord → ℝ) {k : ℕ} (v : Fin k → Coord)
    (c : OrderedFinpartition k) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJet z p)
    (fun j => iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j))

def mixedFaaFactor (z : Coord → ℝ) {k : ℕ} (v : Fin k → Coord)
    (c : OrderedFinpartition k) (r : Fin c.length → Fin 6) (j : Fin c.length) (p : Coord) : ℝ :=
  (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j)) (r j)

def mixedFaaRemainder (g : MetricField) (z : Coord → ℝ) {k : ℕ} (hk : 0 < k)
    (v : Fin k → Coord) (p : Coord) : ℝ :=
  heightPFirst g z 0 p * iteratedFDeriv ℝ k (coordPartial 0 z) p v +
  heightPFirst g z 1 p * iteratedFDeriv ℝ k (coordPartial 1 z) p v +
  ∑ c ∈ (Finset.univ.erase (fullBlockPartition k hk)), mixedFaaTerm g z v c p

def mixedBlockWord (ds : List (Fin 2)) (c : OrderedFinpartition ds.length)
    (j : Fin c.length) : List (Fin 2) := List.ofFn (fun i => ds.get (c.emb j i))

def heightStateSuffix : Fin 4 → List (Fin 2) := ![[0], [1], [0, 1], [1, 1]]

theorem heightStateSuffix_length (i : Fin 4) :
    (heightStateSuffix i).length = heightStateBaseOrder i := by
  fin_cases i <;> rfl

theorem heightStateFactor_zero_eq_suffix (z : Coord → ℝ) (i : Fin 4) :
    heightStateFactor z 0 i = iteratedCoordPartial (heightStateSuffix i) z := by
  fin_cases i <;> rfl

theorem mixedFaaTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (p : Coord) :
    mixedFaaTerm g z v c p =
      ∑ r : Fin c.length → Fin 6,
        coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
          ∏ j, mixedFaaFactor z v c r j p :=
  multilinear_state_components _ _

theorem mixedFaaFactor_height_slot
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (j : Fin c.length)
    (i : Fin 4) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j)) (heightComponentIndex i) =
      iteratedFDeriv ℝ (c.partSize j) (heightStateFactor z 0 i) p (v ∘ c.emb j) := by
  rw [state_fullJet_eval ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))]
  fin_cases i <;> rfl

theorem mixed_coordinate_height_factor_eq_word
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (c : OrderedFinpartition ds.length) (j : Fin c.length)
    (i : Fin 4) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i) =
      iteratedCoordPartial (mixedBlockWord ds c j ++ heightStateSuffix i) z p := by
  rw [mixedFaaFactor_height_slot hU hz hp]
  have hdir : (coordinateDirections ds ∘ c.emb j) =
      fun a => Pi.single (ds.get (c.emb j a)) (1 : ℝ) := by
    funext a
    exact coordinateDirections_apply ds (c.emb j a)
  rw [hdir, fullJet_coordinate_inputs_eq_ordered (heightStateFactor_contDiffOn hU hz 0 i) hU
    (c.partSize j) (fun a => ds.get (c.emb j a)) hp,
    heightStateFactor_zero_eq_suffix]
  exact (congrFun (orderedPartial_append (mixedBlockWord ds c j) (heightStateSuffix i) z) p).symm

theorem mixedFaaFactor_spatial_slot
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (j : Fin c.length)
    (i : Fin 2) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j))
        (if i = 0 then 0 else 1) =
      iteratedFDeriv ℝ (c.partSize j) (fun q : Coord => q i) p (v ∘ c.emb j) := by
  rw [state_fullJet_eval ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))]
  fin_cases i <;> rfl

theorem mixed_nonfull_factor_order {k : ℕ} (hk : 0 < k)
    (c : OrderedFinpartition k) (hc : c ≠ fullBlockPartition k hk)
    (r : Fin c.length → Fin 6) (j : Fin c.length) :
    c.partSize j + stateBaseOrder (r j) ≤ k + 1 := by
  have hsize := ordered_nonfull_partSize_le hk c hc j
  have hbase := stateBaseOrder_le_two (r j)
  omega

theorem mixed_nonfull_height_word_length (ds : List (Fin 2)) (hds : 0 < ds.length)
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length hds)
    (j : Fin c.length) (i : Fin 4) :
    (mixedBlockWord ds c j ++ heightStateSuffix i).length ≤ ds.length + 1 := by
  have hsize := ordered_nonfull_partSize_le hds c hc j
  have hbase : heightStateBaseOrder i ≤ 2 := by fin_cases i <;> norm_num [heightStateBaseOrder]
  simp only [List.length_append, mixedBlockWord, List.length_ofFn, heightStateSuffix_length]
  omega

theorem mixedFaaRemainder_coordinate_eq
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 0 < ds.length) :
    mixedFaaRemainder g z hds (coordinateDirections ds) p =
      heightPFirst g z 0 p * iteratedCoordPartial (ds ++ [0]) z p +
      heightPFirst g z 1 p * iteratedCoordPartial (ds ++ [1]) z p +
      ∑ c ∈ (Finset.univ.erase (fullBlockPartition ds.length hds)),
        mixedFaaTerm g z (coordinateDirections ds) c p := by
  unfold mixedFaaRemainder
  rw [← iteratedCoordPartial_eq_jet (partial_contDiffOn hz hU 0) hU ds hp,
    ← iteratedCoordPartial_eq_jet (partial_contDiffOn hz hU 1) hU ds hp,
    orderedPartial_append ds [0], orderedPartial_append ds [1]]
  rfl

theorem actualP_mixed_faaExpansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (k : ℕ) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (sixVariableP g ∘ solutionJet z) p v =
      ∑ c : OrderedFinpartition k, mixedFaaTerm g z v c p := by
  have h := congrArg (fun L => L v) (iteratedFDeriv_comp
    (sixVariableP_contDiffAt_solutionJet hg hU hp hyy)
    ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))
    (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)))
  simpa [FormalMultilinearSeries.taylorComp, ftaylorSeries,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, mixedFaaTerm] using h

theorem mixed_fullBlock_term (g : MetricField) (z : Coord → ℝ) {k : ℕ}
    (hk : 0 < k) (v : Fin k → Coord) (p : Coord) :
    mixedFaaTerm g z v (fullBlockPartition k hk) p =
      fderiv ℝ (sixVariableP g) (solutionJet z p)
        (iteratedFDeriv ℝ k (solutionJet z) p v) := by
  change iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)
    (fun _ : Fin 1 => iteratedFDeriv ℝ k (solutionJet z) p (v ∘ id)) = _
  rw [iteratedFDeriv_one_apply]
  rfl

theorem mixed_fullBlock_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (v : Fin k → Coord) :
    mixedFaaTerm g z v (fullBlockPartition k (by omega)) p =
      heightPFirst g z 0 p * iteratedFDeriv ℝ k (coordPartial 0 z) p v +
      heightPFirst g z 1 p * iteratedFDeriv ℝ k (coordPartial 1 z) p v +
      2 * hessianQuotient g z p *
        iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 1 z)) p v -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedFDeriv ℝ k (coordPartial 1 (coordPartial 1 z)) p v := by
  rw [mixed_fullBlock_term, solutionJet_fullJet_ge_two hU hz hp k hk v]
  rw [sixVariableP_vertical_direction hg hU hp hyy _ (by rfl) (by rfl)]
  rfl

theorem actualDarboux_mixed_principal
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    {k : ℕ} (hk : 2 ≤ k) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 0 z)) p v =
      2 * hessianQuotient g z p *
        iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 1 z)) p v -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedFDeriv ℝ k (coordPartial 1 (coordPartial 1 z)) p v +
      mixedFaaRemainder g z (by omega) v p := by
  classical
  have heq : coordPartial 0 (coordPartial 0 z) =ᶠ[𝓝 p] sixVariableP g ∘ solutionJet z := by
    filter_upwards [hU.mem_nhds hp] with q hq
    change coordPartial 0 (coordPartial 0 z) q = sixVariableP g (solutionJet z q)
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz hq (hyy q hq) (hD q hq)
  have hder := congrArg (fun L => L v) ((heq.iteratedFDeriv ℝ k).self_of_nhds)
  have hfaa := actualP_mixed_faaExpansion hg hU hz hp (hyy p hp) k v
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset (OrderedFinpartition k))
    (fun c => mixedFaaTerm g z v c p) (Finset.mem_univ (fullBlockPartition k (by omega)))).symm
  rw [mixed_fullBlock_linearization hg hU hz hp (hyy p hp) hk v] at hsplit
  have hfull := hder.trans (hfaa.trans hsplit)
  calc
    _ = _ := hfull
    _ = _ := by unfold mixedFaaRemainder; ring

theorem actualDarboux_ordered_mixed_elimination
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 2 ≤ ds.length) :
    iteratedCoordPartial (ds ++ [0, 0]) z p =
      2 * hessianQuotient g z p * iteratedCoordPartial (ds ++ [0, 1]) z p -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedCoordPartial (ds ++ [1, 1]) z p +
      mixedFaaRemainder g z (by omega) (coordinateDirections ds) p := by
  have h := actualDarboux_mixed_principal hg hU hz hD hyy hp hds (coordinateDirections ds)
  have hxx := partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0
  have hxy := partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  have hyyS := partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1
  rw [← iteratedCoordPartial_eq_jet hxx hU ds hp,
    ← iteratedCoordPartial_eq_jet hxy hU ds hp,
    ← iteratedCoordPartial_eq_jet hyyS hU ds hp] at h
  rw [orderedPartial_append ds [0, 0], orderedPartial_append ds [0, 1],
    orderedPartial_append ds [1, 1]]
  exact h

theorem actualDarboux_arbitrary_word_elimination
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 4 ≤ ds.length) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), ∃ hes : 2 ≤ es.length,
      ds.Perm (es ++ [0, 0]) ∧ es.length + 2 = ds.length ∧
      (es ++ [0, 1]).count 0 < ds.count 0 ∧
      (es ++ [1, 1]).count 0 < ds.count 0 ∧
      iteratedCoordPartial ds z p =
        2 * hessianQuotient g z p * iteratedCoordPartial (es ++ [0, 1]) z p -
        ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
          iteratedCoordPartial (es ++ [1, 1]) z p +
        mixedFaaRemainder g z (by omega) (coordinateDirections es) p := by
  obtain ⟨es, hperm⟩ := word_two_x_permutation ds hx
  have hlen : es.length + 2 = ds.length := by simpa using hperm.length_eq.symm
  have hes : 2 ≤ es.length := by omega
  have hc := hperm.count_eq (0 : Fin 2)
  obtain ⟨_, _, hxycount, hyycount⟩ := mixed_principal_word_orders es
  refine ⟨es, hes, hperm, hlen, ?_, ?_, ?_⟩
  · simpa only [hc] using hxycount
  · simpa only [hc] using hyycount
  · exact (orderedPartial_perm hz hU hperm p hp).trans
      (actualDarboux_ordered_mixed_elimination hg hU hz hD hyy hp es hes)

end SmoothLocal.HighEquation

end

end OAI
