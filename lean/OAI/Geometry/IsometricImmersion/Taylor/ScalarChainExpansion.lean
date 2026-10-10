import OAI.Geometry.IsometricImmersion.Estimates.ActualHighEquation

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateBaseOrder : Fin 6 → ℕ := ![0, 0, 1, 1, 2, 2]

theorem stateBaseOrder_le_two (i : Fin 6) : stateBaseOrder i ≤ 2 := by
  fin_cases i <;> norm_num [stateBaseOrder]

theorem finite_state_basis_decomposition (v : DarbouxState) :
    v = ∑ i : Fin 6, v i • (Pi.single i (1 : ℝ) : DarbouxState) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]

theorem multilinear_state_components {k : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => DarbouxState) ℝ)
    (v : Fin k → DarbouxState) :
    L v = ∑ r : Fin k → Fin 6,
      L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i) := by
  classical
  calc
    L v = L (fun i => ∑ j : Fin 6, v i j • (Pi.single j (1 : ℝ) : DarbouxState)) := by
      congr 1
      funext i
      exact finite_state_basis_decomposition (v i)
    _ = ∑ r : Fin k → Fin 6, L (fun i => v i (r i) • Pi.single (r i) (1 : ℝ)) :=
      L.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : DarbouxState))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [L.map_smul_univ]
      simp only [smul_eq_mul, mul_comm]

def coordinateChainCoefficient (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)
    (fun i => Pi.single (r i) (1 : ℝ))

def coordinateChainFactor (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (i : Fin w.arity) (p : Coord) : ℝ :=
  verticalJet (solutionJet z) (w.order i) p (r i)

def chainFactorOrder (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) : ℕ :=
  w.order i + stateBaseOrder (r i)

theorem coordinateChainTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    (w : ChainWord) (p : Coord) :
    coordinateChainTerm g z w p =
      ∑ r : Fin w.arity → Fin 6,
        coordinateChainCoefficient g z w r p * ∏ i, coordinateChainFactor z w r i p :=
  multilinear_state_components _ _

theorem solutionJetCurve_iteratedDeriv_positive
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (solutionJetCurve z x) y =
      ![0, if n = 1 then 1 else 0,
        coordPartial 0 (verticalJet z n) ![x, y],
        coordPartial 1 (verticalJet z n) ![x, y],
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y],
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]] := by
  have hc := solutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · change iteratedDeriv n (fun _ : ℝ => x) y = 0
    simp [iteratedDeriv_const, Nat.ne_of_gt hn]
  · change iteratedDeriv n id y = if n = 1 then 1 else 0
    simp [iteratedDeriv_id, Nat.ne_of_gt hn]
  · change iteratedDeriv n (fun t => coordPartial 0 z ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn hz hU 0) x n y hp,
      verticalJet_coordPartial hU hz 0 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn hz hU 1) x n y hp,
      verticalJet_coordPartial hU hz 1 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 1 1]
    rfl

theorem coordinate_solutionJet_vertical_positive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 0 < n) :
    verticalJet (solutionJet z) n p =
      ![0, if n = 1 then 1 else 0,
        coordPartial 0 (verticalJet z n) p,
        coordPartial 1 (verticalJet z n) p,
        coordPartial 0 (coordPartial 1 (verticalJet z n)) p,
        coordPartial 1 (coordPartial 1 (verticalJet z n)) p] := by
  have he : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  have h := solutionJetCurve_iteratedDeriv_positive hU hz
    (x := p 0) (y := p 1) (by simpa only [he] using hp) n hn
  have hv := verticalJet_slice hU (solutionJet_contDiffOn hU hz) (p 0) n (p 1)
    (by simpa only [he] using hp)
  change iteratedDeriv n (solutionJetCurve z (p 0)) (p 1) = _ at hv
  rw [hv] at h
  simpa only [he] using h

theorem ChainWord.arity_le_total {w : ChainWord} (hw : w.Positive) : w.arity ≤ w.total := by
  have hsum : ∑ _i : Fin w.arity, (1 : ℕ) ≤ ∑ i : Fin w.arity, w.order i :=
    Finset.sum_le_sum (fun index _ => hw index)
  simpa [ChainWord.total] using hsum

theorem residual_scalar_factor_orders {m : ℕ} {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    (∀ i, chainFactorOrder w r i ≤ m + 3) ∧ w.arity ≤ m + 3 := by
  obtain ⟨hp, ht, hb⟩ := topResidualWords_properties m w hw
  constructor
  · intro i
    have hi := hb i
    have hr := stateBaseOrder_le_two (r i)
    unfold chainFactorOrder
    omega
  · exact ht ▸ ChainWord.arity_le_total hp

theorem residual_scalar_high_unique {m : ℕ} (hm : 8 ≤ m + 3) {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) {i j : Fin w.arity}
    (hi : m + 2 ≤ chainFactorOrder w r i) (hj : m + 2 ≤ chainFactorOrder w r j) : i = j :=
  topResidual_high_unique hm hw (fun k => stateBaseOrder (r k))
    (fun k => stateBaseOrder_le_two (r k)) hi hj

end SmoothLocal.HighEquation

end

end OAI
