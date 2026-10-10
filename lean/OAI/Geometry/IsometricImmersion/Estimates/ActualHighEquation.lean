import OAI.Geometry.IsometricImmersion.Calculus.SecondJetExtraction

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def coordinateChainTerm (g : MetricField) (z : Coord → ℝ) (w : ChainWord) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)
    (fun i => verticalJet (solutionJet z) (w.order i) p)

def coordinateChainSum (g : MetricField) (z : Coord → ℝ) (ws : List ChainWord) (p : Coord) : ℝ :=
  (ws.map (fun w => coordinateChainTerm g z w p)).sum

def actualHighRemainder (g : MetricField) (z : Coord → ℝ) (m : ℕ) (p : Coord) : ℝ :=
  coordinateChainSum g z (topResidualWords m) p +
    (m + 3 : ℝ) * firstJetPairRemainder g z (m + 2) p

theorem chainTerm_eq_coordinateChainTerm
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (w : ChainWord) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) w y =
      coordinateChainTerm g z w ![x, y] := by
  apply congrArg (iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z ![x, y]))
  funext i
  exact verticalJet_slice hU (solutionJet_contDiffOn hU hz) x (w.order i) y hp

theorem chainSum_eq_coordinateChainSum
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (ws : List ChainWord) :
    chainSum (sixVariableP g) (solutionJetCurve z x) ws y =
      coordinateChainSum g z ws ![x, y] := by
  unfold chainSum coordinateChainSum
  congr 1
  apply List.map_congr_left
  intro word _
  exact chainTerm_eq_coordinateChainTerm hU hz hp word

theorem actualP_single_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.single n) y =
      directLinearization g z (verticalJet z n) ![x, y] := by
  rw [chainTerm_single_eq]
  have h := fullBlockPartition_actual_linearization hg hU hz hp hyy n hn
  rw [fullBlockPartition_term] at h
  exact h

theorem actual_differentiated_Darboux
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (m : ℕ) :
    coordPartial 0 (coordPartial 0 (verticalJet z (m + 3))) ![x, y] =
      directLinearization g z (verticalJet z (m + 3)) ![x, y] +
        (m + 3 : ℝ) * secondJetCorrection g z (verticalJet z (m + 3)) ![x, y] +
        actualHighRemainder g z m ![x, y] := by
  have heq : (fun t => coordPartial 0 (coordPartial 0 z) ![x, t]) =ᶠ[𝓝 y]
      sixVariableP g ∘ solutionJetCurve z x := by
    filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hp] with t ht
    change coordPartial 0 (coordPartial 0 z) ![x, t] = sixVariableP g (solutionJet z ![x, t])
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz ht (hyy _ ht) (hD _ ht)
  have htop := actualP_top_chain_expansion hg hU hz hyy hp m
  rw [← heq.iteratedDeriv_eq (m + 3)] at htop
  rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0)
      x (m + 3) y hp,
    verticalJet_two_coordPartials hU hz hp (m + 3) 0 0,
    actualP_single_linearization hg hU hz hp (hyy _ hp) (m + 3) (by omega),
    actualP_pair_extract_secondJet hg hU hz hyy hp (m + 2) (by omega),
    chainSum_eq_coordinateChainSum hU hz hp] at htop
  unfold actualHighRemainder
  convert htop using 1
  ring

theorem actual_differentiated_Darboux_at
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) {p : Coord} (hp : p ∈ U) :
    coordPartial 0 (coordPartial 0 (verticalJet z (m + 3))) p =
      directLinearization g z (verticalJet z (m + 3)) p +
        (m + 3 : ℝ) * secondJetCorrection g z (verticalJet z (m + 3)) p +
        actualHighRemainder g z m p := by
  have he : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  simpa only [he] using actual_differentiated_Darboux hg hU hz hD hyy
    (x := p 0) (y := p 1) (by simpa only [he] using hp) m

end SmoothLocal.HighEquation

end

end OAI
