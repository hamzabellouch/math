import OAI.Geometry.IsometricImmersion.Darboux.QSpatialJets
import OAI.Geometry.IsometricImmersion.Taylor.ScalarChainExpansion

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def heightQCoefficient (g : MetricField) (z : Coord → ℝ) (i : Fin 6) (p : Coord) : ℝ :=
  qFirstCoefficient g i (qSolutionJet z p)

def qDirectLinearization (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  heightQCoefficient g z 2 p * coordPartial 0 u p +
    heightQCoefficient g z 3 p * coordPartial 1 u p +
    heightQCoefficient g z 4 p * coordPartial 0 (coordPartial 1 u) p +
    heightQCoefficient g z 5 p * coordPartial 0 (coordPartial 0 u) p

def qSecondJetCorrection (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (heightQCoefficient g z 4) p * coordPartial 1 u p +
    coordPartial 0 (heightQCoefficient g z 5) p * coordPartial 0 u p

def qFirstJetPairRemainder (g : MetricField) (z : Coord → ℝ) (n : ℕ) (p : Coord) : ℝ :=
  coordPartial 0 (heightQCoefficient g z 2) p * coordPartial 0 (horizontalJet z n) p +
    coordPartial 0 (heightQCoefficient g z 3) p * coordPartial 1 (horizontalJet z n) p

def qCoordinateChainTerm (g : MetricField) (z : Coord → ℝ) (w : ChainWord) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p)
    (fun i => horizontalJet (qSolutionJet z) (w.order i) p)

def qCoordinateChainSum (g : MetricField) (z : Coord → ℝ) (ws : List ChainWord) (p : Coord) : ℝ :=
  (ws.map (fun w => qCoordinateChainTerm g z w p)).sum

def actualQHighRemainder (g : MetricField) (z : Coord → ℝ) (m : ℕ) (p : Coord) : ℝ :=
  qCoordinateChainSum g z (topResidualWords m) p +
    (m + 3 : ℝ) * qFirstJetPairRemainder g z (m + 2) p

theorem heightQCoefficient_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (i : Fin 6) :
    ContDiffOn ℝ ∞ (heightQCoefficient g z i) U :=
  (qFirstCoefficient_contDiffOn hg hU i).comp (qSolutionJet_contDiffOn hU hz)
    (fun p hp => qSolutionJet_mem_domain hp (hxx p hp))

theorem sixVariableQ_direction (g : MetricField) (w v : DarbouxState) :
    fderiv ℝ (sixVariableQ g) w v = ∑ i : Fin 6, qFirstCoefficient g i w * v i := by
  conv_lhs => rw [finite_state_basis_decomposition v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [map_smul, smul_eq_mul, qFirstCoefficient, mul_comm]

theorem sixVariableQ_zero_spatial_direction (g : MetricField) (w v : DarbouxState)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (sixVariableQ g) w v =
      qFirstCoefficient g 2 w * v 2 + qFirstCoefficient g 3 w * v 3 +
        qFirstCoefficient g 4 w * v 4 + qFirstCoefficient g 5 w * v 5 := by
  rw [sixVariableQ_direction]
  simp [Fin.sum_univ_succ, hv0, hv1, add_assoc]

theorem actualQ_top_chain_expansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (hp : coordinatePoint x y ∈ U) (m : ℕ) :
    iteratedDeriv (m + 3) (sixVariableQ g ∘ qSolutionJetCurve z y) x =
      chainTerm (sixVariableQ g) (qSolutionJetCurve z y) (ChainWord.single (m + 3)) x +
      (m + 3 : ℝ) * chainTerm (sixVariableQ g) (qSolutionJetCurve z y)
        (ChainWord.pair 1 (m + 2)) x +
      chainSum (sixVariableQ g) (qSolutionJetCurve z y) (topResidualWords m) x := by
  let I : Set ℝ := {t | coordinatePoint t y ∈ U}
  have hI : IsOpen I := hU.preimage (horizontalPoint_contDiff y).continuous
  have hJ : ContDiffOn ℝ ∞ (qSolutionJetCurve z y) I := by
    intro t ht
    exact (qSolutionJetCurve_contDiffAt hU hz ht).contDiffWithinAt
  have hmap : MapsTo (qSolutionJetCurve z y) I (darbouxQStateDomain g U) := by
    intro t ht
    exact qSolutionJet_mem_domain ht (hxx _ ht)
  exact top_chain_expansion (darbouxQStateDomain_isOpen hg hU) hI
    (sixVariableQ_contDiffOn hg hU) hJ hmap m x hp

theorem actualQ_single_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableQ g) (qSolutionJetCurve z y) (ChainWord.single n) x =
      qDirectLinearization g z (horizontalJet z n) (coordinatePoint x y) := by
  rw [chainTerm_single_eq, qSolutionJetCurve_iteratedDeriv hU hz hp n hn,
    sixVariableQ_zero_spatial_direction _ _ _ (by rfl) (by rfl)]
  rfl

theorem second_fderiv_comp_constant_direction_xi
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial 0 J p, v] =
      coordPartial 0 (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) :=
    fderiv_comp p hdF hJ
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

theorem sixVariableQ_second_zero_spatial_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ r ∈ U, covHessian g z r 0 0 ≠ 0) (hp : p ∈ U)
    (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)
        ![coordPartial 0 (qSolutionJet z) p, v] =
      coordPartial 0 (heightQCoefficient g z 2) p * v 2 +
        coordPartial 0 (heightQCoefficient g z 3) p * v 3 +
        coordPartial 0 (heightQCoefficient g z 4) p * v 4 +
        coordPartial 0 (heightQCoefficient g z 5) p * v 5 := by
  rw [second_fderiv_comp_constant_direction_xi
    (sixVariableQ_contDiffAt_solutionJet hg hU hp (hxx _ hp))
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))]
  have heq : (fun r => fderiv ℝ (sixVariableQ g) (qSolutionJet z r) v) =
      (fun r => heightQCoefficient g z 2 r * v 2 + heightQCoefficient g z 3 r * v 3 +
        heightQCoefficient g z 4 r * v 4 + heightQCoefficient g z 5 r * v 5) :=
    funext (fun r => sixVariableQ_zero_spatial_direction g (qSolutionJet z r) v hv0 hv1)
  have hc (i : Fin 6) := ((heightQCoefficient_contDiffOn hg hU hz hxx i).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hd := ((((hc 2).hasFDerivAt.mul_const (v 2)).add
    ((hc 3).hasFDerivAt.mul_const (v 3))).add
      ((hc 4).hasFDerivAt.mul_const (v 4))).add ((hc 5).hasFDerivAt.mul_const (v 5))
  simp only [Pi.add_def] at hd
  rw [heq]
  unfold coordPartial
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem actualQ_pair_extract_secondJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (hp : coordinatePoint x y ∈ U) (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableQ g) (qSolutionJetCurve z y) (ChainWord.pair 1 n) x =
      qSecondJetCorrection g z (horizontalJet z (n + 1)) (coordinatePoint x y) +
        qFirstJetPairRemainder g z n (coordinatePoint x y) := by
  have hfirst : iteratedDeriv 1 (qSolutionJetCurve z y) x =
      coordPartial 0 (qSolutionJet z) (coordinatePoint x y) :=
    horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) y 1 x hp
  rw [chainTerm_pair_eq, hfirst, qSolutionJetCurve_iteratedDeriv hU hz hp n hn]
  simp only [qSolutionJetCurve]
  rw [
    sixVariableQ_second_zero_spatial_direction hg hU hz hxx hp _ (by rfl) (by rfl)]
  unfold qSecondJetCorrection qFirstJetPairRemainder
  rw [coordPartial_comm (horizontalJet_contDiffOn hU hz n) hU hp 0 1]
  change
    coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x y) *
      coordPartial 0 (horizontalJet z n) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x y) *
      coordPartial 1 (horizontalJet z n) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 4) (coordinatePoint x y) *
      coordPartial 1 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 5) (coordinatePoint x y) *
      coordPartial 0 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) =
    coordPartial 0 (heightQCoefficient g z 4) (coordinatePoint x y) *
      coordPartial 1 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 5) (coordinatePoint x y) *
      coordPartial 0 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) + _
  ring

theorem qChainTerm_eq_coordinateChainTerm
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (w : ChainWord) :
    chainTerm (sixVariableQ g) (qSolutionJetCurve z y) w x =
      qCoordinateChainTerm g z w (coordinatePoint x y) := by
  apply congrArg (iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z (coordinatePoint x y)))
  funext i
  exact horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) y (w.order i) x hp

theorem qChainSum_eq_coordinateChainSum
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (ws : List ChainWord) :
    chainSum (sixVariableQ g) (qSolutionJetCurve z y) ws x =
      qCoordinateChainSum g z ws (coordinatePoint x y) := by
  unfold chainSum qCoordinateChainSum
  congr 1
  apply List.map_congr_left
  intro word _
  exact qChainTerm_eq_coordinateChainTerm hU hz hp word

theorem actual_differentiated_Q
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (hp : coordinatePoint x y ∈ U) (m : ℕ) :
    coordPartial 1 (coordPartial 1 (horizontalJet z (m + 3))) (coordinatePoint x y) =
      qDirectLinearization g z (horizontalJet z (m + 3)) (coordinatePoint x y) +
        (m + 3 : ℝ) * qSecondJetCorrection g z (horizontalJet z (m + 3)) (coordinatePoint x y) +
        actualQHighRemainder g z m (coordinatePoint x y) := by
  have heq : (fun t => coordPartial 1 (coordPartial 1 z) (coordinatePoint t y)) =ᶠ[𝓝 x]
      sixVariableQ g ∘ qSolutionJetCurve z y := by
    filter_upwards [(hU.preimage (horizontalPoint_contDiff y).continuous).mem_nhds hp] with t ht
    exact (darbouxDet_iff_sixVariableQ hg hU hz ht (hxx _ ht)).1 (hD _ ht)
  have htop := actualQ_top_chain_expansion hg hU hz hxx hp m
  rw [← heq.iteratedDeriv_eq (m + 3)] at htop
  rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1)
      y (m + 3) x hp, horizontalJet_two_coordPartials hU hz hp (m + 3) 1 1,
    actualQ_single_linearization hU hz hp (m + 3) (by omega),
    actualQ_pair_extract_secondJet hg hU hz hxx hp (m + 2) (by omega),
    qChainSum_eq_coordinateChainSum hU hz hp] at htop
  unfold actualQHighRemainder
  convert htop using 1
  ring

def qHighBTheta (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  heightQCoefficient g z 3 p + (ell : ℝ) * coordPartial 0 (heightQCoefficient g z 4) p

def qHighBXi (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  heightQCoefficient g z 2 p + (ell : ℝ) * coordPartial 0 (heightQCoefficient g z 5) p

theorem actual_Q_hyperbolic_equation
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (m : ℕ) {p : Coord} (hp : p ∈ U) :
    hyperbolicOperator (heightQCoefficient g z 4) (heightQCoefficient g z 5)
      (horizontalJet z (m + 3)) p =
      qHighBTheta g z (m + 3) p * coordPartial 1 (horizontalJet z (m + 3)) p +
        qHighBXi g z (m + 3) p * coordPartial 0 (horizontalJet z (m + 3)) p +
        actualQHighRemainder g z m p := by
  have he := actual_differentiated_Q hg hU hz hD hxx
    (x := p 0) (y := p 1) (by simpa only [point_eta] using hp) m
  rw [point_eta] at he
  unfold hyperbolicOperator qDirectLinearization qSecondJetCorrection qHighBTheta qHighBXi at *
  rw [he]
  push_cast
  ring

end SmoothLocal.HighEquation

end

end OAI
