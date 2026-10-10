import OAI.Geometry.IsometricImmersion.Metrics.LocalMetricQFull
import OAI.Geometry.IsometricImmersion.Darboux.QFirstSpatialBounds
import OAI.Geometry.IsometricImmersion.Darboux.QSpatialSlabData
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetReverseNorm

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem coordPartial_qSolutionJet_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) (j : Fin 2) :
    ‖coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z := by
  have hJ : DifferentiableAt ℝ (qSolutionJet z) p :=
    ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt (by simp)
  have he (i : Fin 6) : coordPartial j (qSolutionJet z) p i =
      coordPartial j (fun r => qSolutionJet z r i) p := by
    unfold coordPartial
    rw [fderiv_apply hJ i]
    rfl
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [he, Real.norm_eq_abs]
  fin_cases i
  · change |coordPartial j (fun r : Coord => r 0) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |coordPartial j (fun r : Coord => r 1) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |iteratedCoordPartial [j, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 1] z p| ≤ max 1 Z
    exact (hzB [j, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 1] z p| ≤ max 1 Z
    exact (hzB [j, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

theorem second_fderiv_comp_constant_coordinate
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p)
    (j : Fin 2) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial j J p, v] =
      coordPartial j (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) := by
    exact fderiv_comp p hdF hJ
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

theorem heightQCoefficient_partial_eq_second
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) (i : Fin 6) (j : Fin 2) :
    coordPartial j (heightQCoefficient g z i) p =
      iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)
        ![coordPartial j (qSolutionJet z) p, Pi.single i 1] := by
  exact (second_fderiv_comp_constant_coordinate
    (sixVariableQ_contDiffAt_solutionJet hg hU hp hxx)
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    j (Pi.single i 1)).symm

theorem heightQCoefficient_value_bound {g : MetricField} {z : Coord → ℝ}
    {p : Coord} {C : ℝ}
    (hQ : ‖iteratedFDeriv ℝ 1 (sixVariableQ g) (qSolutionJet z p)‖ ≤ C) (i : Fin 6) :
    |heightQCoefficient g z i p| ≤ C := by
  change ‖fderiv ℝ (sixVariableQ g) (qSolutionJet z p) (Pi.single i 1)‖ ≤ C
  have hb := (fderiv ℝ (sixVariableQ g) (qSolutionJet z p)).le_opNorm (Pi.single i 1)
  simp only [Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (by simpa only [norm_iteratedFDeriv_one] using hQ)

theorem heightQCoefficient_partial_bound_of_second
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord} {Z C : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : S ⊆ U) (hzB : CoordinateBound z S 3 Z) (hC : 0 ≤ C)
    {p : Coord} (hp : p ∈ S) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : ‖iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)‖ ≤ C)
    (i : Fin 6) (j : Fin 2) :
    |coordPartial j (heightQCoefficient g z i) p| ≤ C * max 1 Z := by
  rw [heightQCoefficient_partial_eq_second hg hU hz (hSU hp) hxx i j, ← Real.norm_eq_abs]
  have hd := coordPartial_qSolutionJet_norm_bound hU hz hSU hzB hp j
  have hb := (iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)).le_opNorm
    ![coordPartial j (qSolutionJet z) p, Pi.single i (1 : ℝ)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (mul_le_mul hQ hd (norm_nonneg _) hC)

theorem exists_same_region_Q_low_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, ∀ p ∈ S,
        |heightQCoefficient g z i p| ≤ M ∧
          ∀ j : Fin 2, |coordPartial j (heightQCoefficient g z i) p| ≤ M := by
  obtain ⟨C, hC, hQ⟩ := exists_local_metric_Q_jet_bound G (max R Z) hG hd hc 2
  refine ⟨C * max 1 Z, mul_nonneg hC (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden i p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have hpoint := statePoint_qSolutionJet z p
  have hb (n : ℕ) (hn : n ≤ 2) :
      ‖iteratedFDeriv ℝ n (sixVariableQ g) (qSolutionJet z p)‖ ≤ C :=
    hQ g U hg hU (qSolutionJet z p) (by simpa only [hpoint] using hSU hp)
      (fun a b k hk => by simpa only [hpoint] using hgB a b k (by omega) p hp)
      (qSolutionJet_norm_bound_of_coordinateBound hR hz2 hcoords hp)
      (by simpa only [hpoint] using hdet p hp)
      (by simpa only [stateQDenominator_qSolutionJet] using hden p hp) n hn
  refine ⟨(heightQCoefficient_value_bound (hb 1 (by omega)) i).trans ?_, ?_⟩
  · exact le_mul_of_one_le_right hC (le_max_left _ _)
  · intro j
    exact heightQCoefficient_partial_bound_of_second hg hU hz hSU hzB hC hp hxx (hb 2 le_rfl) i j

theorem exists_same_region_Q_low_bound_of_coordinate
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) S 4 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, ∀ p ∈ S,
        |heightQCoefficient g z i p| ≤ M ∧
          ∀ j : Fin 2, |coordPartial j (heightQCoefficient g z i) p| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_same_region_Q_low_bound (16 * G) R Z (by positivity) hR hd hc
  refine ⟨M, hM, ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden
  apply hbound g z U S hg hU hz hSU hcoords ?_ hzB hdet hden
  intro i j k hk p hp
  have hb := (hgB i j).full_jet_norm_bound (hg.1 i j) hU hSU hG hk hp
  have hpow : (2 : ℝ)^k ≤ 16 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at hh ⊢
    exact hh
  exact hb.trans (mul_le_mul_of_nonneg_right hpow hG)

theorem exists_actual_QLowBounds
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) S 4 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ s0 speed : ℝ,
      (∀ p ∈ S, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ S, |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      QLowBounds g z S s0 M speed := by
  obtain ⟨M, hM, hbound⟩ := exists_same_region_Q_low_bound_of_coordinate G R Z hG hR hd hc
  refine ⟨M, hM, ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden s0 speed hs hspeed p hp
  have hb := hbound g z U S hg hU hz hSU hcoords hgB hzB hdet hden
  exact ⟨hs p hp, (hb 2 p hp).1, (hb 3 p hp).1, (hb 5 p hp).1,
    (hb 4 p hp).2 0, (hb 5 p hp).2 0, (hb 5 p hp).2 1, hspeed p hp⟩

end SmoothLocal.HighEquation

end

end OAI
