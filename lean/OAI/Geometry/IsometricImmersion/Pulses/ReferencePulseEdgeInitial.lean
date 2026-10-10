import OAI.Geometry.IsometricImmersion.Calculus.BoundedClassInitialJet
import OAI.Geometry.IsometricImmersion.Pulses.PulseEdgeReferenceDistance

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Perturbation
open SmoothLocal.Flow SmoothLocal.Taylor

theorem exists_bounded_patch_reference_initial_floor
    (G kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ tau0 : ℕ, 1 ≤ tau0 ∧
      ∀ (g0 gStar : MetricField) (V : Set Coord) (eta : metricPatchSet g0 kappa)
        (z : Coord → ℝ) (r : ℝ) (N : ℕ) (delta : ℝ) (tau : ℕ),
      SmoothPositiveOn gStar V → IsOpen V → SmoothLocal.Flow.modelSquare ⊆ V →
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
      0 < r → boundedClassWidth kappa M * r ≤ 1 / 20 →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ SmoothLocal.Flow.modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ SmoothLocal.Flow.modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0 - q0| ≤
        1 / (100 * boundedClassWidth kappa M) →
      0 < delta → tau0 ≤ tau → delta / (tau : ℝ) ≤ r →
      (∀ i j k, k ≤ tau → ∀ p ∈ SmoothLocal.Flow.modelSquare,
        ‖iteratedFDeriv ℝ k
          (fun a => perturbedMetric g0 eta.val a i j -
            testMetric gStar q0 (boundedClassWidth kappa M * r / 16) N delta (tau : ℝ) a i j) p‖ ≤
              metricApproximationAccuracy tau) →
      ∀ x ∈ Ioo (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r),
      (boundedClassSpeed kappa M)^2 / (4 * (M : ℝ)) ≤
        |covHessian (metricInShearCoordinates gStar q0)
          (linearCauchy (-delta / (tau : ℝ))
            (heightCauchyValue (heightInShearCoordinates z q0) (-delta / (tau : ℝ)))
            (heightCauchyVelocity (heightInShearCoordinates z q0) (-delta / (tau : ℝ))))
          ![x, -delta / (tau : ℝ)] 0 0| := by
  let c := (boundedClassSpeed kappa M)^2 / (2 * (M : ℝ))
  have hc : 0 < c := boundedClassShearHxxFloor_pos hkappa hM
  obtain ⟨epsilon, he, htol⟩ := exists_reference_linearCauchy_XX_tolerance
    (8 * G) (boundedClassShearedStateBudget q0 M) hd hc
  obtain ⟨tau0, htau0, herror⟩ := exists_first_error_threshold he
  refine ⟨tau0, htau0, ?_⟩
  intro g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelta htau hwidth happrox x hx
  let g := perturbedMetric g0 eta.val
  let L := boundedClassWidth kappa M
  let a := -delta / (tau : ℝ)
  have hclass0 := hclass
  obtain ⟨_, hadm, _, _, _⟩ := hclass
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
  have hrsmall' : r ≤ 1 / 20 := by
    have hh : r ≤ L * r := by nlinarith
    exact hh.trans hLr
  have htauN : 1 ≤ tau := htau0.trans htau
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htauN)
  have habs : |a| ≤ r := by
    dsimp [a]
    rw [abs_div, abs_neg, abs_of_pos hdelta, abs_of_pos htauR]
    exact hwidth
  have hcutCentral (y : ℝ) (hy : y ∈ Ioo (-(L * r)) (L * r)) :
      inverseShearCoordinates q0 ![y, a] ∈ centralBox :=
    inverseShear_slab_mem_centralBox hL1 hr.le hLr hq0 (abs_le.mpr ⟨hy.1.le, hy.2.le⟩) habs
  have hcutS (y : ℝ) (hy : y ∈ Ioo (-(L * r)) (L * r)) :
      inverseShearCoordinates q0 ![y, a] ∈ SmoothLocal.Flow.modelSquare :=
    centralBox_subset_modelSquare (hcutCentral y hy)
  have hpS := hcutS x hx
  have hpU := hSU hpS
  have hpx : |x| ≤ L * r := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have hsmall := bounded_class_slab_quotient_small_of_cap_radius hclass0 hG hd hr.le hq0 hrsmall
    hgB hdet hcenter hpS hpx habs
  have hK : gaussianCurvature g (inverseShearCoordinates q0 ![x, a]) ≤ -kappa / 2 :=
    (eta.property.2 _ (hcutCentral x hx)).le
  obtain ⟨_, hxx, _, _⟩ := bounded_class_shear_estimates hclass0 hkappa hpS hK hsmall
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  have hfirst := sheared_first_input_norm_le_of_original_jets hg hU hpU hG hq1
    (fun i j k hk => hgB i j k (by omega) _ hpS)
  have hstate := bounded_class_sheared_solution_state_bound hclass0 q0 hpS
    (show |(![x,a] : Coord) 0| ≤ 1 ∧ |(![x,a] : Coord) 1| ≤ 1 from
      ⟨by change |x| ≤ 1; exact hpx.trans (hLr.trans (by norm_num)),
        by change |a| ≤ 1; exact habs.trans (hrsmall'.trans (by norm_num))⟩)
  have hdet0 : d ≤ (g (inverseShearCoordinates q0 ![x,a])).det := by
    have hh := hdet _ hpS
    rw [abs_of_pos (hg.2 _ hpU).det_pos] at hh
    exact hh
  have hdetS : d ≤ (metricInShearCoordinates g q0 ![x,a]).det := by
    rw [metricDet_in_shear_coordinates]
    exact hdet0
  have hdist := actual_pulse_edge_reference_first_distance hg hgStar hU hV hq1
    (div_pos (mul_pos hL hr) (by norm_num)) hdelta htauN hpU (hSV hpS)
    (fun i j k hk => happrox i j k hk _ hpS)
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hresult := htol (metricInShearCoordinates g q0) (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' U) hzS hUS
    (-(L * r)) (L * r) a (fun y hy => hSU (hcutS y hy)) x hx hfirst hstate hdetS hxx
    (hdist.trans (herror tau htau))
  have heq : c / 2 = (boundedClassSpeed kappa M)^2 / (4 * (M : ℝ)) := by
    dsimp [c]
    ring
  rw [heq] at hresult
  exact hresult

end SmoothLocal.Pulse

end

end OAI
