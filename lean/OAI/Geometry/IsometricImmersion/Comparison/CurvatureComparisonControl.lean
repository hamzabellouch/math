import OAI.Geometry.IsometricImmersion.Pulses.PulseDensitySlab

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem matrix_entry_abs_le_norm (G : MetricMatrix) (i j : Fin 2) : |G i j| ≤ ‖G‖ := by
  simpa only [Real.norm_eq_abs] using
    (Matrix.norm_entry_le_entrywise_sup_norm G (i := i) (j := j))

theorem det_sub_le_first_distance (G H : MetricMatrix) {B e : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (hG : ‖G‖ ≤ B) (hD : ‖H-G‖ ≤ e) :
    |H.det-G.det| ≤ 4*B*e+2*e^2 := by
  let D := H-G
  have hg (i j : Fin 2) : |G i j| ≤ B := (matrix_entry_abs_le_norm G i j).trans hG
  have hd (i j : Fin 2) : |D i j| ≤ e := (matrix_entry_abs_le_norm D i j).trans hD
  have hgd (i j k l : Fin 2) : |G i j*D k l| ≤ B*e := by
    rw [abs_mul]
    exact mul_le_mul (hg i j) (hd k l) (abs_nonneg _) hB
  have hdg (i j k l : Fin 2) : |D i j*G k l| ≤ e*B := by
    rw [abs_mul]
    exact mul_le_mul (hd i j) (hg k l) (abs_nonneg _) he
  have hdd (i j k l : Fin 2) : |D i j*D k l| ≤ e^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hd i j) (hd k l) (abs_nonneg _) he
  have hsum (i j k l : Fin 2) :
      |G i j*D k l+D i j*G k l+D i j*D k l| ≤ B*e+e*B+e^2 :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add (hgd i j k l) (hdg i j k l)) (hdd i j k l))
  have hEq : H.det-G.det =
      (G 0 0*D 1 1+D 0 0*G 1 1+D 0 0*D 1 1)-
        (G 0 1*D 1 0+D 0 1*G 1 0+D 0 1*D 1 0) := by
    simp only [D,Matrix.det_fin_two,Matrix.sub_apply]
    ring
  rw [hEq]
  calc
    _ ≤ |G 0 0*D 1 1+D 0 0*G 1 1+D 0 0*D 1 1|+
        |G 0 1*D 1 0+D 0 1*G 1 0+D 0 1*D 1 0| := abs_sub _ _
    _ ≤ (B*e+e*B+e^2)+(B*e+e*B+e^2) := add_le_add (hsum 0 0 1 1) (hsum 0 1 1 0)
    _ = _ := by ring

theorem det_sub_le_small_first_distance (G H : MetricMatrix) {B e : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1) (hG : ‖G‖ ≤ B) (hD : ‖H-G‖ ≤ e) :
    |H.det-G.det| ≤ (4*B+2)*e := by
  apply (det_sub_le_first_distance G H hB he hG hD).trans
  have hee : e^2 ≤ e := by nlinarith [mul_le_mul_of_nonneg_left he1 he]
  nlinarith

theorem first_jet_close_segment_subset_tube (a b : CurvatureFirstInput) {B d : ℝ}
    (ha : ‖a‖ ≤ B) (hdet : d ≤ (Matrix.of a.1).det) (hdist : ‖b-a‖ ≤ 1)
    (hsmall : (4*max B 0+2)*‖b-a‖ ≤ d/2) :
    segment ℝ a b ⊆ curvatureFirstTube (max B 0+1) (d/2) := by
  intro x hx
  have hxa : ‖x-a‖ ≤ ‖b-a‖ := by
    have hball : x ∈ Metric.closedBall a ‖b-a‖ :=
      (convex_closedBall a ‖b-a‖).segment_subset
        (by simp) (Metric.mem_closedBall.mpr (dist_eq_norm b a).le) hx
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hball
  have hxnorm : ‖x‖ ≤ max B 0+1 := by
    calc
      _ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-a‖+‖a‖ := norm_add_le _ _
      _ ≤ 1+max B 0 := add_le_add (hxa.trans hdist) (ha.trans (le_max_left _ _))
      _ = _ := by ring
  have hmatrixD : ‖x.1-a.1‖ ≤ ‖b-a‖ :=
    (show ‖x.1-a.1‖ ≤ ‖x-a‖ from norm_fst_le (x-a)).trans hxa
  have hmatrixA : ‖a.1‖ ≤ max B 0 := (norm_fst_le a).trans (ha.trans (le_max_left _ _))
  have hdetdiff := det_sub_le_small_first_distance (Matrix.of a.1) (Matrix.of x.1) (le_max_right B 0)
    (norm_nonneg _) hdist hmatrixA hmatrixD
  have hxdet : d/2 ≤ (Matrix.of x.1).det := by
    have hneg := neg_abs_le ((Matrix.of x.1).det-(Matrix.of a.1).det)
    linarith [hdetdiff.trans hsmall]
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm,hxdet⟩

theorem exists_uniform_curvature_first_comparison (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : CurvatureFirstInput,
      ‖a‖ ≤ B → d ≤ (Matrix.of a.1).det → ‖b-a‖ ≤ 1 →
      (4*max B 0+2)*‖b-a‖ ≤ d/2 →
      |curvatureFirstFunction b-curvatureFirstFunction a| ≤ C*‖b-a‖ := by
  obtain ⟨C,hC,hbound⟩ := curvatureFirstTube_fderiv_bound (max B 0+1) (half_pos hd)
  refine ⟨C,hC,?_⟩
  intro a b ha hdet hdist hsmall
  have htube := first_jet_close_segment_subset_tube a b ha hdet hdist hsmall
  have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ curvatureFirstFunction x := by
    intro x hx
    exact (curvatureFirstFunction_contDiffOn.contDiffAt (curvatureFirstDomain_isOpen.mem_nhds
      (curvatureFirstTube_subset_domain (max B 0+1) (half_pos hd) (htube hx)))).differentiableAt (by simp)
  simpa only [Real.norm_eq_abs] using
    (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
      (fun x hx => hbound x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

theorem exists_uniform_curvature_density_comparison (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g h : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn h U → IsOpen U →
      ∀ p ∈ U, ∀ e : ℝ,
        ‖actualCurvatureFirstInput h p‖ ≤ B → d ≤ (h p).det →
        ‖actualCurvatureFirstInput g p-actualCurvatureFirstInput h p‖ ≤ e →
        e ≤ 1 → (4*max B 0+2)*e ≤ d/2 →
        (∀ i j k l : Fin 2,
          |coordPartial i (coordPartial j (fun q => g q k l)) p-
            coordPartial i (coordPartial j (fun q => h q k l)) p| ≤ e) →
        |curvatureDensity g p-curvatureDensity h p| ≤ C*e := by
  obtain ⟨C0,hC0,hbound⟩ := exists_uniform_curvature_first_comparison B hd
  refine ⟨2+C0,by linarith,?_⟩
  intro g h U hg hh hU p hp e hjet hdet hdist he1 hsmall hsecond
  have hscale : 0 ≤ 4*max B 0+2 := by linarith [le_max_right B 0]
  have hfirst := hbound (actualCurvatureFirstInput h p) (actualCurvatureFirstInput g p)
    hjet hdet (hdist.trans he1) ((mul_le_mul_of_nonneg_left hdist hscale).trans hsmall)
  have hL : |curvatureLowerTerm g p-curvatureLowerTerm h p| ≤ C0*e :=
    hfirst.trans (mul_le_mul_of_nonneg_left hdist hC0)
  rw [←curvatureDensityJetError_eq hg hh hU hp]
  exact ((curvatureDensityJetError_le g h p (hsecond 0 1 0 1) (hsecond 0 0 1 1)
    (hsecond 1 1 0 0)).trans (add_le_add le_rfl hL)).trans_eq (by ring)

end SmoothLocal.Pulse

end

end OAI
