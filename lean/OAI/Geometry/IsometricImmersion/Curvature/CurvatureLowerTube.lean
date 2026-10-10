import OAI.Geometry.IsometricImmersion.Pulses.PulseCurvaturePrincipal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

abbrev CurvatureFirstInput := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → Fin 2 → ℝ)

def curvatureFirstFunction (a : CurvatureFirstInput) : ℝ := curvatureLowerJet a.1 a.2
def curvatureFirstDomain : Set CurvatureFirstInput := {a | (Matrix.of a.1).det ≠ 0}
def curvatureFirstTube (M d : ℝ) : Set CurvatureFirstInput :=
  Metric.closedBall 0 M ∩ (fun a : CurvatureFirstInput => (Matrix.of a.1).det) ⁻¹' Ici d

def actualCurvatureFirstInput (g : MetricField) (p : Coord) : CurvatureFirstInput :=
  ((fun i j => g p i j),(fun d i j => metricFirstJet g p d i j))

def thetaCurvatureFirstIncrement (f : Coord → ℝ) (p : Coord) : CurvatureFirstInput :=
  ((fun i j => (!![0,0;0,f p] : MetricMatrix) i j),
    (fun d i j => thetaPulseFirstJet f p d i j))

theorem curvatureFirstDet_contDiff :
    ContDiff ℝ ∞ (fun a : CurvatureFirstInput => (Matrix.of a.1).det) := by
  simp only [Matrix.det_fin_two,Matrix.of_apply]
  fun_prop

theorem curvatureFirstDomain_isOpen : IsOpen curvatureFirstDomain :=
  isOpen_ne_fun curvatureFirstDet_contDiff.continuous continuous_const

theorem curvatureFirstFunction_contDiffOn :
    ContDiffOn ℝ ∞ curvatureFirstFunction curvatureFirstDomain :=
  curvatureLowerJet_contDiffOn (fun i j => by fun_prop)
    (fun d i j => by fun_prop) (fun _ h => h)

theorem curvatureFirstTube_isCompact (M d : ℝ) : IsCompact (curvatureFirstTube M d) :=
  (isCompact_closedBall (0 : CurvatureFirstInput) M).inter_right
    (isClosed_Ici.preimage curvatureFirstDet_contDiff.continuous)

theorem curvatureFirstTube_subset_domain (M : ℝ) {d : ℝ} (hd : 0 < d) :
    curvatureFirstTube M d ⊆ curvatureFirstDomain := by
  intro a ha
  exact ne_of_gt (hd.trans_le ha.2)

theorem curvatureFirstTube_fderiv_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ curvatureFirstTube M d,
      ‖fderiv ℝ curvatureFirstFunction a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ curvatureFirstFunction) curvatureFirstDomain :=
    (curvatureFirstFunction_contDiffOn.fderiv_of_isOpen (m := 0)
      curvatureFirstDomain_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (curvatureFirstTube_isCompact M d).exists_bound_of_continuousOn
    (hcont.mono (curvatureFirstTube_subset_domain M hd))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

theorem theta_first_segment_det (a : CurvatureFirstInput) (f : Coord → ℝ) (p : Coord)
    (t : ℝ) :
    (Matrix.of ((1-t) • a + t • (a+thetaCurvatureFirstIncrement f p)).1).det =
      (1-t)*(Matrix.of a.1).det+t*(Matrix.of (a+thetaCurvatureFirstIncrement f p).1).det := by
  simp only [Matrix.det_fin_two,thetaCurvatureFirstIncrement,Prod.fst_add,Prod.smul_fst,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.of_apply]
  ring

theorem theta_first_segment_subset_tube (a : CurvatureFirstInput) (f : Coord → ℝ) (p : Coord)
    {M d : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖a+thetaCurvatureFirstIncrement f p‖ ≤ M)
    (hda : d ≤ (Matrix.of a.1).det)
    (hdb : d ≤ (Matrix.of (a+thetaCurvatureFirstIncrement f p).1).det) :
    segment ℝ a (a+thetaCurvatureFirstIncrement f p) ⊆ curvatureFirstTube M d := by
  intro x hx
  have hball : x ∈ Metric.closedBall (0 : CurvatureFirstInput) M :=
    (convex_closedBall (0 : CurvatureFirstInput) M).segment_subset
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using ha)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb) hx
  refine ⟨hball,?_⟩
  rw [segment_eq_image] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  change d ≤ (Matrix.of ((1-t) • a + t • (a+thetaCurvatureFirstIncrement f p)).1).det
  rw [theta_first_segment_det]
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hda)
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr hdb)
  nlinarith

theorem thetaPulseLowerDifference_eq_firstFunction (g : MetricField) (f : Coord → ℝ) (p : Coord) :
    thetaPulseLowerDifference g f p =
      curvatureFirstFunction (actualCurvatureFirstInput g p+thetaCurvatureFirstIncrement f p)-
        curvatureFirstFunction (actualCurvatureFirstInput g p) := rfl

theorem thetaCurvatureFirstIncrement_norm_le (f : Coord → ℝ) (p : Coord) {e : ℝ}
    (he : 0 ≤ e) (hf : |f p| ≤ e) (hdf : ∀ i, |coordPartial i f p| ≤ e) :
    ‖thetaCurvatureFirstIncrement f p‖ ≤ e := by
  change max ‖(!![0,0;0,f p] : MetricMatrix)‖ ‖thetaPulseFirstJet f p‖ ≤ e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    fin_cases i <;> fin_cases j
    · simpa using he
    · simpa using he
    · simpa using he
    · simpa [Matrix.of_apply,Real.norm_eq_abs] using hf
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    simp only [thetaPulseFirstJet,Real.norm_eq_abs]
    split_ifs
    · exact hdf d
    · simpa using he

theorem exists_uniform_thetaPulseLowerDifference_bound (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (f : Coord → ℝ) (p : Coord),
      ‖actualCurvatureFirstInput g p‖ ≤ B → d ≤ (g p).det →
      ‖thetaCurvatureFirstIncrement f p‖ ≤ 1 → |g p 0 0| * |f p| ≤ d/2 →
      |thetaPulseLowerDifference g f p| ≤ C*‖thetaCurvatureFirstIncrement f p‖ := by
  obtain ⟨C,hC,hbound⟩ := curvatureFirstTube_fderiv_bound (B+1) (half_pos hd)
  refine ⟨C,hC,?_⟩
  intro g f p hg hdet hincr hsmall
  let a := actualCurvatureFirstInput g p
  let b := a+thetaCurvatureFirstIncrement f p
  have ha : ‖a‖ ≤ B+1 := hg.trans (by linarith)
  have hb : ‖b‖ ≤ B+1 := (norm_add_le _ _).trans (add_le_add hg hincr)
  have hda : d/2 ≤ (Matrix.of a.1).det := (by linarith : d/2 ≤ d).trans hdet
  have hdetEq : (Matrix.of b.1).det = (g p).det+g p 0 0*f p := by
    simp only [b,a,actualCurvatureFirstInput,thetaCurvatureFirstIncrement,
      Matrix.det_fin_two,Prod.fst_add,Pi.add_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.of_apply]
    ring
  have hdb : d/2 ≤ (Matrix.of b.1).det := by
    rw [hdetEq]
    have hprod : -(d/2) ≤ g p 0 0*f p := by
      have h := neg_abs_le (g p 0 0*f p)
      rw [abs_mul] at h
      linarith
    linarith
  have htube := theta_first_segment_subset_tube a f p ha hb hda hdb
  have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ curvatureFirstFunction x := by
    intro x hx
    exact (curvatureFirstFunction_contDiffOn.contDiffAt
      (curvatureFirstDomain_isOpen.mem_nhds
        (curvatureFirstTube_subset_domain (B+1) (half_pos hd) (htube hx)))).differentiableAt (by simp)
  have h := (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun x hx => hbound x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [b,a,thetaPulseLowerDifference_eq_firstFunction,Real.norm_eq_abs,
    add_sub_cancel_left] using h

end SmoothLocal.Pulse

end

end OAI
