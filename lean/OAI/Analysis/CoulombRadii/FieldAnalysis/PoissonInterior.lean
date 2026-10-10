import Mathlib
import OAI.Analysis.CoulombRadii.Localization.HarmonicInterior
import OAI.Analysis.CoulombRadii.Localization.HarmonicScale

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
theorem poisson_interior_estimates (c : Position) {r A M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball c (3*r)) →
      HasWeakLaplacian F (Metric.ball c (2*r)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0 ≤ σ x) →
      (∀ x ∈ Metric.closedBall c (3*r), σ x ≤ A) →
      (∫ x in Metric.closedBall c (2*r), ‖F x‖) ≤ M →
      (∀ z ∈ Metric.closedBall c r, ‖F z‖ ≤ C) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖F z-F z'‖ ≤ C*‖z-z'‖) := by
  obtain ⟨HC, hHC, hest⟩ := harmonic_interior_estimates_local hr
  let W := Metric.closedBall c (3*r)
  let W' := Metric.closedBall c (2*r)
  let V := (volume W).toReal
  let V' := (volume W').toReal
  let PB := A*(∫ y in Metric.ball (0 : Position) 1, coulombKernel y)+A*V
  let LB := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+A*V
  have hPB : 0 ≤ PB := add_nonneg (mul_nonneg hA (integral_nonneg coulombKernel_nonneg))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  have hLB : 0 ≤ LB := add_nonneg (mul_nonneg hA (integral_nonneg (fun y => sq_nonneg _)))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  let H := M+PB*V'
  have hH : 0 ≤ H := add_nonneg hM (mul_nonneg hPB ENNReal.toReal_nonneg)
  let C := HC*H+PB+LB+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro F σ hF hpoisson hσ hσpos hσbd hIF
  let ρ := W.indicator σ
  have hρ : Integrable ρ := hσ.indicator measurableSet_closedBall
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => Set.indicator_nonneg (fun y _ => hσpos y) x
  have hρbd : ∀ x, ρ x ≤ A := by
    intro x
    by_cases hx : x ∈ W
    · simpa only [ρ, Set.indicator_of_mem hx] using hσbd x hx
    · simpa only [ρ, Set.indicator_of_notMem hx] using hA
  have hmass : (∫ x, ρ x) ≤ A*V := by
    rw [show ρ = W.indicator σ from rfl, integral_indicator measurableSet_closedBall]
    calc
      (∫ x in W, σ x) ≤ ∫ _ in W, A := integral_mono_ae hσ.integrableOn
        (integrableOn_const (isCompact_closedBall c (3*r)).measure_ne_top)
        ((ae_restrict_mem measurableSet_closedBall).mono (fun x hx => hσbd x hx))
      _ = A*V := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, V,
          measureReal_def, mul_comm]
  let P := potentialOf ρ
  have hPcont : Continuous P := potentialOf_continuous hρ hρpos hρbd
  have hPbd (x : Position) : ‖P x‖ ≤ PB := by
    have hp : 0 ≤ P x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρpos y))
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hρpos hρbd x).2.trans (by dsimp only [PB]; linarith)
  have hPlip (x y : Position) : ‖P x-P y‖ ≤ LB*‖x-y‖ :=
    (potentialOf_lipschitz_bound hρ hρpos hρbd x y).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [LB]; linarith) (norm_nonneg _))
  have hW' : W' ⊆ Metric.ball c (3*r) := by
    intro x hx
    change dist x c ≤ 2*r at hx
    change dist x c < 3*r
    linarith
  have hball : Metric.ball c (2*r) ⊆ Metric.ball c (3*r) :=
    Metric.ball_subset_ball (by linarith)
  let h : Position → ℝ := fun x => F x+P x
  have hhcont : ContinuousOn h (Metric.ball c (3*r)) := hF.add hPcont.continuousOn
  have hharm : HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) :=
    local_harmonic_part Metric.isOpen_ball (hF.mono hball) hpoisson hρ hρpos hρbd (by
      intro x hx
      have hxW : x ∈ W := by
        change dist x c ≤ 3*r
        exact (hball hx).le
      exact (Set.indicator_of_mem hxW σ).symm)
  have hiF : IntegrableOn (fun x => ‖F x‖) W' :=
    ((hF.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hih : IntegrableOn (fun x => ‖h x‖) W' :=
    ((hhcont.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hiPB : IntegrableOn (fun _ : Position => PB) W' :=
    integrableOn_const (isCompact_closedBall c (2*r)).measure_ne_top
  have hIh : (∫ x in W', ‖h x‖) ≤ H := by
    calc
      (∫ x in W', ‖h x‖) ≤ ∫ x in W', ‖F x‖+PB := integral_mono_ae hih (hiF.add hiPB)
        (Filter.Eventually.of_forall (fun x => (norm_add_le (F x) (P x)).trans
          (add_le_add le_rfl (hPbd x))))
      _ = (∫ x in W', ‖F x‖)+PB*V' := by
        rw [integral_add hiF hiPB, integral_const]
        simp only [Measure.restrict_apply_univ, smul_eq_mul, V', measureReal_def, mul_comm]
      _ ≤ H := by dsimp only [H]; linarith
  obtain ⟨hval, hdiff⟩ := hest c h hhcont hharm
  have hCval : HC*H+PB ≤ C := by dsimp [C]; linarith
  have hClip : HC*H+LB ≤ C := by dsimp [C]; linarith
  constructor
  · intro z hz
    calc
      ‖F z‖ = ‖h z-P z‖ := by dsimp [h]; rw [add_sub_cancel_right]
      _ ≤ ‖h z‖+‖P z‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)+PB := add_le_add (hval z hz) (hPbd z)
      _ ≤ HC*H+PB := by linarith [mul_le_mul_of_nonneg_left hIh hHC.le]
      _ ≤ C := hCval
  · intro z hz z' hz'
    calc
      ‖F z-F z'‖ = ‖(h z-h z')-(P z-P z')‖ := by congr 1; dsimp [h]; ring
      _ ≤ ‖h z-h z'‖+‖P z-P z'‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)*‖z-z'‖+LB*‖z-z'‖ :=
        add_le_add (hdiff z hz z' hz') (hPlip z z')
      _ ≤ (HC*H+LB)*‖z-z'‖ := by
        have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIh hHC.le)
          (norm_nonneg (z-z'))
        nlinarith
      _ ≤ C*‖z-z'‖ := mul_le_mul_of_nonneg_right hClip (norm_nonneg _)

end NeutralAtom

end
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

lemma HasWeakLaplacian.const_mul {F q : Position → ℝ} {U : Set Position}
    (h : HasWeakLaplacian F U q) (b : ℝ) :
    HasWeakLaplacian (fun x => b*F x) U (fun x => b*q x) := by
  intro φ hφ hφc ht
  simp_rw [mul_assoc, integral_const_mul]
  rw [h φ hφ hφc ht]

theorem poisson_unit_negative_oscillation {A M : ℝ} (hA : 0≤A) (hM : 0≤M) :
    ∃ C : ℝ, 0<C ∧ ∀ (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball 0 3) →
      HasWeakLaplacian F (Metric.ball 0 2) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0≤σ x) →
      (∀ x ∈ Metric.closedBall 0 3, σ x≤A) →
      (∀ x ∈ Metric.closedBall 0 2, F x≤M) →
      volume.real (Metric.closedBall (0:Position) 2)*F 0 ≤
        (∫ x in Metric.closedBall 0 2, F x) →
      ∀ z ∈ Metric.closedBall (0:Position) 1,
        ‖F z-F 0‖ ≤ C*(1+max (-F 0) 0)*‖z‖ := by
  let V := volume.real (Metric.closedBall (0:Position) 2)
  have hV : 0≤V := ENNReal.toReal_nonneg
  obtain ⟨C,hC,H⟩ := poisson_interior_estimates (0:Position)
    (r:=1) (A:=A) (M:=V*(2*M+1)) (by norm_num) hA (by positivity)
  refine ⟨C,hC,?_⟩
  intro F σ hF hLap hσ hp hb hFM hmean z hz
  let T := 1+max (-F 0) 0
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : 1≤T := by dsimp [T]; linarith [le_max_right (-F 0) 0]
  have h2sub : Metric.closedBall (0:Position) 2⊆Metric.ball 0 3 := by
    intro x hx
    change dist x 0≤2 at hx
    change dist x 0<3
    linarith
  have hiF : IntegrableOn F (Metric.closedBall 0 2) :=
    (hF.mono h2sub).integrableOn_compact (isCompact_closedBall _ _)
  have hiabs := hiF.norm
  have hic : IntegrableOn (fun _ : Position => 2*M) (Metric.closedBall 0 2) :=
    integrableOn_const (isCompact_closedBall (0:Position) 2).measure_ne_top
  have hIF : (∫ x in Metric.closedBall 0 2, ‖F x‖) ≤ V*(2*M+max (-F 0) 0) := by
    calc
      (∫ x in Metric.closedBall 0 2, ‖F x‖) ≤
          ∫ x in Metric.closedBall 0 2, 2*M-F x := by
        apply integral_mono_ae hiabs (hic.sub hiF)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        change ‖F x‖ ≤ 2*M-F x
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hFM x hx], by linarith [hFM x hx]⟩
      _ = V*(2*M)-(∫ x in Metric.closedBall 0 2, F x) := by
        rw [integral_sub hic hiF,integral_const]
        simp only [measureReal_restrict_apply_univ,smul_eq_mul,V]
      _ ≤ V*(2*M+max (-F 0) 0) := by
        change V*F 0 ≤ _ at hmean
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-F 0) 0) hV]
  have hIscaled : (∫ x in Metric.closedBall 0 2, ‖T⁻¹*F x‖) ≤ V*(2*M+1) := by
    simp_rw [norm_mul,Real.norm_eq_abs T⁻¹,abs_of_pos (inv_pos.mpr hT),integral_const_mul]
    have hnum : V*(2*M+max (-F 0) 0) ≤ T*(V*(2*M+1)) := by
      dsimp [T]
      nlinarith [mul_nonneg (mul_nonneg hV hM) (le_max_right (-F 0) 0)]
    calc
      _ ≤ T⁻¹*(T*(V*(2*M+1))) :=
        mul_le_mul_of_nonneg_left (hIF.trans hnum) (inv_nonneg.mpr hT.le)
      _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hT.ne',one_mul]
  have hLap' : HasWeakLaplacian (fun x => T⁻¹*F x) (Metric.ball 0 2)
      (fun x => 4*Real.pi*(T⁻¹*σ x)) := by
    convert hLap.const_mul T⁻¹ using 1
    funext point
    ring
  obtain ⟨_,hdiff⟩ := H (fun x => T⁻¹*F x) (fun x => T⁻¹*σ x)
    (by simpa only [mul_one] using hF.const_mul T⁻¹) (by simpa using hLap')
    (hσ.const_mul _) (fun x => mul_nonneg (inv_nonneg.mpr hT.le) (hp x))
    (by
      intro x hx
      have hh : σ x≤A := hb x (by simpa using hx)
      have hinv : T⁻¹≤1 := inv_le_one_of_one_le₀ hT1
      exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hT.le)).trans
        (by simpa using mul_le_mul_of_nonneg_right hinv hA)) (by simpa using hIscaled)
  have hh := hdiff z (by simpa using hz) 0 (by simp)
  simp only [←mul_sub,norm_mul,Real.norm_eq_abs T⁻¹,abs_of_pos (inv_pos.mpr hT),sub_zero] at hh
  have hm := mul_le_mul_of_nonneg_left hh hT.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hT.ne',one_mul,mul_comm T C,T] using hm

end NeutralAtom

end

end OAI
