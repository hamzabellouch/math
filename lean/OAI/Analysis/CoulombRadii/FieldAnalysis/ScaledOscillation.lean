import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior
import OAI.Analysis.CoulombRadii.FieldAnalysis.NewtonSubmean

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

lemma affine_ball_distance (y z : Position) {a : ℝ} (ha : 0<a) :
    dist (y+a • z) y = a*‖z‖ := by
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem poisson_scaled_negative_oscillation {A M : ℝ} (hA : 0≤A) (hM : 0≤M) :
    ∃ C : ℝ, 0<C ∧ ∀ (F σ : Position → ℝ) (y : Position) (a : ℝ), 0<a →
      ContinuousOn F (Metric.ball y (3*a)) →
      HasWeakLaplacian F (Metric.ball y (2*a)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0≤σ x) →
      (∀ x ∈ Metric.closedBall y (3*a), σ x≤A/a^6) →
      (∀ x ∈ Metric.closedBall y (2*a), F x≤M/a^4) →
      F y ≤ (∫ x, F x*Coulomb.ballCloud y (2*a) 1 x) →
      ∀ z ∈ Metric.closedBall y a,
        ‖F z-F y‖ ≤ C*(‖z-y‖/a)*((a^4)⁻¹+max (-F y) 0) := by
  obtain ⟨C,hC,H⟩ := poisson_unit_negative_oscillation hA hM
  refine ⟨C,hC,?_⟩
  intro F σ y a ha hF hLap hi hp hb hcap hmean z hz
  let G := fun x => a^4*F (y+a • x)
  let τ := fun x => a^6*σ (y+a • x)
  have hmap {R : ℝ} {x : Position} (hx : x∈Metric.ball 0 R) :
      y+a • x∈Metric.ball y (R*a) := by
    rw [Metric.mem_ball,affine_ball_distance y x ha]
    have h := mul_lt_mul_of_pos_left (show ‖x‖<R by simpa using hx) ha
    simpa only [mul_comm a R] using h
  have hmapc {R : ℝ} {x : Position} (hx : x∈Metric.closedBall 0 R) :
      y+a • x∈Metric.closedBall y (R*a) := by
    rw [Metric.mem_closedBall,affine_ball_distance y x ha]
    have h := mul_le_mul_of_nonneg_left (show ‖x‖≤R by simpa using hx) ha.le
    simpa only [mul_comm a R] using h
  have hAff : Continuous (fun x : Position => y+a • x) :=
    continuous_const.add (continuous_id.const_smul a)
  have hm3 : MapsTo (fun x : Position => y+a • x) (Metric.ball 0 3)
      (Metric.ball y (3*a)) := fun x hx => hmap (R:=3) hx
  have hGc : ContinuousOn G (Metric.ball 0 3) :=
    (hF.comp hAff.continuousOn hm3).const_mul (a^4)
  have hGL : HasWeakLaplacian G (Metric.ball 0 2) (fun x => 4*Real.pi*τ x) := by
    have hh := HasWeakLaplacian.dilate ha (hLap.translate y)
    have hh' := hh.mono (show Metric.ball (0:Position) 2⊆(fun z => a • z) ⁻¹' {x | y+x∈Metric.ball y (2*a)} from
      fun x hx => hmap hx)
    convert hh' using 1
    funext x
    dsimp [G,τ]
    ring
  have hτ : Integrable τ := ((hi.comp_add_left y).comp_smul ha.ne').const_mul _
  have hτ0 (x) : 0≤τ x := mul_nonneg (pow_nonneg ha.le _) (hp _)
  have hτA (x) (hx : x∈Metric.closedBall (0:Position) 3) : τ x≤A := by
    have hh := mul_le_mul_of_nonneg_left (hb _ (hmapc hx)) (pow_nonneg ha.le 6)
    dsimp [τ]
    exact hh.trans_eq (by field_simp [ha.ne'])
  have hGM (x) (hx : x∈Metric.closedBall (0:Position) 2) : G x≤M := by
    have hh := mul_le_mul_of_nonneg_left (hcap _ (hmapc hx)) (pow_nonneg ha.le 4)
    dsimp [G]
    exact hh.trans_eq (by field_simp [ha.ne'])
  have hG0 : G 0=a^4*F y := by simp [G]
  have hGmean : volume.real (Metric.closedBall (0:Position) 2)*G 0 ≤
      (∫ x in Metric.closedBall 0 2, G x) := by
    rw [hG0]
    exact Coulomb.submean_affine y ha hmean
  let w := a⁻¹ • (z-y)
  have hw : w∈Metric.closedBall (0:Position) 1 := by
    have hdist : ‖z-y‖≤a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    simp only [Metric.mem_closedBall,dist_zero_right,w,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).mpr (by simpa using hdist)
  have hGw : G w=a^4*F z := by
    simp only [G,w,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,add_sub_cancel]
  have hh := H G τ hGc hGL hτ hτ0 hτA hGM hGmean w hw
  rw [hGw,hG0,←mul_sub,norm_mul,Real.norm_eq_abs (a^4),abs_of_pos (pow_pos ha 4)] at hh
  have hm : max (-(a^4*F y)) 0=a^4*max (-F y) 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le 4)]
    simp only [mul_zero,mul_neg]
  rw [hm] at hh
  have hn : ‖w‖=a⁻¹*‖z-y‖ := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  rw [hn] at hh
  have ht : a^4*(C*(‖z-y‖/a)*((a^4)⁻¹+max (-F y) 0)) =
      C*(1+a^4*max (-F y) 0)*(a⁻¹*‖z-y‖) := by
    field_simp [ha.ne']
  exact (mul_le_mul_iff_right₀ (pow_pos ha 4)).mp (hh.trans_eq ht.symm)

end NeutralAtom
end

end
end

end OAI
