import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.AmplitudeOscillation
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorFieldPDE

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma enlarged_band_near {r L : ℝ} (hr : 0 < r) (hL : 1 ≤ L)
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz : ‖z-y‖ ≤ 3*(r/16)) :
    3*r/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 6*L*r := by
  have h0 := norm_le_norm_add_norm_sub z y
  have h1 := norm_le_norm_add_norm_sub y z
  rw [norm_sub_rev y z] at h1
  have hLr := mul_le_mul_of_nonneg_right hL hr.le
  constructor <;> linarith

theorem atomic_band_negative_oscillation {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ,0 < C ∧ ∀ (ρ : Position → ℝ) (Z r L lam : ℝ),
      Integrable ρ → Measurable ρ → (∀ x,0 ≤ ρ x) →
      (∃ B : ℝ,∀ x,ρ x ≤ B) → Continuous (potentialOf ρ) →
      0 < r → 1 ≤ L → 1 ≤ lam →
      (∀ x,3*r/4 ≤ ‖x‖ → ‖x‖ ≤ 6*L*r → ρ x ≤ lam*(A/r^6)) →
      (∀ x,3*r/4 ≤ ‖x‖ → ‖x‖ ≤ 6*L*r →
        Z*coulombKernel x-potentialOf ρ x ≤ lam*(M/r^4)) →
      ∀ y z : Position,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ‖z-y‖ ≤ r/16 →
        ‖(Z*coulombKernel z-potentialOf ρ z)-(Z*coulombKernel y-potentialOf ρ y)‖ ≤
          C*(‖z-y‖/r)*(lam/r^4+max (-(Z*coulombKernel y-potentialOf ρ y)) 0) := by
  obtain ⟨C,hC,H⟩ := poisson_amplitude_negative_oscillation hA hM
  refine ⟨16^5*C,by positivity,?_⟩
  intro ρ Z r L lam hi hm hp hb hc hr hL hlam hd hcap y z hy0 hy1 hz
  let F := fun x => Z*coulombKernel x-potentialOf ρ x
  let a := r/16
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a ≤ r := by dsimp [a]; linarith
  have hnear (x : Position) (hx : x∈Metric.closedBall y (3*a)) :
      3*r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 6*L*r :=
    enlarged_band_near hr hL hy0 hy1 (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  have hnot (b : ℝ) (hb : b ≤ 3*a) : (0:Position) ∉ Metric.ball y b := by
    intro h0
    have he := hnear 0 (Metric.mem_closedBall.mpr ((Metric.mem_ball.mp h0).le.trans hb))
    simp only [norm_zero] at he
    linarith [he.1]
  have hF : ContinuousOn F (Metric.ball y (3*a)) :=
    ((continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr
      (fun he => hnot (3*a) le_rfl (he ▸ hx)))).const_mul Z).sub hc.continuousOn
  have hLap := atomic_screenedField_weakLaplacian hi hc Z (hnot (2*a) (by linarith))
  have hden (x) (hx : x∈Metric.closedBall y (3*a)) : ρ x ≤ lam*(A/a^6) := by
    apply (hd x (hnear x hx).1 (hnear x hx).2).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact div_le_div_of_nonneg_left hA (pow_pos ha _) (pow_le_pow_left₀ ha.le har _)
  have hbound (x) (hx : x∈Metric.closedBall y (2*a)) : F x ≤ lam*(M/a^4) := by
    have hx' : x∈Metric.closedBall y (3*a) := Metric.closedBall_subset_closedBall (by linarith) hx
    apply (hcap x (hnear x hx').1 (hnear x hx').2).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact div_le_div_of_nonneg_left hM (pow_pos ha _) (pow_le_pow_left₀ ha.le har _)
  obtain ⟨B,hB⟩ := hb
  have hmean := atomic_screened_ballCloud_submean hi hm hp hB Z (by linarith : 0 < 2*a) y
    (by dsimp [a]; linarith : 2*a ≤ ‖y‖)
  have HH := H F ρ y a lam ha (by linarith) hF hLap hi hp hden hbound hmean z
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz)
  apply HH.trans
  have hNN : 0 ≤ max (-F y) 0 := le_max_right _ _
  have hn : 0 ≤ ‖z-y‖ := norm_nonneg _
  dsimp only [a,F] at hNN ⊢
  field_simp
  norm_num
  simp only [neg_sub] at hNN
  nlinarith [mul_nonneg (mul_nonneg hn (pow_nonneg hr.le 4)) hNN]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma packetKernel_fixed_amplitude {g : Position → ℝ} {B c r₀ s : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ z, |g z^2| ≤ B)
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (x y : Position) :
    |packetKernel g c r₀ s x y| ≤ B/(packetWidth c r₀ s x)^3 := by
  have ht := packetWidth_pos hc hr hs x
  unfold packetKernel
  rw [abs_mul,abs_of_pos (by positivity : 0 < ((packetWidth c r₀ s x)^3)⁻¹)]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul (hbound ((packetWidth c r₀ s x)⁻¹ • (y-x))) le_rfl
      (by positivity : 0 ≤ ((packetWidth c r₀ s x)^3)⁻¹) hB

lemma packetKernel_fixed_lipschitz {g : Position → ℝ} {L c r₀ s : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ z v, |g z^2-g v^2| ≤ L*‖z-v‖)
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (x y z : Position) :
    |packetKernel g c r₀ s x y-packetKernel g c r₀ s x z| ≤
      (L/(packetWidth c r₀ s x)^4)*‖y-z‖ := by
  let t := packetWidth c r₀ s x
  have ht : 0 < t := packetWidth_pos hc hr hs x
  change |(t^3)⁻¹*g (t⁻¹ • (y-x))^2-(t^3)⁻¹*g (t⁻¹ • (z-x))^2| ≤ _
  rw [←mul_sub,abs_mul,abs_of_pos (by positivity : 0 < (t^3)⁻¹)]
  calc
    _ ≤ (t^3)⁻¹*(L*‖t⁻¹ • (y-x)-t⁻¹ • (z-x)‖) :=
      by
        simpa only [_root_.mul_comm] using
          mul_le_mul (hlip (t⁻¹ • (y-x)) (t⁻¹ • (z-x))) (le_refl ((t^3)⁻¹))
            (by positivity) (mul_nonneg hL (norm_nonneg _))
    _ = (L/t^4)*‖y-z‖ := by
      rw [←smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      field_simp
    _ = _ := rfl

theorem mixture_packet_band_bounds {n : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g)
    {B L c r₀ s τ : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ z, |g z^2| ≤ B) (hlip : ∀ z v, |g z^2-g v^2| ≤ L*‖z-v‖)
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (hτ : 0 < τ)
    {S T : Set Position} (hS : MeasurableSet S)
    (hsp : ∀ y∈T,∀ x,packetKernel g c r₀ s x y ≠ 0 → x∈S)
    (hw : ∀ x∈S,τ ≤ packetWidth c r₀ s x) :
    (∀ y∈T,mixturePacketDensity ν g c r₀ s y ≤
      (B/τ^3)*(∫ x,rawCount S x ∂ν)) ∧
    (∀ y∈T,∀ z∈T,|mixturePacketDensity ν g c r₀ s y-mixturePacketDensity ν g c r₀ s z| ≤
      (L/τ^4)*‖y-z‖*(∫ x,rawCount S x ∂ν)) := by
  have hcount : Integrable (rawCount (n:=n) S) ν := by
    apply Integrable.of_bound (measurable_rawCount hS).aestronglyMeasurable (n:ℝ)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (rawCount_nonneg S x)]
    exact rawCount_le_number S x
  have hpoint (x y : Position) (hy : y∈T) :
      packetKernel g c r₀ s x y ≤ (B/τ^3)*S.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx,mul_one]
      apply (le_abs_self _).trans
      apply (packetKernel_fixed_amplitude hB hbound hc hr hs x y).trans
      exact div_le_div_of_nonneg_left hB (pow_pos hτ 3) (pow_le_pow_left₀ hτ.le (hw x hx) 3)
    · have hz : packetKernel g c r₀ s x y=0 := by by_contra hh; exact hx (hsp y hy x hh)
      simp only [hz,Set.indicator_of_notMem hx,mul_zero,le_refl]
  have hdiff (x y z : Position) (hy : y∈T) (hz : z∈T) :
      |packetKernel g c r₀ s x y-packetKernel g c r₀ s x z| ≤
        ((L/τ^4)*‖y-z‖)*S.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx,mul_one]
      apply (packetKernel_fixed_lipschitz hL hlip hc hr hs x y z).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact div_le_div_of_nonneg_left hL (pow_pos hτ 4) (pow_le_pow_left₀ hτ.le (hw x hx) 4)
    · have hy0 : packetKernel g c r₀ s x y=0 := by by_contra hh; exact hx (hsp y hy x hh)
      have hz0 : packetKernel g c r₀ s x z=0 := by by_contra hh; exact hx (hsp z hz x hh)
      simp only [hy0,hz0,sub_self,abs_zero,Set.indicator_of_notMem hx,mul_zero,le_refl]
  constructor
  · intro y hy
    have H := integral_mono (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
      (hcount.const_mul (B/τ^3)) (fun x => show rawPacketDensity g c r₀ s x y ≤ (B/τ^3)*rawCount S x from by
        unfold rawPacketDensity rawCount
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => hpoint (x i) y hy))
    simpa only [mixturePacketDensity,integral_const_mul] using H
  · intro y hy z hz
    have hi := (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y).sub
      (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν z)
    change |(∫ x,rawPacketDensity g c r₀ s x y ∂ν)-(∫ x,rawPacketDensity g c r₀ s x z ∂ν)| ≤ _
    rw [←integral_sub (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
      (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν z)]
    apply (abs_integral_le_integral_abs).trans
    have H := integral_mono hi.abs (hcount.const_mul ((L/τ^4)*‖y-z‖)) (fun x => show
      |rawPacketDensity g c r₀ s x y-rawPacketDensity g c r₀ s x z| ≤ ((L/τ^4)*‖y-z‖)*rawCount S x from by
        unfold rawPacketDensity rawCount
        rw [←Finset.sum_sub_distrib,Finset.mul_sum]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hdiff (x i) y z hy hz)))
    simpa only [integral_const_mul,Pi.sub_apply] using H
end NeutralAtom
end

end

end OAI
