import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakComparison
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakHarmonicMean
import OAI.Analysis.CoulombIonization.Localization.PacketScaleControl

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma packetDensity_scaled_upper {P : ℝ}
    (hP : ∀ z : Space, packetDensity 0 1 z ≤ P) (x y : Space) {r : ℝ} (hr : 0 < r) :
    packetDensity x r y ≤ P/r^3 := by
  rw [packetDensity_scale x y hr]
  have hh := mul_le_mul_of_nonneg_left (hP (r⁻¹ • (y-x))) (pow_nonneg (inv_nonneg.mpr hr.le) 3)
  simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hh

lemma weak_harmonic_mean_from_larger_ball {u : Space → ℝ} {c : Space} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall c (3*R)))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ x, u x*Δ g x) = 0)
    {x : Space} (hx : x ∈ closedBall c R) :
    (∫ z, packetDensity x R z*u z) = u x := by
  have hsub : closedBall x (2*R) ⊆ closedBall c (3*R) := by
    intro z hz
    rw [mem_closedBall] at hx hz ⊢
    have hh := dist_triangle z x c
    linarith
  apply weak_harmonic_packet_mean_local (hu.mono hsub) hR (by linarith)
  intro g hg hcg hs
  exact hw g hg hcg (hs.trans (by
    intro z hz
    rw [mem_ball] at hz ⊢
    have hxc : dist x c ≤ R := hx
    have hh := dist_triangle z x c
    linarith))

lemma packet_integrable_on_larger_ball {u : Space → ℝ} {c : Space} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall c (3*R)))
    {x : Space} (hx : x ∈ closedBall c R) :
    Integrable (fun z => packetDensity x R z*u z) := by
  have hh := continuousOn_mul_integrable_support (isCompact_closedBall c (3*R)) hu
    (packetDensity_continuous x R) (fun z hz => by
      have hz' := packetDensity_support x hR hz
      rw [mem_closedBall] at hx ⊢
      rw [←dist_eq_norm] at hz'
      have ht := dist_triangle z x c
      linarith)
  simpa only [mul_comm] using hh

theorem exists_weak_harmonic_L1_constants : ∃ P L : ℝ, 0 ≤ P ∧ 0 ≤ L ∧
    ∀ (u : Space → ℝ) (c : Space) (R : ℝ), 0 < R →
    ContinuousOn u (closedBall c (3*R)) →
    (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ x, u x*Δ g x) = 0) →
    ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      |u x| ≤ P/R^3*(∫ z in closedBall c (3*R), |u z|) ∧
      |u x-u y| ≤ L/R^4*(∫ z in closedBall c (3*R), |u z|)*‖x-y‖ := by
  obtain ⟨P,hP⟩ := (packetDensity_compact (0 : Space) (by norm_num : (0:ℝ)<1)).exists_bound_of_continuous
    (packetDensity_continuous 0 1)
  obtain ⟨L,_p,_hp,hL,_hlow⟩ := exists_packet_unit_control
  have hP0 : 0 ≤ P := (norm_nonneg (packetDensity 0 1 0)).trans (hP 0)
  have hPu (z : Space) : packetDensity 0 1 z ≤ P :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hP z)
  refine ⟨P,L,hP0,L.coe_nonneg,?_⟩
  intro u c R hR hu hw x hx y hy
  let K := closedBall c (3*R)
  have hK : MeasurableSet K := isClosed_closedBall.measurableSet
  have hi : Integrable (K.indicator (fun z => |u z|)) :=
    (hu.abs.integrableOn_compact (isCompact_closedBall c (3*R))).integrable_indicator hK
  have hm := weak_harmonic_mean_from_larger_ball hR hu hw hx
  have hm' := weak_harmonic_mean_from_larger_ball hR hu hw hy
  have hix := packet_integrable_on_larger_ball hR hu hx
  have hiy := packet_integrable_on_larger_ball hR hu hy
  have hzpacket (z : Space) (hz : z ∉ K) (w : Space) (hw' : w ∈ closedBall c R) :
      packetDensity w R z = 0 := by
    by_contra hne
    have hs := packetDensity_support w hR hne
    apply hz
    rw [mem_closedBall] at hw' ⊢
    rw [←dist_eq_norm] at hs
    have ht := dist_triangle z w c
    linarith
  constructor
  · have hb := norm_integral_le_of_norm_le (hi.const_mul (P/R^3))
      (f := fun z => packetDensity x R z*u z) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (packetDensity_nonneg x R z)]
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz]
          exact mul_le_mul_of_nonneg_right (packetDensity_scaled_upper hPu x z hR) (abs_nonneg _)
        · simp only [indicator_of_notMem hz,hzpacket z hz x hx,zero_mul,mul_zero,le_refl]))
    rw [Real.norm_eq_abs,hm,integral_const_mul,integral_indicator hK] at hb
    exact hb
  · have he : (∫ z, (packetDensity x R z-packetDensity y R z)*u z) = u x-u y := by
      simp_rw [sub_mul]
      rw [integral_sub hix hiy,hm,hm']
    have hb := norm_integral_le_of_norm_le (hi.const_mul ((L:ℝ)/R^4*‖x-y‖))
      (f := fun z => (packetDensity x R z-packetDensity y R z)*u z)
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul]
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz]
          exact mul_le_mul_of_nonneg_right (packetDensity_scaled_difference hL hR x y z) (abs_nonneg _)
        · simp only [indicator_of_notMem hz,hzpacket z hz x hx,hzpacket z hz y hy,
            sub_self,abs_zero,zero_mul,mul_zero,le_refl]))
    rw [Real.norm_eq_abs,he,integral_const_mul,integral_indicator hK] at hb
    convert hb using 1
    ring

end CoulombAnalysis

end

end OAI
