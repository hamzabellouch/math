import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakHarmonicMean
import OAI.Analysis.CoulombIonization.Localization.PacketScaleControl

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma weak_harmonic_packet_oscillation {u : Space → ℝ} (hu : Continuous u)
    {R : ℝ} (hR : 0 < R) (hn : ∀ z ∈ closedBall (0 : Space) (3*R), 0 ≤ u z)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (3*R) → (∫ z, u z*Δ g z) = 0)
    {L : NNReal} {p : ℝ} (hp : 0 < p) (hL : LipschitzWith L (packetDensity 0 1))
    (hlo : ∀ z : Space, ‖z‖ ≤ 3/4 → p ≤ packetDensity 0 1 z)
    (x : Space) (hx : ‖x‖ ≤ R/2) :
    |u x-u 0| ≤ (8*(L:ℝ)/p)/R*‖x‖*u 0 := by
  have hm0 := weak_harmonic_packet_mean hu 0 hR (by linarith : R < 3*R) hw
  have hmb := weak_harmonic_packet_mean hu 0 (by linarith : 0 < 2*R)
    (by linarith : 2*R < 3*R) hw
  have hmx := weak_harmonic_packet_mean hu x hR (by linarith : R < 2*R)
    (fun g hg hcg hs => hw g hg hcg (fun z hz => ?_))
  · let D : ℝ := (8*(L:ℝ)/p)/R*‖x‖
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hi (y : Space) {r : ℝ} (hr : 0 < r) : Integrable (fun z => packetDensity y r z*u z) :=
      ((packetDensity_continuous y r).mul hu).integrable_of_hasCompactSupport
        (packetDensity_compact y hr).mul_right
    have hid : Integrable (fun z => (packetDensity x R z-packetDensity 0 R z)*u z) := by
      convert! (hi x hR).sub (hi 0 hR) using 1
      ext z
      change (packetDensity x R z-packetDensity 0 R z)*u z =
        packetDensity x R z*u z-packetDensity 0 R z*u z
      ring
    have hbn (z : Space) : 0 ≤ packetDensity 0 (2*R) z*u z := by
      by_cases hz : packetDensity 0 (2*R) z = 0
      · simp [hz]
      · apply mul_nonneg (packetDensity_nonneg _ _ _) (hn z _)
        have ht := packetDensity_support 0 (by linarith : 0 < 2*R) hz
        rw [sub_zero] at ht
        simpa only [mem_closedBall,dist_zero_right] using ht.trans (by linarith : 2*R ≤ 3*R)
    have hb (z : Space) : |(packetDensity x R z-packetDensity 0 R z)*u z| ≤
        D*(packetDensity 0 (2*R) z*u z) := by
      by_cases hd : packetDensity x R z-packetDensity 0 R z = 0
      · simpa only [hd,zero_mul,abs_zero] using mul_nonneg hD (hbn z)
      · have hz : ‖z‖ ≤ 3*R/2 := by
          by_cases ha : packetDensity x R z = 0
          · have hb : packetDensity 0 R z ≠ 0 := by intro hb; simp [ha,hb] at hd
            have ht := packetDensity_support 0 hR hb
            rw [sub_zero] at ht
            linarith
          · have ht := packetDensity_support x hR ha
            have hh : ‖z‖ ≤ ‖z-x‖+‖x‖ := by
              calc ‖z‖ = ‖(z-x)+x‖ := by rw [sub_add_cancel]
                   _ ≤ ‖z-x‖+‖x‖ := norm_add_le _ _
            linarith
        have huz : 0 ≤ u z := hn z (by
          simpa only [mem_closedBall,dist_zero_right] using hz.trans (by linarith : 3*R/2 ≤ 3*R))
        have hpl := packetDensity_scaled_lower (by linarith : 0 < 2*R) hlo
          (z := z) (by linarith)
        have hdf := packetDensity_scaled_difference hL hR x 0 z
        rw [sub_zero] at hdf
        have he : D*(p/(2*R)^3) = (L:ℝ)/R^4*‖x‖ := by
          dsimp [D]
          field_simp
          ring
        rw [abs_mul,abs_of_nonneg huz,←mul_assoc]
        apply mul_le_mul_of_nonneg_right _ huz
        calc
          _ ≤ (L:ℝ)/R^4*‖x‖ := hdf
          _ = D*(p/(2*R)^3) := he.symm
          _ ≤ D*packetDensity 0 (2*R) z := mul_le_mul_of_nonneg_left hpl hD
    calc
      |u x-u 0| = |∫ z, (packetDensity x R z-packetDensity 0 R z)*u z| := by
        simp only [sub_mul,integral_sub (hi x hR) (hi 0 hR),hmx,hm0]
      _ ≤ ∫ z, |(packetDensity x R z-packetDensity 0 R z)*u z| := abs_integral_le_integral_abs
      _ ≤ ∫ z, D*(packetDensity 0 (2*R) z*u z) :=
        integral_mono hid.abs ((hi 0 (by linarith : 0 < 2*R)).const_mul D) hb
      _ = D*u 0 := by rw [integral_const_mul,hmb]
  · have ht : ‖z-x‖ < 2*R := by simpa only [mem_ball,dist_eq_norm] using hs hz
    have hh : ‖z‖ ≤ ‖z-x‖+‖x‖ := by
      calc ‖z‖ = ‖(z-x)+x‖ := by rw [sub_add_cancel]
           _ ≤ ‖z-x‖+‖x‖ := norm_add_le _ _
    simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < 3*R by linarith)

theorem exists_weak_harmonic_oscillation_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (u : Space → ℝ) (R : ℝ), 0 < R → ContinuousOn u (closedBall 0 (3*R)) →
      (∀ z ∈ closedBall (0 : Space) (3*R), 0 ≤ u z) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 (3*R) → (∫ z, u z*Δ g z) = 0) →
      ∀ x : Space, ‖x‖ ≤ R/2 → |u x-u 0| ≤ C/R*‖x‖*u 0 := by
  obtain ⟨L,p,hp,hL,hlo⟩ := exists_packet_unit_control
  let C : ℝ := 8*(L:ℝ)/p+1
  have hbase : 0 ≤ 8*(L:ℝ)/p := by positivity
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro u R hR hu hn hw x hx
  let f : C(closedBall (0 : Space) (3*R),ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall (0 : Space) (3*R)) : v z = u z :=
    congrArg (fun h : C(closedBall (0 : Space) (3*R),ℝ) => h ⟨z,hz⟩) hv
  have hh := weak_harmonic_packet_oscillation v.continuous hR
    (fun z hz => by rw [he z hz]; exact hn z hz) (fun g hg hcg hs => ?_) hp hL hlo x hx
  · rw [he x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans (by linarith : R/2 ≤ 3*R)),
      he 0 (mem_closedBall_self (by positivity))] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (hn 0 (mem_closedBall_self (by positivity)))
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ hR.le
    dsimp [C]; linarith
  · convert hw g hg hcg hs using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z*Δ g z = u z*Δ g z
        rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]

end CoulombAnalysis

end

end OAI
