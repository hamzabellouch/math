import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.FacetDeficitAnalytic
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.SliceMoments
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.FacetBody

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

end SliceTransport

namespace FacetVolume

end FacetVolume

namespace FacetVolume

lemma slice_ball_lower {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {b r : ℝ}
    {q : Fin n → ℝ} (hK : IsCompact K) (hball : Metric.ball q r ⊆ slice K b) :
    (volume (Metric.ball (0 : Fin n → ℝ) r)).toReal ≤ sliceVolume K b := by
  rw [← Measure.addHaar_ball_center volume q r]
  exact ENNReal.toReal_mono (compact_slice hK b).measure_lt_top.ne (measure_mono hball)

lemma projection_min_lt_top {n : ℕ} {K : Set (Fin (n+1) → ℝ)}
    {a b : ℝ} {z : Fin (n+1) → ℝ} (hK : IsCompact K)
    (hvol : 0 < volume K) (hz : z ∈ K) (hza : z 0 = a)
    (hproj : ∀ z ∈ K, z 0 ∈ Icc a b) : a < b := by
  have hab := (hza ▸ (hproj z hz)).2
  by_contra hnot
  have heq : a=b := le_antisymm hab (le_of_not_gt hnot)
  have h := intervalIntegral_sliceVolume hK hab hproj
  rw [heq, intervalIntegral.integral_same] at h
  exact (ENNReal.toReal_pos hvol.ne' hK.measure_lt_top.ne).ne' h.symm

theorem exists_uniform_facet_constant (n : ℕ) (r B : ℝ) (hr : 0 < r) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (K L M : Set (Fin (n+1) → ℝ)) (b d : ℝ)
      (qK qL : Fin n → ℝ),
      IsCompact K → IsCompact L → IsCompact M →
      Convex ℝ K → Convex ℝ L → Convex ℝ M →
      0 < volume K → 0 < volume L →
      (∀ z ∈ K, z 0 ∈ Icc (b-2) b) →
      (∀ z ∈ L, z 0 ∈ Icc (d-2) d) →
      Metric.ball qK r ⊆ slice K b → Metric.ball qL r ⊆ slice L d →
      (volume K).toReal ≤ B → (volume L).toReal ≤ B →
      (∀ x ∈ K, ∀ y ∈ L, (1/2 : ℝ) • x+(1/2 : ℝ) • y ∈ M) →
      κ * ((b-(∫ z in K, z 0)/(volume K).toReal)-
        (d-(∫ z in L, z 0)/(volume L).toReal))^2 ≤
      Real.log ((volume M).toReal/Real.sqrt ((volume K).toReal*(volume L).toReal)) := by
  let S := (volume (Metric.ball (0 : Fin n → ℝ) r)).toReal
  have hS : 0 < S := ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne
  let C := 2+|B|/S
  have hC2 : 2 ≤ C := le_add_of_nonneg_right (div_nonneg (abs_nonneg B) hS.le)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  refine ⟨(8*C^2+2^2)⁻¹, by positivity, ?_⟩
  intro K L M b d qK qL hK hL hM hcK hcL hcM hvolK hvolL hprojK hprojL hballK hballL hBK hBL hcomb
  have hS_K := slice_ball_lower hK hballK
  have hS_L := slice_ball_lower hL hballL
  have htopK : 0 < sliceVolume K b := hS.trans_le hS_K
  have htopL : 0 < sliceVolume L d := hS.trans_le hS_L
  have hKn : K.Nonempty := nonempty_of_measure_ne_zero hvolK.ne'
  have hLn : L.Nonempty := nonempty_of_measure_ne_zero hvolL.ne'
  obtain ⟨zK,hzK,hminK⟩ := hK.exists_isMinOn hKn (continuous_apply 0).continuousOn
  obtain ⟨zL,hzL,hminL⟩ := hL.exists_isMinOn hLn (continuous_apply 0).continuousOn
  have hprojK' : ∀ z ∈ K, z 0 ∈ Icc (zK 0) b := fun z hz => ⟨hminK hz,(hprojK z hz).2⟩
  have hprojL' : ∀ z ∈ L, z 0 ∈ Icc (zL 0) d := fun z hz => ⟨hminL hz,(hprojL z hz).2⟩
  have hKlt := projection_min_lt_top hK hvolK hzK rfl hprojK'
  have hLlt := projection_min_lt_top hL hvolL hzL rfl hprojL'
  have hK2 : b-zK 0 ≤ 2 := by linarith [(hprojK zK hzK).1]
  have hL2 : d-zL 0 ≤ 2 := by linarith [(hprojL zL hzL).1]
  have hKS : (volume K).toReal ≤ C*sliceVolume K b := by
    calc
      _ ≤ |B| := hBK.trans (le_abs_self B)
      _ ≤ C*S := by dsimp [C]; field_simp; nlinarith [hS]
      _ ≤ C*sliceVolume K b := mul_le_mul_of_nonneg_left hS_K hC.le
  have hLS : (volume L).toReal ≤ C*sliceVolume L d := by
    calc
      _ ≤ |B| := hBL.trans (le_abs_self B)
      _ ≤ C*S := by dsimp [C]; field_simp; nlinarith [hS]
      _ ≤ C*sliceVolume L d := mul_le_mul_of_nonneg_left hS_L hC.le
  simpa only [div_eq_mul_inv, mul_comm] using compact_body_facet_deficit hK hL hM hcK hcL hcM
    hKlt hLlt hC hzK rfl hzL rfl hprojK' hprojL' htopK htopL (hK2.trans hC2)
    (hL2.trans hC2) hK2 hL2 hKS hLS hcomb

end FacetVolume

end
end

end OAI
