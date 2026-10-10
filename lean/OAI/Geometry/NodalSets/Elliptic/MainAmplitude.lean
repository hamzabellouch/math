import OAI.Geometry.NodalSets.Waves.LatticeMainLogJets
import OAI.Geometry.NodalSets.Waves.NormalizedWaveRatio

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_main_amplitude_ratio (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hy : Continuous y)
    (R e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ t x s, 1 ≤ s →
      sourceEuclideanNorm (x-y t.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      ∀ v : Coord, ‖v‖ ≤ R →
      b.amplitude n t x ≠ 0 ∧
      ‖b.amplitude n t (x+((n:ℝ)*s)⁻¹ • v)/b.amplitude n t x-1‖ ≤ e ∧
      (b.wave n t =ᶠ[𝓝 x] (fun z ↦ b.amplitude n t z*Complex.exp ((n:ℂ)*b.phase t z))) ∧
      (b.wave n t =ᶠ[𝓝 (x+((n:ℝ)*s)⁻¹ • v)]
        (fun z ↦ b.amplitude n t z*Complex.exp ((n:ℂ)*b.phase t z))) := by
  obtain ⟨delta,hd,C,hC,D,hD,hb⟩ := b.uniform_amplitude_bounds hg hp hy
  filter_upwards [eventually_shifted_main_distance R,
    eventually_nat_frequency (main_scale_eventually 2 D delta hd),
    eventually_nat_frequency (main_scale_eventually (6*C) 1 e he)] with n hshift hn heps
  intro t x s hs hnear v hv
  have hN0 : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hn.1
  have hr : 0 < (n:ℝ)^(-5/12:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hx := (norm_le_sourceEuclideanNorm _).trans hnear
  have hz := hshift s hs x (y t.1) v hv hnear
  have hx2 : ‖x-y t.1‖ ≤ 2*(n:ℝ)^(-5/12:ℝ) := by linarith
  have hall (z : Coord) (hz : ‖z-y t.1‖ ≤ 2*(n:ℝ)^(-5/12:ℝ)) := hb t z (hz.trans hn.2.1)
  have hbx := hall x hx2
  have hbz := hall _ hz
  have hagx := hbx.2.2.2 n hn.1
  have hagz := hbz.2.2.2 n hn.1
  have hdiff : ‖b.amplitude n t (x+((n:ℝ)*s)⁻¹ • v)-b.amplitude n t x‖ ≤
      3*C*(n:ℝ)^(-5/12:ℝ) := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ 1 _).trans
    rw [norm_sub_rev (1:ℂ)]
    exact (add_le_add hagz.2.1 hagx.2.1).trans (by nlinarith)
  refine ⟨hagx.2.2.2.2.1,(amplitude_ratio_near_one hagx.2.2.1 hdiff).trans (by nlinarith [heps.2.1]),?_,?_⟩
  · exact b.wave_germ_of_small_inverse n hN0 t x hbx.1
      ((hbx.2.1.trans (mul_le_mul_of_nonneg_left hx2 (by linarith))).trans_lt hn.2.2)
  · exact b.wave_germ_of_small_inverse n hN0 t _ hbz.1
      ((hbz.2.1.trans (mul_le_mul_of_nonneg_left hz (by linarith))).trans_lt hn.2.2)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
