import OAI.Geometry.NodalSets.Elliptic.RescaledPhaseDefect
import OAI.Geometry.NodalSets.Waves.LatticeMainLogJets

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

theorem uniform_rescaled_phase_first (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ t x s, 1 ≤ s →
      sourceEuclideanNorm (x-y t.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      ∀ v : Coord, ‖v‖ ≤ R →
      let L := frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))
      ‖rescaledPhaseDefect (b.phase t) L n s x v‖ ≤ e ∧
      ‖fderiv ℝ (rescaledPhaseDefect (b.phase t) L n s x) v‖ ≤ e := by
  obtain ⟨dp,hdp,C,hC,hpbound⟩ := b.uniform_frozen_phase_gradient hg hp hS hy hp0
  obtain ⟨ds,hds,A,hA,D,hD,hsbound⟩ := b.uniform_spatial_bounds hg hp hy 1
  filter_upwards [eventually_shifted_main_distance R,
    eventually_nat_frequency (main_scale_eventually 2 1 (min dp ds) (lt_min hdp hds)),
    eventually_nat_frequency (main_scale_eventually (3*C*(R+1)) 1 e he)] with n hshift hn heps
  intro t x s hs hnear
  have hN : 1 ≤ (n:ℝ) := hn.1
  have hN0 : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hr : 0 < (n:ℝ)^(-5/12:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hx : ‖x-y t.1‖ ≤ (n:ℝ)^(-5/12:ℝ) := (norm_le_sourceEuclideanNorm _).trans hnear
  have hxdp : ‖x-y t.1‖ ≤ dp := by linarith [min_le_left dp ds,hn.2.1]
  have hzd (v : Coord) (hv : ‖v‖ ≤ R) := hshift s hs x (y t.1) v hv hnear
  let L := frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))
  have hsm (v : Coord) (hv : ‖v‖ ≤ R) : DifferentiableAt ℝ (b.phase t) (x+((n:ℝ)*s)⁻¹ • v) := by
    apply (hsbound t _ ((hzd v hv).trans (hn.2.1.trans (min_le_right _ _)))).2.1.differentiableAt
    simp
  have hb (v : Coord) (hv : ‖v‖ ≤ R) : ‖fderiv ℝ (b.phase t) (x+((n:ℝ)*s)⁻¹ • v)-L‖ ≤ 3*C*(n:ℝ)^(-5/12:ℝ) := by
    apply (hpbound t x _ hxdp ((hzd v hv).trans (hn.2.1.trans (min_le_left _ _)))).trans
    nlinarith [hzd v hv]
  intro v hv
  have hvalue := rescaledPhaseDefect_bound (b.phase t) L hN hs hR
    (by positivity : 0 ≤ 3*C*(n:ℝ)^(-5/12:ℝ)) x hsm hb v hv
  have hder := rescaledPhaseDefect_hasFDerivAt (b.phase t) L hN0.ne' hs0.ne' x v (hsm v hv)
  have he' : 3*C*(n:ℝ)^(-5/12:ℝ)*(R+1) ≤ e := by nlinarith [heps.2.1]
  constructor
  · exact hvalue.trans ((mul_le_mul_of_nonneg_left (hv.trans (by linarith)) (by positivity)).trans he')
  · rw [hder.fderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs0)]
    have hi : s⁻¹ ≤ 1 := (inv_le_one₀ hs0).mpr hs
    calc
      _ ≤ 1*(3*C*(n:ℝ)^(-5/12:ℝ)) := mul_le_mul hi (hb v hv) (norm_nonneg _) zero_le_one
      _ ≤ e := by nlinarith

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
