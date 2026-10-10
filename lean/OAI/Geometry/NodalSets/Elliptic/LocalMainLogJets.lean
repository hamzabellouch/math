import OAI.Geometry.NodalSets.Elliptic.LocalLogJetBounds
import OAI.Geometry.NodalSets.Elliptic.MainLogJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem original_main_logarithmic_jet_estimates (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0,
      ∀ᶠ n : ℕ in atTop, ∀ t x,
      ‖x-coverSourceCenter a.cover t.1‖ ≤ L*(n:ℝ)^(-5/12:ℝ) →
      ‖(a.beams.F t).symm x‖ < (n:ℝ)^(-1/3:ℝ) ∧
      ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-5/12:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧
      a.beams.wave n t x ≠ 0 ∧ ∀ v,
      |(normalizedLogJet n (a.beams.wave n t) x v).re -
        (fderiv ℝ S x v-a.originalEta t*g (coverSourceCenter a.cover t.1)
          (x-coverSourceCenter a.cover t.1) v)| ≤ Cr*(n:ℝ)^(-5/6:ℝ)*‖v‖ ∧
      |(normalizedLogJet n (a.beams.wave n t) x v).im -
        g (coverSourceCenter a.cover t.1) (a.cover.triple.q t.1 t.2) v| ≤
          Ci*(n:ℝ)^(-5/12:ℝ)*‖v‖ := by
  have hy := continuous_coverSourceCenter a.cover
  have hp0 (t : a.cover.Parameter) := a.nonzero_gradient _ (a.cover.center t).property
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,hjet⟩ := a.beams.uniform_main_logarithmic_jet_estimates
    a.smooth_G a.symmetric_G a.positive_G a.smooth_A hy hp0 L hL
  obtain ⟨r,hr,hri⟩ := a.common_original_neighborhood
  refine ⟨Ca,hCa,Cr,hCr,Ci,hCi,?_⟩
  filter_upwards [eventually_nat_frequency hjet,
    eventually_nat_frequency (main_scale_eventually L 1 r hr)] with n hj hn
  intro t x hx
  have hxE := hri t.1 x (hx.trans hn.2.1)
  obtain ⟨_,_,hA⟩ := a.germ x hxE
  obtain ⟨hcut,ha,hl,hu,hne,hrest⟩ := hj t x hx
  refine ⟨hcut,ha,hl,hu,hne,?_⟩
  intro v
  have hh := hrest v
  rw [hA.fderiv_eq,a.eta_original,(a.center_identifications t.1).1] at hh
  exact hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
