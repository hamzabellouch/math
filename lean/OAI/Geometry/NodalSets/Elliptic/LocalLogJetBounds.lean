import OAI.Geometry.NodalSets.Elliptic.LogJetBounds
import OAI.Geometry.NodalSets.Elliptic.ScalarBounds
import OAI.Geometry.NodalSets.Waves.LocalWaveHessian

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def originalEta (t : a.cover.Parameter × Fin 3) : ℝ :=
  sourceDirectionEta (g (coverSourceCenter a.cover t.1))
    (sourceHessian g S (coverSourceCenter a.cover t.1))
    (metricGradient g S (coverSourceCenter a.cover t.1)) (a.cover.triple.q t.1 t.2)

lemma eta_original (t : a.cover.Parameter × Fin 3) : a.beams.eta t = a.originalEta t := by
  unfold TripleSourceWaveData.eta originalEta
  rw [(a.center_identifications t.1).1,(a.center_identifications t.1).2.2.1,
    (a.center_identifications t.1).2.2.2]

lemma common_original_neighborhood : ∃ r > 0, ∀ t : a.cover.Parameter, ∀ x,
    ‖x-coverSourceCenter a.cover t‖ ≤ r → x ∈ a.E := by
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius isCompact_univ
    (fun z : a.cover.Parameter × Coord ↦ coverSourceCenter a.cover z.1+z.2)
    (((continuous_coverSourceCenter a.cover).comp continuous_fst).add continuous_snd)
    a.open_E (fun t _ ↦ by simpa only [add_zero] using (show coverSourceCenter a.cover t ∈ a.E from a.centers_E (a.cover.center t).property))
  refine ⟨r/2,by positivity,?_⟩
  intro t x hx
  have h := hri t (mem_univ t) (x-coverSourceCenter a.cover t) (by linarith)
  simpa using h

theorem original_logarithmic_jet_estimates (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∃ c > 0, ∃ C > 0,
      ∀ᶠ n : ℕ in atTop, ∀ t x,
      ‖x-coverSourceCenter a.cover t.1‖ ≤ L*(n:ℝ)^(-1/2:ℝ) →
      ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧
      a.beams.wave n t x ≠ 0 ∧
      (c ≤ ‖a.beams.wave n t x‖*Real.exp (-(n:ℝ)*S x) ∧
        ‖a.beams.wave n t x‖*Real.exp (-(n:ℝ)*S x) ≤ C) ∧
      ∀ v,
      |(normalizedLogJet n (a.beams.wave n t) x v).re -
        (fderiv ℝ S x v-a.originalEta t*g (coverSourceCenter a.cover t.1) (x-coverSourceCenter a.cover t.1) v)| ≤ Cr/n*‖v‖ ∧
      |(normalizedLogJet n (a.beams.wave n t) x v).im -
        g (coverSourceCenter a.cover t.1) (a.cover.triple.q t.1 t.2) v| ≤ Ci*(n:ℝ)^(-1/2:ℝ)*‖v‖ := by
  have hy := continuous_coverSourceCenter a.cover
  have hp0 (t : a.cover.Parameter) := a.nonzero_gradient _ (a.cover.center t).property
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,hjet⟩ := a.beams.uniform_logarithmic_jet_estimates
    a.smooth_G a.symmetric_G a.positive_G a.smooth_A hy hp0 L hL
  obtain ⟨c,hc,C,hC,hscalar⟩ := a.beams.uniform_relative_wave_bounds
    a.smooth_G a.positive_G a.smooth_A hy hp0 L hL
  obtain ⟨r,hr,hri⟩ := a.common_original_neighborhood
  refine ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,?_⟩
  filter_upwards [eventually_nat_frequency hjet,eventually_nat_frequency hscalar,
    eventually_nat_frequency (half_scale_eventually L 1 r hr)] with n hj hs hn
  intro t x hx
  have hxE := hri t.1 x (hx.trans hn.2.1)
  obtain ⟨_,_,hA⟩ := a.germ x hxE
  obtain ⟨ha,hl,hu,hne,hrest⟩ := hj t x hx
  have hsc := hs t x hx
  rw [hA.self_of_nhds] at hsc
  refine ⟨ha,hl,hu,hne,hsc,?_⟩
  intro v
  have hh := hrest v
  rw [hA.fderiv_eq,a.eta_original,(a.center_identifications t.1).1] at hh
  exact hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
