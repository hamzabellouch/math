import OAI.Geometry.NodalSets.Waves.LatticeSourceWaves
import OAI.Geometry.NodalSets.Waves.LocalCompactWaves
import OAI.Geometry.NodalSets.Waves.WaveGerm

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma center_identifications (t : a.cover.Parameter) :
    a.G (coverSourceCenter a.cover t) = g (coverSourceCenter a.cover t) ∧
    a.A (coverSourceCenter a.cover t) = S (coverSourceCenter a.cover t) ∧
    metricGradient a.G a.A (coverSourceCenter a.cover t) = metricGradient g S (coverSourceCenter a.cover t) ∧
    sourceHessian a.G a.A (coverSourceCenter a.cover t) = sourceHessian g S (coverSourceCenter a.cover t) := by
  obtain ⟨hG,hW,hA⟩ := a.germ _ (a.centers_E (a.cover.center t).property)
  exact ⟨hG.self_of_nhds,hA.self_of_nhds,(metricGradient_eventuallyEq hG hA).self_of_nhds,
    (sourceHessian_eventuallyEq hG hA).self_of_nhds⟩

lemma source_phase_center (t : a.cover.Parameter × Fin 3) :
    a.beams.phase t (coverSourceCenter a.cover t.1) = (S (coverSourceCenter a.cover t.1):ℂ) := by
  rw [a.beams.phase_center,(a.center_identifications t.1).2.1]

lemma source_wave_center (N : ℝ) (hN : 0 < N) (t : a.cover.Parameter × Fin 3) :
    a.beams.wave N t (coverSourceCenter a.cover t.1) =
      Complex.exp ((N:ℂ)*(S (coverSourceCenter a.cover t.1):ℂ)) := by
  rw [a.beams.wave_center N hN,(a.center_identifications t.1).2.1]

lemma source_phase_first (t : a.cover.Parameter × Fin 3) (v : Coord) :
    fderiv ℝ (a.beams.phase t) (coverSourceCenter a.cover t.1) v =
      (g (coverSourceCenter a.cover t.1) (metricGradient g S (coverSourceCenter a.cover t.1)) v:ℂ)+
        Complex.I*(g (coverSourceCenter a.cover t.1) (a.cover.triple.q t.1 t.2) v:ℂ) := by
  have h := a.beams.phase_first a.positive_G
    (fun t ↦ a.nonzero_gradient _ (a.cover.center t).property) t v
  rw [(a.center_identifications t.1).1,(a.center_identifications t.1).2.2.1] at h
  exact h

lemma source_phase_second (t : a.cover.Parameter × Fin 3) (v : Coord) :
    sourceHessian g (fun z ↦ (a.beams.phase t z).re) (coverSourceCenter a.cover t.1) v v =
      sourceHessian g S (coverSourceCenter a.cover t.1) v v -
        sourceDirectionEta (g (coverSourceCenter a.cover t.1)) (sourceHessian g S (coverSourceCenter a.cover t.1))
          (metricGradient g S (coverSourceCenter a.cover t.1)) (a.cover.triple.q t.1 t.2) *
          g (coverSourceCenter a.cover t.1) v v := by
  have h := a.beams.phase_second a.smooth_G a.symmetric_G a.positive_G a.smooth_A
    (fun t ↦ a.nonzero_gradient _ (a.cover.center t).property) t v
  obtain ⟨hG,_,_⟩ := a.germ _ (a.centers_E (a.cover.center t.1).property)
  have he := (sourceHessian_eventuallyEq hG
    (Filter.EventuallyEq.refl (𝓝 (coverSourceCenter a.cover t.1)) (fun z ↦ (a.beams.phase t z).re))).self_of_nhds
  change sourceHessian a.G (fun z ↦ (a.beams.phase t z).re) (coverSourceCenter a.cover t.1) =
    sourceHessian g (fun z ↦ (a.beams.phase t z).re) (coverSourceCenter a.cover t.1) at he
  rw [he,(a.center_identifications t.1).1,(a.center_identifications t.1).2.2.1,
    (a.center_identifications t.1).2.2.2] at h
  exact h

theorem local_lattice_estimates {U : Set Coord} (hUD : U ⊆ D) :
    ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3),
      let V := latticeWave a.cover a.beams hUD n z j
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ a.E ∧
      tsupport V ⊆ {x | sourceEuclideanNorm (x-scaledLatticePoint n z) ≤ a.beams.R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ x : Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V x‖ ≤
          a.beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x-a.beams.c*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2)) ∧
        DerivativeBound k0 (fun x ↦ sourceWeightedOperator g w V x+((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V x) x
          (a.beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
  filter_upwards [a.estimates] with n hn
  intro z j
  simpa only [latticeWave,TripleSourceWaveData.wave,latticeFrame_center] using hn (latticeFrame a.cover hUD n z,j)

lemma local_lattice_nonzero {U : Set Coord} (hUD : U ⊆ D) (n : ℕ) (hn : 0 < n)
    (z : SourceGrid U n) (j : Fin 3) : latticeWave a.cover a.beams hUD n z j ≠ 0 :=
  a.beams.wave_ne_zero n (by exact_mod_cast hn) (latticeFrame a.cover hUD n z,j)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
