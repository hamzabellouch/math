import OAI.Geometry.NodalSets.Elliptic.LocalMainLogJets
import OAI.Geometry.NodalSets.Elliptic.ShiftedCenterDistance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma eventually_shifted_main_distance (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℝ), 1 ≤ s → ∀ (x y v : Coord), ‖v‖ ≤ R →
      sourceEuclideanNorm (x-y) ≤ (n:ℝ)^(-5/12:ℝ) →
      ‖x+((n:ℝ)*s)⁻¹ • v-y‖ ≤ 2*(n:ℝ)^(-5/12:ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)^(7/12:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7/12)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop R),eventually_gt_atTop (0:ℕ)]
    with n hn hnpos
  intro s hs x y v hv hnear
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hd := rescaling_displacement_bound (x := x) hn1 hs hv
  rw [← main_radius_times_frequency hn0] at hn
  have hshift : ‖(x+((n:ℝ)*s)⁻¹ • v)-x‖ ≤ (n:ℝ)^(-5/12:ℝ) := by nlinarith
  have hxy := (norm_le_sourceEuclideanNorm _).trans hnear
  have he : x+((n:ℝ)*s)⁻¹ • v-y =
      (x+((n:ℝ)*s)⁻¹ • v-x)+(x-y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_shifted_main_log_jets (hUD : U ⊆ D) (R : ℝ) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0,
      ∀ᶠ n : ℕ in atTop, ∀ (x : Coord) (s : ℝ), 1 ≤ s →
      ∀ (v : Coord), ‖v‖ ≤ R → ∀ (i : SourceGrid U n × Fin 3),
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      let t := (latticeFrame a.cover hUD n i.1,i.2)
      let z := x+((n:ℝ)*s)⁻¹ • v
      ‖(a.beams.F t).symm z‖ < (n:ℝ)^(-1/3:ℝ) ∧
      ‖a.beams.amplitude n t z-1‖ ≤ Ca*(n:ℝ)^(-5/12:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t z‖ ∧ ‖a.beams.amplitude n t z‖ ≤ 3/2 ∧
      latticeWave a.cover a.beams hUD n i.1 i.2 z ≠ 0 ∧ ∀ u,
      |(normalizedLogJet n (latticeWave a.cover a.beams hUD n i.1 i.2) z u).re -
        (fderiv ℝ S z u-a.originalEta t*g (scaledLatticePoint n i.1)
          (z-scaledLatticePoint n i.1) u)| ≤ Cr*(n:ℝ)^(-5/6:ℝ)*‖u‖ ∧
      |(normalizedLogJet n (latticeWave a.cover a.beams hUD n i.1 i.2) z u).im -
        g (scaledLatticePoint n i.1) (a.cover.triple.q t.1 t.2) u| ≤
          Ci*(n:ℝ)^(-5/12:ℝ)*‖u‖ := by
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,hjets⟩ := a.original_main_logarithmic_jet_estimates 2 (by norm_num)
  refine ⟨Ca,hCa,Cr,hCr,Ci,hCi,?_⟩
  filter_upwards [hjets,eventually_shifted_main_distance R] with n hj hd
  intro x s hs v hv i hi
  have hz := hd s hs x (scaledLatticePoint n i.1) v hv hi
  have hh := hj (latticeFrame a.cover hUD n i.1,i.2) (x+((n:ℝ)*s)⁻¹ • v)
    (by simpa only [latticeFrame_center] using hz)
  simpa only [latticeFrame_center,latticeWave,TripleSourceWaveData.wave] using hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
