import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights
import OAI.Geometry.NodalSets.Waves.PlaneWaveJets2

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_main_coefficient_jets (hUD : U ⊆ D) (R : ℝ) (hR : 0 ≤ R)
    (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ D, ∀ s : ℝ, 1 ≤ s →
      ∀ (sigma : ℝ) (v : Coord), ‖v‖ ≤ R → ∀ i : SourceGrid U n × Fin 3,
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) → ∀ k, k ≤ d0 →
      ‖iteratedFDeriv ℝ k (fun z ↦ normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s sigma x z -
        (latticeWave a.cover a.beams hUD n i.1 i.2 x/(sigma:ℂ))*
          planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s z) v‖ ≤
        e*‖latticeWave a.cover a.beams hUD n i.1 i.2 x/(sigma:ℂ)‖ := by
  have hy := continuous_coverSourceCenter a.cover
  have hp0 t := a.nonzero_gradient _ (a.cover.center t).property
  filter_upwards [a.beams.uniform_main_coefficient_jets a.smooth_G a.positive_G
    a.smooth_A hy hp0 R hR d0 e he] with n hn
  intro x hx s hs sigma v hv i hi k hk
  have hh := hn (latticeFrame a.cover hUD n i.1,i.2) x s hs
    (by simpa only [latticeFrame_center] using hi) sigma v hv k hk
  have hxA := (a.germ x (a.centers_E hx)).2.2
  have hyG := (a.germ (scaledLatticePoint n i.1) (a.centers_E (hUD i.1.property))).1
  simpa only [latticeFrame_center,hyG.self_of_nhds,latticeWave,TripleSourceWaveData.wave,
    normalizedRescaling,rescaledSeedNormalizer,hxA.fderiv_eq] using hh

theorem lattice_main_jet_approximation (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : Coord, ‖v‖ ≤ R → ∀ k, k ≤ d0 →
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
        sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
        ‖iteratedFDeriv ℝ k (fun z ↦ normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s
          (a.latticeSigma hUD n x) x z - a.latticeAlpha hUD n x i *
          planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s z) v‖^2 ≤ e := by
  classical
  filter_upwards [a.lattice_main_coefficient_jets hUD R hR d0 (Real.sqrt e) (Real.sqrt_pos.mpr he),
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU 1 zero_lt_one] with n hn hmass
  obtain ⟨hfin,hmass⟩ := hmass
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k hk
  let I := Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
    sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ))
  have hsum : ∑ i ∈ I, ‖a.latticeAlpha hUD n x i‖^2 ≤ 1 := by
    rw [← (hmass x hx).1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ I, e*‖a.latticeAlpha hUD n x i‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := hn x (hUD (hQU hx)) s hs (a.latticeSigma hUD n x) v hv i (Finset.mem_filter.mp hi).2 k hk
      have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [mul_pow,Real.sq_sqrt he.le] at hh
      exact hh
    _ = e*(∑ i ∈ I, ‖a.latticeAlpha hUD n x i‖^2) := by rw [Finset.mul_sum]
    _ ≤ e := by nlinarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
