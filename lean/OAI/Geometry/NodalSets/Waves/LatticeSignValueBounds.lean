import OAI.Geometry.NodalSets.Coefficients.TwoPointCoefficientEnergy
import OAI.Geometry.NodalSets.Elliptic.SignScaleSeed
import OAI.Geometry.NodalSets.Waves.LatticeTwoPointCovariance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_sign_coefficient_upper (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ v : Coord, ‖v‖ ≤ 2 →
        ∑ i : SourceGrid U n × Fin 3,
          ‖normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2)
            S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x v‖^2 ≤ 4 := by
  classical
  filter_upwards [a.lattice_full_jet_approximation hUD hU hUb hQ hQU hS 2 (by norm_num) 1 (by norm_num),
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)] with n herr hm
  obtain ⟨hfin,herr⟩ := herr
  obtain ⟨hfin',hm⟩ := hm
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv
  let W := a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x)
  let A := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
    (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x
  have hs : 1 ≤ sourceSignScale g S x := by
    linarith [a.source_sign_scale_lower x (hUD (hQU hx))]
  have herr' := herr x hx _ hs v hv (0 : Fin (k0+1))
  simp +instances only [Fin.val_zero,norm_iteratedFDeriv_zero] at herr'
  have hW : ∑ i, ‖W i v‖^2 ≤ 1 := by
    rw [← variance_pairLinearSum,← gaussianWaveField_eq_pair,a.lattice_plane_wave_variance,← (hm x hx).1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ ↦ sq_nonneg _)
  have hh (i : SourceGrid U n × Fin 3) : ‖A i v‖^2 ≤ 2*‖A i v-W i v‖^2+2*‖W i v‖^2 := by
    simpa only [sub_add_cancel] using complex_norm_add_sq_bound (A i v-W i v) (W i v)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (SourceGrid U n × Fin 3))) ↦ hh i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  change (∑ i, ‖A i v‖^2) ≤ 4
  change (∑ i, ‖A i v-W i v‖^2) ≤ 1 at herr'
  linarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
