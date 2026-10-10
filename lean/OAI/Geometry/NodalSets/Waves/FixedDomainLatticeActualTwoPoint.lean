import OAI.Geometry.NodalSets.Coefficients.TwoPointCoefficientEnergy
import OAI.Geometry.NodalSets.Waves.FixedDomainLatticeTwoPointGap
import OAI.Geometry.NodalSets.Waves.LatticeActualTwoPoint

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_actual_two_point_energy_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ delta > 0,
      ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U → ContDiff ℝ ∞ S →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4, ∀ u v : ℝ,
            let coeff := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
              (latticeWave a.cover a.beams hUD n i.1 i.2) S n
              (sourceSignScale g S x) (a.latticeSigma hUD n x) x
            delta*(u^2+v^2) ≤ ∑ i,
              ‖(u:ℂ)*coeff i 0+(v:ℂ)*coeff i (tau • Pi.single j 1)‖^2 := by
  obtain ⟨tau,ht,ht4,d,hd,hgaps⟩ := lattice_plane_wave_two_point_gap_fixed_domain g hH hg hp
  refine ⟨tau,ht,ht4,d/4,by positivity,?_⟩
  intro w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS
  filter_upwards [hgaps w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU,
    a.lattice_full_jet_approximation hUD hU hUb hQ hQU hS 2 (by norm_num) (d/8) (by positivity)]
    with n hgap herr
  obtain ⟨hfin,hgap⟩ := hgap
  obtain ⟨hfin',herr⟩ := herr
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hM,hM1,hW,hC0,hC⟩ := hgap x hx
  dsimp only at hM hM1 hW hC0 hC
  let W := a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x)
  let A := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
    (latticeWave a.cover a.beams hUD n i.1 i.2) S n
    (sourceSignScale g S x) (a.latticeSigma hUD n x) x
  have hgap' : ∀ u v : ℝ, d*(u^2+v^2) ≤
      ∑ i, ‖(u:ℂ)*W i 0+(v:ℂ)*W i (tau • Pi.single j 1)‖^2 := by
    intro u v
    apply two_point_energy_of_gap _ _ _ _ d rfl _ rfl _ _ u v
    · simpa only [gaussianWaveField_eq_pair] using hW
    · have hm0 := variance_nonneg (fun coeff ↦ gaussianWaveField W coeff 0) gaussianPairs
      rw [gaussianWaveField_eq_pair] at hm0
      simp only [gaussianWaveField_eq_pair] at hC0
      linarith
    · simpa only [gaussianWaveField_eq_pair] using hC
  have hs : 1 ≤ sourceSignScale g S x := by
    linarith [a.source_sign_scale_lower x (hUD (hQU hx))]
  have hnorm : ‖(tau • Pi.single j (1:ℝ) : Coord)‖ ≤ 2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,Pi.norm_single,norm_one,mul_one]
    linarith
  have he0 := herr x hx _ hs 0 (by simp) (0 : Fin (k0+1))
  have he1 := herr x hx _ hs _ hnorm (0 : Fin (k0+1))
  simp +instances only [Fin.val_zero,norm_iteratedFDeriv_zero] at he0 he1
  refine ⟨j,?_⟩
  intro u v
  have hh := two_point_energy_perturbation (fun i ↦ W i 0) (fun i ↦ W i (tau • Pi.single j 1))
    (fun i ↦ A i 0) (fun i ↦ A i (tau • Pi.single j 1)) d (d/8) he0 he1 hgap' u v
  convert hh using 1; ring

end
end Yau.Geometry

end OAI
