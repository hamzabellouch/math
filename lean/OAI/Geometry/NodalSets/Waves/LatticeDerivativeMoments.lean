import OAI.Geometry.NodalSets.Elliptic.SignScaleSeed
import OAI.Geometry.NodalSets.Waves.LatticeActualDerivativeEnergy

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_derivative_second_moments
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S S0 T0 : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0) (_ : H ⊆ D) (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → d ≤ k0 →
      ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : ℕ, k ≤ d →
        ∀ dirs : Fin k → Coord, ‖dirs‖ ≤ 1 →
        let F := rescaledGaussianField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
          S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
        MemLp (fun coeff ↦ iteratedFDeriv ℝ k (F coeff) v dirs) 2 gaussianPairs ∧
        (∫ coeff, (iteratedFDeriv ℝ k (F coeff) v dirs)^2 ∂gaussianPairs) ≤ C := by
  obtain ⟨C,hC,henergy⟩ := lattice_actual_derivative_energy g hH hg hp d
  refine ⟨1+C,by positivity,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  filter_upwards [henergy w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS hd,
    a.sign_scale_seed_decay hUD hU hUb hQ hQU hS S0 T0 hS0 hT0 gamma hgamma hgap d 1 (by norm_num),
    a.estimates] with n he hs hest
  obtain ⟨hfin,he⟩ := he
  obtain ⟨hfin',hs⟩ := hs
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv k hk dirs hdirs
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  refine ⟨rescaledGaussianField_derivative_memLp V hV _ _ _ hS0 hT0 _ _ _ _ _ _ _,?_⟩
  rw [rescaledGaussianField_derivative_moment V hV _ _ _ hS0 hT0]
  have hseed := hs x hx v hv (⟨k,by omega⟩ : Fin (d+1))
  have hseed' := (iteratedFDeriv ℝ k
    (rescaledSeed S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x) v).unit_le_opNorm hdirs
  have hmean := pow_le_pow_left₀ (norm_nonneg _) (hseed'.trans hseed) 2
  simp only [Real.norm_eq_abs,sq_abs,one_pow] at hmean
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (SourceGrid U n × Fin 3))) ↦
    pow_le_pow_left₀ (norm_nonneg _)
      ((iteratedFDeriv ℝ k (normalizedRescaling (V i) S n (sourceSignScale g S x)
        (a.latticeSigma hUD n x) x) v).unit_le_opNorm hdirs) 2)
  have hbound := he x hx v ((norm_le_sourceEuclideanNorm v).trans hv) k hk
  change (∑ i, ‖iteratedFDeriv ℝ k (normalizedRescaling (V i) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x) v‖^2) ≤ C at hbound
  linarith

end
end Yau.Geometry

end OAI
