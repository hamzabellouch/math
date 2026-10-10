import OAI.Geometry.NodalSets.Elliptic.SignScaleSeed
import OAI.Geometry.NodalSets.Waves.LatticeActualTwoPoint
import OAI.Geometry.NodalSets.Waves.LatticeSignValueBounds
import OAI.Geometry.NodalSets.Waves.TwoValueSignProbability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section

theorem lattice_sign_margin_probability
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ p : ℝ≥0∞, 0 < p ∧
      ∀ (w S S0 T0 : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : H ⊆ D) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let F := rescaledGaussianField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
              S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
            p ≤ gaussianPairs {coeff | 1 ≤ F coeff 0 ∧ F coeff (tau • Pi.single j 1) ≤ -1} := by
  obtain ⟨tau,ht,ht4,d,hd,henergy⟩ := lattice_actual_two_point_energy g hH hg hp
  obtain ⟨p,hp,hprob⟩ := two_value_sign_probability d 2 hd (by norm_num)
  refine ⟨tau,ht,ht4,p,hp,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS hS0 hT0 gamma hgamma hgap
  filter_upwards [henergy w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS,
    a.lattice_sign_coefficient_upper hUD hU hUb hQ hQU hS,
    a.sign_scale_seed_decay hUD hU hUb hQ hQU hS S0 T0 hS0 hT0 gamma hgamma hgap 0 1 (by norm_num)]
    with n he hu hs
  obtain ⟨hfin,he⟩ := he
  obtain ⟨hfin',hu⟩ := hu
  obtain ⟨hfin'',hs⟩ := hs
  have heq : hfin' = hfin := Subsingleton.elim _ _
  have heq' : hfin'' = hfin := Subsingleton.elim _ _
  subst hfin'
  subst hfin''
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := he x hx
  let v : Coord := tau • Pi.single j 1
  let seed := rescaledSeed S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
  let A := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
    (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x
  let mean : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![seed 0,seed v]
  have hvnorm : ‖v‖ = tau := by
    simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos ht,Pi.norm_single]
  have hv : sourceEuclideanNorm v ≤ 2 := (sourceEuclideanNorm_le v).trans (by rw [hvnorm]; linarith)
  have hv0 : sourceEuclideanNorm (0:Coord) ≤ 2 := by simp [sourceEuclideanNorm]
  have hs0 := hs x hx 0 hv0 (0 : Fin 1)
  have hs1 := hs x hx v hv (0 : Fin 1)
  simp only [Fin.val_zero,norm_iteratedFDeriv_zero] at hs0 hs1
  change ‖seed 0‖ ≤ 1 at hs0
  change ‖seed v‖ ≤ 1 at hs1
  have hmean : ‖mean‖ ≤ 2 := by
    have hsq : ‖mean‖^2 = (seed 0)^2+(seed v)^2 := by
      simp [mean,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    have h0 := pow_le_pow_left₀ (norm_nonneg _) hs0 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hs1 2
    simp only [Real.norm_eq_abs,sq_abs,one_pow] at h0 h1
    nlinarith [norm_nonneg mean]
  have hb := hprob (fun i ↦ A i 0) (fun i ↦ A i v) mean hmean
    (hu x hx 0 (by simp)) (hu x hx v (by rw [hvnorm]; linarith)) hj
  refine ⟨j,?_⟩
  convert hb using 1
  congr 1
  ext coeff
  simp [rescaledGaussianField_decomposition,mean,seed,A,v,
    pairLinearSum_eq_complex,gaussianWaveField,Complex.re_sum]

end
end Yau.Geometry

end OAI
