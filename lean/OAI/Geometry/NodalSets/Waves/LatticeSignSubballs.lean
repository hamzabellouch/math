import OAI.Geometry.NodalSets.Waves.LatticeGradientExpectation
import OAI.Geometry.NodalSets.Waves.LatticeSignMargin
import OAI.Geometry.NodalSets.Waves.SignSubballProbability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_sign_subballs_probability
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ r : ℝ, 0 < r ∧
      r < tau/4 ∧ r < (1-tau)/2 ∧ ∃ p : ℝ, 0 < p ∧
      ∀ (w S S0 T0 : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : H ⊆ D) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let F := rescaledGaussianField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
              S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
            p ≤ gaussianPairs.real {coeff |
              (∀ v : Coord, sourceEuclideanNorm v ≤ r →
                sourceEuclideanNorm v ≤ 1 ∧ 0 < F coeff v) ∧
              (∀ v : Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
                sourceEuclideanNorm v ≤ 1 ∧ F coeff v < 0)} := by
  obtain ⟨tau,ht,ht4,p,hp0,hmargin⟩ := lattice_sign_margin_probability g hH hg hp
  obtain ⟨q,hq,hq1,hqp⟩ := positive_real_probability_floor hp0
  obtain ⟨C,hC,hmean⟩ := lattice_gradient_expectation g hH hg hp
  obtain ⟨L,hL,r,hr,hrt,hr1,hrL,hCL⟩ := sign_subball_constants ht (by linarith) hq hC.le
  refine ⟨tau,ht,ht4,r,hr,hrt,hr1,q/2,by positivity,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  filter_upwards [hmargin w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU
    hS hS0 hT0 gamma hgamma hgap,
    hmean w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hd gamma hgamma hgap,a.estimates] with n hn hm hest
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',hm⟩ := hm
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  let : IsProbabilityMeasure (gaussianPairs (ι := SourceGrid U n × Fin 3)) := by
    unfold gaussianPairs; infer_instance
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := hn x hx
  obtain ⟨G,hGc,hGi,hG0,hGC,hGe⟩ := hm x hx
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  let F := rescaledGaussianField V S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  have hF (coeff) : ContDiff ℝ ∞ (F coeff) := by
    have he : F coeff = fun z ↦ rescaledSeed S0 T0 S n (sourceSignScale g S x)
        (a.latticeSigma hUD n x) x z + gaussianWaveField
          (fun i ↦ normalizedRescaling (V i) S n (sourceSignScale g S x)
            (a.latticeSigma hUD n x) x) coeff z := by
      ext z
      exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
    rw [he]
    exact (rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _).add
      (gaussianWaveField_contDiff _ _ (fun i ↦ normalizedRescaling_smooth _ (hV i) _ _ _ _ _))
  have hqA : q ≤ gaussianPairs.real {coeff | 1 ≤ F coeff 0 ∧ F coeff (tau • Pi.single j 1) ≤ -1} := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (hqp.trans hj)
    simpa only [ENNReal.toReal_ofReal hq.le,Measure.real] using hh
  refine ⟨j,?_⟩
  exact sign_subballs_probability gaussianPairs F hF G hGi hG0 ht.le hr.le hL
    (by linarith) hrL hGC hCL (fun coeff hcoeff ↦ (hGe coeff L hL.le).mp hcoeff) j hqA

end
end Yau.Geometry

end OAI
