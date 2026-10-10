import OAI.Geometry.NodalSets.Elliptic.CompactSignEvents
import OAI.Geometry.NodalSets.Elliptic.RescaledSignTransfer
import OAI.Geometry.NodalSets.Waves.LatticeSignSubballs

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_physical_sign_subballs
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
            let scale := (n:ℝ)*sourceSignScale g S x
            let f := fun coeff y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
            let A : Set (((SourceGrid U n × Fin 3) × Fin 2) → ℝ) := {coeff |
              (∀ y : Coord, sourceEuclideanNorm (y-x) ≤ r/scale → 0 < f coeff y) ∧
              (∀ y : Coord, sourceEuclideanNorm (y-(x+scale⁻¹ • (tau • Pi.single j 1))) ≤ r/scale →
                f coeff y < 0)}
            0 < scale ∧ MeasurableSet A ∧ p ≤ gaussianPairs.real A := by
  obtain ⟨tau,ht,ht4,r,hr,hrt,hr1,p,hp0,hprob⟩ := lattice_sign_subballs_probability g hH hg hp
  refine ⟨tau,ht,ht4,r,hr,hrt,hr1,p,hp0,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  obtain ⟨c,hc,C,hC,hsigma⟩ := a.lattice_sigma_comparison hUD hU hUb hQ hQU
  filter_upwards [hprob w S S0 T0 D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hd gamma hgamma hgap,hsigma,eventually_gt_atTop (0:ℕ),a.estimates] with n hn hs hn0 hest
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',hs⟩ := hs
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  let : IsProbabilityMeasure (gaussianPairs (ι := SourceGrid U n × Fin 3)) := by
    unfold gaussianPairs; infer_instance
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := hn x hx
  have hsc : 0 < (n:ℝ)*sourceSignScale g S x := mul_pos (by exact_mod_cast hn0)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (a.source_sign_scale_lower x (hUD (hQU hx))))
  have hsig : 0 < a.latticeSigma hUD n x :=
    (mul_pos hc (Real.exp_pos _)).trans_le (hs x hx).1
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  have hmeas := seeded_gaussian_sign_balls_measurable V (oscillatorySeed S0 T0 n)
    hV (oscillatorySeed_contDiff S0 T0 hS0 hT0 n)
    x (x+((n:ℝ)*sourceSignScale g S x)⁻¹ • (tau • Pi.single j 1))
    (r/((n:ℝ)*sourceSignScale g S x)) (r/((n:ℝ)*sourceSignScale g S x))
  refine ⟨j,hsc,hmeas,hj.trans ?_⟩
  apply measureReal_mono
  · intro coeff hcoeff
    exact rescaled_sign_subballs_transfer _ S0 T0 S n (sourceSignScale g S x)
        (a.latticeSigma hUD n x) x coeff hsc hsig tau r j
        (fun v hv ↦ (hcoeff.1 v hv).2) (fun v hv ↦ (hcoeff.2 v hv).2)
  · exact measure_ne_top _ _

end
end Yau.Geometry

end OAI
