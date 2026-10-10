import OAI.Geometry.NodalSets.Elliptic.SpatialNet
import OAI.Geometry.NodalSets.Waves.LatticeGaussianSmallBall
import OAI.Geometry.NodalSets.Waves.NetProbability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma measurable_latticeSeededJet (hUD : U ⊆ D) (n : ℕ)
    (hfin : Fintype (SourceGrid U n)) (seed : Coord → ℝ) (x : Coord)
    (hs : DifferentiableAt ℝ seed x)
    (hV : ∀ z j, DifferentiableAt ℝ (latticeWave a.cover a.beams hUD n z j) x) :
    Measurable (a.latticeSeededJet hUD n hfin seed x) := by
  let := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have he : a.latticeSeededJet hUD n hfin seed x = fun coeff ↦
      normalizedRealJet seed n (S x) x +
        pairJetMap (jetWaveCoefficients V n (S x) x) (WithLp.toLp 2 coeff) := by
    funext coeff
    exact seeded_gaussian_jet_eq V seed n (S x) x (fun i ↦ hV i.1 i.2) hs coeff
  rw [he]
  fun_prop

theorem actual_lattice_net_small_ball (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ E : Set Coord, E ⊆ Q → ∃ t : Finset Coord,
        (↑t : Set Coord) ⊆ E ∧ (t.card : ℝ) ≤ C*(n:ℝ)^276 ∧
        (∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ (4*(n:ℝ)^69)⁻¹ ∧
          sourceEuclideanNorm (x-y) ≤ (2*(n:ℝ)^69)⁻¹) ∧
        ∀ seed : Coord → ℝ, (∀ x ∈ Q, DifferentiableAt ℝ seed x) →
          gaussianPairs {coeff | ∃ x ∈ t,
            ‖a.latticeSeededJet hUD n hfin seed x coeff‖ ≤ 2/(n:ℝ)^56} ≤
          ENNReal.ofReal (C*(n:ℝ)^276*
            (12*(Real.sqrt (c/(n:ℝ)))⁻¹*(2/(n:ℝ)^56)/Real.sqrt (2*Real.pi))^5) := by
  obtain ⟨c,hc,hsmall⟩ := a.actual_lattice_gaussian_small_ball hUD hU hUb hQ hQU
  obtain ⟨C,hC,hnet⟩ := jet_scale_internal_net hQ.isBounded
  refine ⟨c,hc,C,hC,?_⟩
  filter_upwards [hsmall,lattice_wave_estimates a.cover a.beams hUD,
    eventually_gt_atTop (0:ℕ)] with n hn hw hnpos
  obtain ⟨hfin,hp⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro E hEQ
  obtain ⟨t,ht,hcard,hcover⟩ := hnet n hnpos E hEQ
  refine ⟨t,ht,hcard,hcover,?_⟩
  intro seed hs
  let b := (12*(Real.sqrt (c/(n:ℝ)))⁻¹*(2/(n:ℝ)^56)/Real.sqrt (2*Real.pi))^5
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hp' (x : Coord) (hx : x ∈ t) :
      gaussianPairs {coeff | ‖a.latticeSeededJet hUD n hfin seed x coeff‖ ≤ 2/(n:ℝ)^56} ≤
        ENNReal.ofReal b := by
    have hxQ := hEQ (ht hx)
    have h := hp seed x hxQ (hs x hxQ) (2/(n:ℝ)^56) (by positivity)
    rw [Measure.map_apply (a.measurable_latticeSeededJet hUD n hfin seed x (hs x hxQ)
      (fun z j ↦ ((hw z j).1.differentiable (by simp)).differentiableAt))
      (measurableSet_le (by fun_prop) measurable_const)] at h
    exact h
  have hu := finite_small_ball_union gaussianPairs t
    (fun coeff x ↦ a.latticeSeededJet hUD n hfin seed x coeff)
    (2/(n:ℝ)^56) (ENNReal.ofReal b) hp'
  refine hu.trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact_mod_cast (ENNReal.ofReal_le_ofReal hcard)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
