import OAI.Geometry.NodalSets.Waves.EuclideanGaussianSmallBall
import OAI.Geometry.NodalSets.Waves.GaussianJet
import OAI.Geometry.NodalSets.Waves.LatticeCovariance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal RealInnerProductSpace
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeSeededJet (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : Coord → ℝ) (x : Coord)
    (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) : JetSpace :=
  letI := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  normalizedRealJet (fun z ↦ seed z+gaussianWaveField V coeff z) (n:ℝ) (S x) x

lemma latticeSeededJet_inner (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : Coord → ℝ) (x : Coord) (v : JetSpace)
    (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) :
    ⟪v,a.latticeSeededJet hUD n hfin seed x coeff⟫ =
      a.latticeSeededRandomDual hUD n hfin seed x (v 0) (Fin.tail (WithLp.ofLp v)) coeff := by
  let := hfin
  unfold latticeSeededJet latticeSeededRandomDual
  exact normalizedRealJet_inner
    (fun z ↦ seed z + gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
      coeff z) (n : ℝ) (S x) x v

theorem actual_lattice_gaussian_small_ball (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ (seed : Coord → ℝ) (x : Coord), x ∈ Q → DifferentiableAt ℝ seed x →
      ∀ r : ℝ, 0 ≤ r →
        (gaussianPairs.map (a.latticeSeededJet hUD n hfin seed x)) {y | ‖y‖ ≤ r} ≤
          ENNReal.ofReal ((12*(Real.sqrt (c/(n:ℝ)))⁻¹*r/Real.sqrt (2*Real.pi))^5) := by
  obtain ⟨c,hc,hcov⟩ := a.actual_lattice_covariance_lower_bound hUD hU hUb hQ hQU
  refine ⟨c,hc,?_⟩
  filter_upwards [hcov,lattice_wave_estimates a.cover a.beams hUD,
    eventually_gt_atTop (0:ℕ)] with n hn hw hnpos
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro seed x hx hs r hr
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV : ∀ i, DifferentiableAt ℝ (V i) x := fun i ↦
    ((hw i.1 i.2).1.differentiable (by simp)).differentiableAt
  have hb (v : JetSpace) : c/(n:ℝ)*‖v‖^2 ≤
      ‖(pairJetMap (jetWaveCoefficients V n (S x) x)).adjoint v‖^2 := by
    have h := hbound seed x hx hs (v 0) (Fin.tail (WithLp.ofLp v))
    have he : (fun coeff ↦ ⟪v,a.latticeSeededJet hUD n hfin seed x coeff⟫) =
        a.latticeSeededRandomDual hUD n hfin seed x (v 0) (Fin.tail (WithLp.ofLp v)) := by
      funext coeff
      exact a.latticeSeededJet_inner hUD n hfin seed x v coeff
    rw [← he] at h
    change c/(n:ℝ)*((v 0)^2+∑ i : Fin 4, (v i.succ)^2) ≤
      Var[fun coeff ↦ ⟪v,normalizedRealJet (fun y ↦ seed y+gaussianWaveField V coeff y)
        (n:ℝ) (S x) x⟫; gaussianPairs] at h
    rw [seeded_gaussian_jet_variance V seed n (S x) x hV hs v] at h
    simpa only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ] using h
  have hl := seeded_gaussian_jet_law V seed n (S x) x hV hs
  change gaussianPairs.map (a.latticeSeededJet hUD n hfin seed x) = _ at hl
  rw [hl]
  have h := gaussian_map_small_ball (pairJetMap (jetWaveCoefficients V n (S x) x))
    (normalizedRealJet seed n (S x) x) (c/(n:ℝ)) r (by positivity) hr hb
  convert h using 1
  norm_num
  congr 2
  ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
