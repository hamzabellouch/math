import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientTail
import OAI.Geometry.NodalSets.Elliptic.NetDecay
import OAI.Geometry.NodalSets.Waves.LatticeCount
import OAI.Geometry.NodalSets.Waves.LatticeNetSmallBall

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section

lemma lattice_coefficient_event_failure {U : Set Coord} (hU : Bornology.IsBounded U) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ hfin : Fintype (SourceGrid U n),
      letI := hfin
      (gaussianPairs (ι := SourceGrid U n × Fin 3)) (coefficientEvent (n:ℝ))ᶜ ≤
        ENNReal.ofReal (C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) := by
  obtain ⟨C,hC,hcard⟩ := source_coefficient_card_bound hU
  refine ⟨4*C,by positivity,?_⟩
  intro n hn hfin
  let := hfin
  have h := coefficient_event_failure (ι := SourceGrid U n × Fin 3)
    (r := (n:ℝ)) (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : (Fintype.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard n hn
  nlinarith [mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-(n:ℝ)^2/8))]

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem actual_lattice_net_failure_rate (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ B > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ E : Set Coord, E ⊆ Q → ∃ t : Finset Coord,
        (↑t : Set Coord) ⊆ E ∧
        (∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ (4*(n:ℝ)^69)⁻¹ ∧
          sourceEuclideanNorm (x-y) ≤ (2*(n:ℝ)^69)⁻¹) ∧
        ∀ seed : Coord → ℝ, (∀ x ∈ Q, DifferentiableAt ℝ seed x) →
          gaussianPairs {coeff | ∃ x ∈ t,
            ‖a.latticeSeededJet hUD n hfin seed x coeff‖ ≤ 2/(n:ℝ)^56} ≤
          ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)) := by
  obtain ⟨c,hc,C,hC,hnet⟩ := a.actual_lattice_net_small_ball hUD hU hUb hQ hQU
  refine ⟨C*(24/(Real.sqrt c*Real.sqrt (2*Real.pi)))^5,by positivity,?_⟩
  filter_upwards [hnet,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro E hEQ
  obtain ⟨t,ht,_,hcover,hprob⟩ := hb E hEQ
  refine ⟨t,ht,hcover,?_⟩
  intro seed hs
  have h := hprob seed hs
  rw [net_small_ball_rate C c n hc (by positivity)] at h
  exact h

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
