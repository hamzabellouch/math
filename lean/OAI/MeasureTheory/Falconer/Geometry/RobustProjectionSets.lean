import OAI.MeasureTheory.Falconer.Estimates.ProjectedSubsetRegularity
import OAI.MeasureTheory.Falconer.Geometry.FiniteWeightedProjectionSample
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! A good original direction works for every later large point subset.
The output is an actual separated projected set, with original witnesses,
explicit regularity cost and a quantitative cardinality lower bound. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def projectedSubsetSampleConstant
    (N : ℕ) (s t KI KP ρ : ℝ) : ℝ :=
  let C := (2*(2*projectionEnergyBudget N s t KI KP)/ρ)*(2/ρ)*(2:ℝ)^s
  let γ := (1/(2:ℝ)^N)/4
  2*(2*(((Real.exp 1-1)*(C*(4:ℝ)^s)+(1-10*Real.log γ))*(8:ℝ)^s))^2

theorem robust_projection_subset (N : ℕ) {s t KI KP c ρ : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP)
    (hc : |c| ≤ 1) (hρ : 0 < ρ)
    (P A : Finset (Space 2)) (hP : P.Nonempty) (hchart : InBoundedLineChart P)
    (hAP : A ⊆ P) (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (henergy : planarProjectionEnergy N s c P ≤
      2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2) :
    let γ := (1/(2:ℝ)^N)/4
    let K := projectedSubsetSampleConstant N s t KI KP ρ
    ∃ Q : Finset (Space 2), Q.Nonempty ∧
      Q ⊆ A.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) ∧
      FiniteSeparatedAt γ Q ∧ NormalizedFiniteBallBound γ s K Q ∧
      1 ≤ K*γ^s*(Q.card:ℝ) ∧ Q.card ≤ Nat.ceil (γ^(-s)) ∧
      ∀ x ∈ Q, x 0 = 0 ∧ |x 1| ≤ 1/2 := by
  dsimp only
  have hbudget := projectionEnergyBudget_pos N hst hKI hKP
  obtain ⟨S,hSA,hS,_,hball⟩ := projected_subset_weighted_regular N hs
    (mul_pos (by norm_num) hbudget) hρ P A hP hAP hsize henergy
  let C := (2*(2*projectionEnergyBudget N s t KI KP)/ρ)*(2/ρ)*(2:ℝ)^s
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδ1 : 1/(2:ℝ)^N ≤ 1 := by
    exact (div_le_one (by positivity : (0:ℝ) < (2:ℝ)^N)).2
      (one_le_pow₀ (by norm_num))
  obtain ⟨Q,hQ,hQS,hsep,hreg,hcard⟩ := finite_weighted_projection_sample hδ hδ1 hs
    (show 0 ≤ C by dsimp [C]; positivity) hc S hS
    (fun x hx => hchart x (hAP (hSA hx))) hball
  have hQA : Q ⊆ A.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) :=
    hQS.trans (Finset.image_subset_image hSA)
  have hreg' : NormalizedFiniteBallBound ((1/(2:ℝ)^N)/4) s
      (projectedSubsetSampleConstant N s t KI KP ρ) Q := hreg
  refine ⟨Q,hQ,hQA,hsep,hreg',finite_ball_bound_card_lower
    (by positivity) (by linarith only [hδ1]) hQ hreg',hcard,?_⟩
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hQA hx)
  have hpchart := hchart p (hAP hp)
  have hproj : |lineParameterProjection c p| ≤ 2 := by
    have hm := mul_le_mul hc hpchart.1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    rw [← abs_mul] at hm
    unfold lineParameterProjection
    exact (abs_add_le _ _).trans (by linarith only [hm,hpchart.2])
  refine ⟨rfl,?_⟩
  simp only [rowPoint_one,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
  linarith only [hproj]

theorem robust_projection_directions (N : ℕ) {s t KI KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 1 ≤ KI) (hKP : 1 ≤ KP)
    (I : Finset ℝ) (P : Finset (Space 2)) (hPne : P.Nonempty)
    (hI : ∀ c ∈ I, |c| ≤ 1) (hP : InBoundedLineChart P)
    (hIball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ KI*r^s*(I.card:ℝ))
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    ∃ J ⊆ I, (I.card:ℝ)/2 ≤ (J.card:ℝ) ∧
      ∀ c ∈ J, ∀ (ρ : ℝ), 0 < ρ → ∀ A : Finset (Space 2), A ⊆ P →
        ρ*(P.card:ℝ) ≤ (A.card:ℝ) →
      let γ := (1/(2:ℝ)^N)/4
      let K := projectedSubsetSampleConstant N s t KI KP ρ
      ∃ Q : Finset (Space 2), Q.Nonempty ∧
        Q ⊆ A.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) ∧
        FiniteSeparatedAt γ Q ∧ NormalizedFiniteBallBound γ s K Q ∧
        1 ≤ K*γ^s*(Q.card:ℝ) ∧ Q.card ≤ Nat.ceil (γ^(-s)) ∧
        ∀ x ∈ Q, x 0 = 0 ∧ |x 1| ≤ 1/2 := by
  obtain ⟨J,hJI,hJ,henergy⟩ := good_projection_directions N hs hst hKI hKP I P
    hPne hI hP hIball hPball
  refine ⟨J,hJI,hJ,?_⟩
  intro c hc ρ hρ A hAP hsize
  exact robust_projection_subset N hs hst (zero_le_one.trans hKI) (zero_le_one.trans hKP)
    (hI c (hJI hc)) hρ P A hPne hP hAP hsize (henergy c hc)

end Falconer

end OAI
