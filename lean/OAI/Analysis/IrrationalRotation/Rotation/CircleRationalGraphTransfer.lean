import OAI.Analysis.IrrationalRotation.Model.CircleRationalGraphs
import OAI.Analysis.IrrationalRotation.Rotation.CircleRationalGraphCaps
import OAI.Analysis.IrrationalRotation.Operators.OperatorCompactTransfer
import OAI.Analysis.IrrationalRotation.Analysis.CountableGraphTransfer
import OAI.Analysis.IrrationalRotation.Analysis.UniformAbsoluteContinuity

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem rational_graph_measure_ratio_cap (A : ℕ) (hA : 1 ≤ A) (r k : ℤ) :
    ∀ᵐ z ∂(circleTranslationGraph (p.rationalTranslation A r) : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ p.rationalRatioBound A := by
  change ∀ᵐ z ∂circleMeasure.map (fun x => (x, x + p.rationalTranslation A r)), _
  apply (ae_map_iff (measurable_id.prodMk
    (measurable_id.add measurable_const)).aemeasurable ?_).mpr
  · filter_upwards [hp.ae_rational_graph_ratio_cap] with x hx
    exact hx A hA r k
  · exact measurableSet_le
      ((hp.measurable_parameter_cocycle k).comp measurable_snd |>.div
        ((hp.measurable_parameter_cocycle k).comp measurable_fst)) measurable_const

theorem rational_graph_identity_of_approximants
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ x, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (A : ℕ) (hA : 1 ≤ A) (r : ℤ)
    (ν : ℕ → FiniteMeasure (Circle × Circle))
    (hν : Tendsto ν atTop (𝓝 (circleTranslationGraph (p.rationalTranslation A r))))
    (hfirst : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.snd))
    (hcap : ∀ j k, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ p.rationalRatioBound A)
    (hzero : ∀ j, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      (1 - P z.2).comp ((ratioDiagonal (p.floorCocycle θ) z).comp (P z.1)) = 0) :
    ∀ᵐ x ∂circleMeasure,
      (1 - P (x + p.rationalTranslation A r)) *
        ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0 := by
  let : IsFiniteMeasure circleMeasure := by
    change IsFiniteMeasure (volume : Measure Circle)
    infer_instance
  have hlim := CompactTransfer.compact_operator_transfer circleMeasure P hP
    (p.floorCocycle θ) (fun k x => p.floorCocycle_pos θ k x)
    hp.measurable_parameter_cocycle hPm hν hfirst hsecond
    (p.rationalRatioBound A) (Real.exp_pos _)
    hcap (fun k => hp.rational_graph_measure_ratio_cap A hA r k) hzero
  have h := ae_of_ae_map
    (measurable_id.prodMk (measurable_id.add measurable_const)).aemeasurable hlim
  filter_upwards [h] with x hx
  exact hx

theorem rational_graph_identity_of_orbit_approximants
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ x, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂circleMeasure,
      (1 - P (CircleWeights.rotate θ (n : ℤ) x)).comp
        ((ratioDiagonal (p.floorCocycle θ)
          (x, CircleWeights.rotate θ (n : ℤ) x)).comp (P x)) = 0)
    (A : ℕ) (hA : 1 ≤ A) (r : ℤ)
    (ν : ℕ → FiniteMeasure (Circle × Circle))
    (hν : Tendsto ν atTop (𝓝 (circleTranslationGraph (p.rationalTranslation A r))))
    (hfirst : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.snd))
    (hcap : ∀ j k, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ p.rationalRatioBound A)
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      ∃ n : ℕ, 0 < n ∧ z.2 = CircleWeights.rotate θ (n : ℤ) z.1) :
    ∀ᵐ x ∂circleMeasure,
      (1 - P (x + p.rationalTranslation A r)) *
        ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0 := by
  apply hp.rational_graph_identity_of_approximants P hP hPm A hA r ν hν hfirst hsecond hcap
  intro j
  apply Fields.ae_pair_relation_of_countable_graphs
    (fun x y => (1 - P y).comp ((ratioDiagonal (p.floorCocycle θ) (x, y)).comp (P x)) = 0)
    (fun n : ℕ+ => CircleWeights.rotate θ (n : ℤ))
    (hfirst.absolutelyContinuous j)
  · intro n
    exact horbit n n.property
  · filter_upwards [hsupport j] with z hz
    obtain ⟨n, hn, he⟩ := hz
    exact ⟨⟨n, hn⟩, he⟩

omit hp in
theorem rationalGraphIdentities_of_forall (_hp : CircleParameterLaws θ p)
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (h : ∀ A : ℕ, 1 ≤ A → ∀ r : ℤ, ∀ᵐ x ∂circleMeasure,
      (1 - P (x + p.rationalTranslation A r)) *
        ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0) :
    p.RationalGraphIdentities θ P := by
  apply ae_all_iff.mpr
  intro A
  by_cases hA : 1 ≤ A
  · filter_upwards [ae_all_iff.mpr (h A hA)] with x hx
    exact fun _ => hx
  · exact Filter.Eventually.of_forall fun _ hAx => (hA hAx).elim

end Invariant233.CircleParameterLaws

end

end OAI
