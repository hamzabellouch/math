import OAI.Analysis.IrrationalRotation.Product.IndependentKernelProduct
import OAI.Analysis.IrrationalRotation.Couplings.OneCoordinateConditional
import OAI.Analysis.IrrationalRotation.Couplings.ProductCoupling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling KernelProduct

private lemma coordinate_right_disintegration (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.1) ⊗ₘ
      rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) =
        (coordinateLaw P i).map (fun z => (z.2.1, z.2.2)) := by
  have hleft : (coordinateLaw P i).map (fun z => z.2.1) =
      (pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)).fst := by
    rw [← coordinateLaw_map_pair P i, Measure.fst,
      Measure.map_map measurable_fst measurable_snd]
    rfl
  rw [hleft]
  simpa only [Prod.eta] using
    (rightGivenLeft_disintegration (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)).trans (coordinateLaw_map_pair P i).symm

private lemma coordinate_left_disintegration (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.2) ⊗ₘ
      leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) =
        (coordinateLaw P i).map (fun z => (z.2.2, z.2.1)) := by
  have hright : (coordinateLaw P i).map (fun z => z.2.2) =
      (pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)).snd := by
    rw [← coordinateLaw_map_pair P i, Measure.snd,
      Measure.map_map measurable_snd measurable_snd]
    rfl
  rw [hright, leftGivenRight_disintegration (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
    (P.t_nonneg i) (P.t_le i), ← coordinateLaw_map_pair P i,
    Measure.map_map measurable_swap measurable_snd]
  rfl

theorem right_condDistrib_eq_product (P : Parameters) :
    condDistrib rightEndpoint leftEndpoint (law P)
      =ᵐ[(law P).map leftEndpoint] fun x => Measure.infinitePi
        (fun i => rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (x i)) := by
  let (i : ℕ) : IsMarkovKernel
      (rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    rightGivenLeft_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  exact condDistrib_of_coordinate_disintegration (coordinateLaw P)
    (fun _ z => z.2.1) (fun _ z => z.2.2) (by fun_prop) (by fun_prop)
    (fun i => rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i))
    (coordinate_right_disintegration P)

theorem left_condDistrib_eq_product (P : Parameters) :
    condDistrib leftEndpoint rightEndpoint (law P)
      =ᵐ[(law P).map rightEndpoint] fun y => Measure.infinitePi
        (fun i => leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (y i)) := by
  let (i : ℕ) : IsMarkovKernel
      (leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    leftGivenRight_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  exact condDistrib_of_coordinate_disintegration (coordinateLaw P)
    (fun _ z => z.2.2) (fun _ z => z.2.1) (by fun_prop) (by fun_prop)
    (fun i => leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i))
    (coordinate_left_disintegration P)

theorem right_coordinates_conditionally_independent (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint,
      iIndepFun (fun i (y : Endpoint) => y i)
        (condDistrib rightEndpoint leftEndpoint (law P) x) := by
  let (i : ℕ) : IsMarkovKernel
      (rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    rightGivenLeft_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [right_condDistrib_eq_product P] with x hx
  rw [hx]
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem left_coordinates_conditionally_independent (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint,
      iIndepFun (fun i (x : Endpoint) => x i)
        (condDistrib leftEndpoint rightEndpoint (law P) y) := by
  let (i : ℕ) : IsMarkovKernel
      (leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    leftGivenRight_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [left_condDistrib_eq_product P] with y hy
  rw [hy]
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem right_condDistrib_coordinate_law (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ i,
      (condDistrib rightEndpoint leftEndpoint (law P) x).map
        (fun y : Endpoint => y i) =
      rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (x i) := by
  let (i : ℕ) : IsMarkovKernel
      (rightGivenLeft (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    rightGivenLeft_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [right_condDistrib_eq_product P] with x hx i
  rw [hx, Measure.infinitePi_map_eval]

theorem left_condDistrib_coordinate_law (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ i,
      (condDistrib leftEndpoint rightEndpoint (law P) y).map
        (fun x : Endpoint => x i) =
      leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (y i) := by
  let (i : ℕ) : IsMarkovKernel
      (leftGivenRight (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
    leftGivenRight_isMarkov (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
      (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  filter_upwards [left_condDistrib_eq_product P] with y hy i
  rw [hy, Measure.infinitePi_map_eval]

theorem ae_leftEndpoint_mem_unit (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
  apply (ae_map_iff leftEndpoint_measurable.aemeasurable (by measurability)).mpr
  apply ae_all_iff.mpr
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.1 ∈ Set.Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_fst.comp measurable_snd).aemeasurable)
    simp only [Function.comp_def]
    rw [coordinateLaw_map_left P i]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

theorem ae_rightEndpoint_mem_unit (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ i, y i ∈ Set.Ico (0 : ℝ) 1 := by
  apply (ae_map_iff rightEndpoint_measurable.aemeasurable (by measurability)).mpr
  apply ae_all_iff.mpr
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.2 ∈ Set.Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_snd.comp measurable_snd).aemeasurable)
    simp only [Function.comp_def]
    rw [coordinateLaw_map_right P i]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

end Invariant233.OrderedProductCoupling

end

end OAI
