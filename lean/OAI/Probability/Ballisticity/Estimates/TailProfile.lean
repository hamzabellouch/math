import Mathlib
import OAI.Probability.Ballisticity.Walk.ProfileGrowth2

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]
    [MeasurableSingletonClass X]

theorem measurable_profile_cuts (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) :
    ∃ j : ℕ → D → ℤ, (∀ r, Measurable (j r)) ∧
      (∀ d (r : ℕ) (k : ℤ), TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) k ≤
        TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) (j r d)) ∧
      (∀ d, Tendsto (fun r => j r d) atTop atBot ∧
        Tendsto (fun r => j r d + (r : ℤ)) atTop atTop) := by
  have hpos : ∀ d z, 0 < ((w d).map ξ).real {z} :=
    fun d => coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)
  have hL : ∀ n, Measurable (fun d => TailCuts.lower ((w d).map ξ) n) := by
    intro n
    have hh := ((w.map ξ).measurable_coe (s := Set.Iic n) measurableSet_Iic).ennreal_toReal
    simpa only [TailCuts.lower, Measure.real, Kernel.map_apply _ hξ] using hh
  have hU : ∀ n, Measurable (fun d => TailCuts.upper ((w d).map ξ) n) := by
    intro n
    have hh := ((w.map ξ).measurable_coe (s := Set.Ici n) measurableSet_Ici).ennreal_toReal
    simpa only [TailCuts.upper, Measure.real, Kernel.map_apply _ hξ] using hh
  have hex : ∀ r : ℕ, ∃ j : D → ℤ, Measurable j ∧
      ∀ d k, TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) k ≤
        TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) (j d) := by
    intro r
    exact TailCuts.measurable_maximizing_cut _ _ (r : ℤ) hL hU
      (fun d => (TailCuts.finite_profile_cuts_escape ((w d).map ξ) (hpos d)).1 _)
  choose j hj hmax using hex
  refine ⟨j,hj,fun d r => hmax r d,fun d => ?_⟩
  exact (TailCuts.finite_profile_cuts_escape ((w d).map ξ) (hpos d)).2
    (fun r => j r d) (fun r k => hmax r d k)

noncomputable def lowerKernel (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) : Kernel D X :=
  cutKernel w (fun n => ξ ⁻¹' Set.Iic n) (fun _ => hξ measurableSet_Iic) j hj

noncomputable def upperKernel (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) : Kernel D X :=
  cutKernel w (fun n => ξ ⁻¹' Set.Ici n) (fun _ => hξ measurableSet_Ici) j hj

lemma lowerKernel_markov (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (lowerKernel w ξ hξ j hj) := by
  apply cutKernel_markov
  · intro d
    have ht := TailCuts.lower_pos ((w d).map ξ)
      (coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)) (j d)
    rw [TailCuts.lower, Measure.real, Measure.map_apply hξ measurableSet_Iic] at ht
    exact (ENNReal.toReal_pos_iff.mp ht).1.ne'
  · exact fun d => measure_ne_top _ _

lemma upperKernel_markov (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (upperKernel w ξ hξ j hj) := by
  apply cutKernel_markov
  · intro d
    have ht := TailCuts.upper_pos ((w d).map ξ)
      (coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)) (j d)
    rw [TailCuts.upper, Measure.real, Measure.map_apply hξ measurableSet_Ici] at ht
    exact (ENNReal.toReal_pos_iff.mp ht).1.ne'
  · exact fun d => measure_ne_top _ _

omit [MeasurableSingletonClass X] in
lemma lowerKernel_supported [MeasurableSingletonClass X]
    (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) (d : D) :
    ∀ᵐ x ∂lowerKernel w ξ hξ j hj d, ξ x ≤ j d :=
  cutKernel_supported _ _ _ _ _ _

omit [MeasurableSingletonClass X] in
lemma upperKernel_supported [MeasurableSingletonClass X]
    (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) (d : D) :
    ∀ᵐ x ∂upperKernel w ξ hξ j hj d, j d ≤ ξ x :=
  cutKernel_supported _ _ _ _ _ _

end TailSampling

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

abbrev ZeroHeightPair {d : ℕ} (e : Direction d) :=
  {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}

def horizontalPair {d : ℕ} (e : Direction d)
    (p : HorizontalLayer e × HorizontalLayer e) : ZeroHeightPair e :=
  ⟨(p.1.1,p.2.1), by
    simp only [PairAtHeight, Set.mem_ofPred, dot_signed_direction, signedCoordinate,
      p.1.2, p.2.2, Int.cast_zero, neg_zero, ite_self, and_self]⟩

noncomputable def profilePairKernel {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e))
    (R : ℤ) (j : D → ℤ) (hj : Measurable j) : Kernel D (ZeroHeightPair e) :=
  ((TailSampling.lowerKernel w (fun x => x.1 f) (measurable_of_countable _) j hj).prod
    (TailSampling.upperKernel w (fun x => x.1 f) (measurable_of_countable _)
      (fun z => j z+R) (hj.add_const R))).map (horizontalPair e)

lemma profilePairKernel_markov {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (profilePairKernel e f w R j hj) := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  unfold profilePairKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

lemma profilePairKernel_supported {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) (z : D) :
    ∀ᵐ p ∂profilePairKernel e f w R j hj z,
      p.1.1 f ≤ j z ∧ j z+R ≤ p.1.2 f := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  rw [profilePairKernel, Kernel.map_apply _ (measurable_of_countable _), Kernel.prod_apply]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    ((Set.to_countable _).measurableSet)).mpr
  apply (Measure.ae_prod_iff_ae_ae ((Set.to_countable _).measurableSet)).mpr
  filter_upwards [TailSampling.lowerKernel_supported w (fun x => x.1 f)
    (measurable_of_countable _) j hj z] with x hx
  filter_upwards [TailSampling.upperKernel_supported w (fun x => x.1 f)
    (measurable_of_countable _) (fun z => j z+R) (hj.add_const R) z] with y hy
  exact ⟨hx,hy⟩

lemma profilePairKernel_integral {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) (z : D) (F : ZeroHeightPair e → ℝ) :
    (∫ p, F p ∂profilePairKernel e f w R j hj z) =
      ∫ p : HorizontalLayer e × HorizontalLayer e, F (horizontalPair e p)
        ∂((TailGrowth.normalizedRestriction (w z) {x | x.1 f ≤ j z}).prod
          (TailGrowth.normalizedRestriction (w z) {x | j z+R ≤ x.1 f})) := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  rw [profilePairKernel, Kernel.map_apply _ (measurable_of_countable _),
    integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    Kernel.prod_apply]
  rfl

lemma profilePairKernel_integrable {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) (z : D)
    (F : ZeroHeightPair e → ℝ) :
    Integrable F (profilePairKernel e f w R j hj z) ↔
      Integrable (fun p : HorizontalLayer e × HorizontalLayer e => F (horizontalPair e p))
        ((TailGrowth.normalizedRestriction (w z) {x | x.1 f ≤ j z}).prod
          (TailGrowth.normalizedRestriction (w z) {x | j z+R ≤ x.1 f})) := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  rw [profilePairKernel, Kernel.map_apply _ (measurable_of_countable _), Kernel.prod_apply]
  exact integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable

end DirectionalTransience

end

end OAI
