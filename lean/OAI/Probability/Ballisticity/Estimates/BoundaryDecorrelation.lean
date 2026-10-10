import Mathlib
import OAI.Probability.Ballisticity.Estimates.RealJointPastRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairSide {α : Type*} (b : Bool) (p : α × α) : α := if b then p.2 else p.1

lemma measurable_pairSide {α : Type*} [MeasurableSpace α] (b : Bool) :
    Measurable (pairSide (α := α) b) := by
  cases b <;> exact (by first | exact measurable_fst | exact measurable_snd)

lemma measurable_pairSide_recenter {d : ℕ} (b : Bool) (z : Lattice d × Lattice d) :
    Measurable (fun Q : Path d × Path d => fun j => pairSide b Q j-pairSide b z) := by
  exact Measurable.of_eval (fun index => ((measurable_pi_apply index).comp
    (measurable_pairSide b)).sub_const _)

lemma shared_boundary_test_decorrelation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0 < H i)
    (F : ℕ → BoundaryData d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i j, ‖F i j‖ ≤ C)
    (Z : ℕ → Lattice d → Lattice d → (Path d × Path d) → ℝ)
    (hZ : ∀ i a b, Measurable (Z i a b)) (M : ℝ)
    (hZb : ∀ i a b Q, ‖Z i a b Q‖ ≤ M)
    (hu : ∀ ε > 0, ∀ᶠ i in atTop, ∀ a b, signedHeight e a = signedHeight e b →
      |∫ Q, Z i a b Q ∂sharedConditionedPairLaw ν (realPosition (step e)) a b| < ε) :
    let ℓ := realPosition (step e)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => ∫ P, F i (D i P) *
      Z i (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (Y i P)
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let κ := fun (_ : ℕ) (z : BoundaryData d) =>
    sharedConditionedPairLaw ν ℓ (boundaryTerminal z).1 (boundaryTerminal z).2
  let hμprob : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ _ _
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let hκprob : ∀ i z, IsProbabilityMeasure (κ i z) := fun i z =>
    sharedConditionedPairLaw_probability ν ℓ _ _
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  refine @countable_restart_decorrelation (Path d × Path d) (BoundaryData d) (Path d × Path d)
    _ _ _ _ _ μ hμprob D Y κ hκprob (fun i => measurable_boundaryData _ _)
    (fun i => measurable_boundarySuffix _ _)
    (fun i => shared_boundaryData_map ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i) (hH i))
    (fun _ z => signedHeight e (boundaryTerminal z).1 = signedHeight e (boundaryTerminal z).2)
    ?_ F (fun i z Q => Z i (boundaryTerminal z).1 (boundaryTerminal z).2 Q)
    (fun i z => hZ i _ _) C M hC hF (fun i z Q => hZb i _ _ Q) ?_
  · intro i
    filter_upwards [shared_boundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
      (x i) (y i) (hxy i) (H i) (hH i)] with P hP
    simp only [D,boundaryTerminal_data]
    have he := hP.2.2.1.2.2
    rw [signedHeight_projection e,signedHeight_projection e] at he
    exact_mod_cast he
  · intro ε hε
    filter_upwards [hu ε hε] with i hi z hz
    simpa only [Real.norm_eq_abs] using hi _ _ hz

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

namespace DirectionalTransience

lemma uniform_eventually_of_all_sequences {A : Type*} [Nonempty A]
    (P : ℕ → A → Prop) (hP : ∀ a : ℕ → A, ∀ᶠ i in atTop, P i (a i)) :
    ∀ᶠ i in atTop, ∀ a, P i a := by
  let a (i : ℕ) : A := if h : ∃ x, ¬ P i x then h.choose else Classical.choice inferInstance
  filter_upwards [hP a] with i hi x
  by_contra hx
  have hh : ∃ x, ¬ P i x := ⟨x,hx⟩
  have ha : ¬ P i (a i) := by simpa only [a,dite_eq_left hh] using hh.choose_spec
  exact ha hi

lemma integral_bounded_test_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ℕ → Ω → E) (W : ProbabilityMeasure E)
    (hX : TendstoInDistribution X atTop id μ W) (F : E →ᵇ ℝ) :
    Tendsto (fun i => ∫ z, F (X i z) ∂μ i) atTop (𝓝 (∫ z, F z ∂(W : Measure E))) := by
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hX.tendsto F
  simpa only [ProbabilityMeasure.coe_mk,Measure.map_id,
    integral_map (hX.forall_aemeasurable _) F.continuous.aestronglyMeasurable] using hh

theorem shared_path_marginal_tests_uniform {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let F := fun i => recordLinearPath ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i)
      (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ G : C(unitInterval,ℝ) →ᵇ ℝ, ∀ ε > 0, ∀ᶠ i in atTop,
        ∀ x y : Lattice d, signedHeight e x = signedHeight e y →
          |(∫ P, G (F i (fun j => P.1 j-x)) ∂sharedConditionedPairLaw ν ℓ x y)-
            (∫ g, G g ∂(W : Measure C(unitInterval,ℝ)))| < ε ∧
          |(∫ P, G (F i (fun j => P.2 j-y)) ∂sharedConditionedPairLaw ν ℓ x y)-
            (∫ g, G g ∂(W : Measure C(unitInterval,ℝ)))| < ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let F := fun i => recordLinearPath ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i)
    (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr hT
  refine ⟨W,hW,fun G ε hε => ?_⟩
  let A := {p : Lattice d × Lattice d // signedHeight e p.1 = signedHeight e p.2}
  let : Nonempty A := ⟨⟨(0,0),rfl⟩⟩
  have hh : ∀ᶠ i in atTop, ∀ p : A,
      |(∫ P, G (F i (fun j => P.1 j-p.val.1)) ∂sharedConditionedPairLaw ν ℓ p.val.1 p.val.2)-
        (∫ g, G g ∂(W : Measure C(unitInterval,ℝ)))| < ε ∧
      |(∫ P, G (F i (fun j => P.2 j-p.val.2)) ∂sharedConditionedPairLaw ν ℓ p.val.1 p.val.2)-
        (∫ g, G g ∂(W : Measure C(unitInterval,ℝ)))| < ε := by
    apply uniform_eventually_of_all_sequences
    intro p
    let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (p i).val.1 (p i).val.2) := fun i =>
      sharedConditionedPairLaw_probability ν ℓ _ _
        (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
    obtain ⟨h1,h2⟩ := hlim (fun i => (p i).val.1) (fun i => (p i).val.2) (fun i => (p i).property)
    have h1' := integral_bounded_test_tendsto _ _ W h1 G
    have h2' := integral_bounded_test_tendsto _ _ W h2 G
    filter_upwards [(Metric.tendsto_nhds.mp h1') ε hε,(Metric.tendsto_nhds.mp h2') ε hε] with i hi hj
    simpa only [Real.dist_eq] using And.intro hi hj
  filter_upwards [hh] with i hi x y hxy
  exact hi ⟨(x,y),hxy⟩

end DirectionalTransience

end

end

end OAI
