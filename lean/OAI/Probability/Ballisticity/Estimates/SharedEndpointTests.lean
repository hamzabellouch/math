import Mathlib
import OAI.Probability.Ballisticity.Estimates.BoundaryDecorrelation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def centeredFirstHit {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) (X : Path d) : ℝ :=
  (signedCoordinate f (recordIndexPosition ℓ k (fun j => X j-x))-(k:ℝ)*θ)/r

lemma measurable_centeredFirstHit {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) : Measurable (centeredFirstHit ℓ f θ r k x) := by
  apply Measurable.div_const
  apply Measurable.sub_const
  exact ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ k)).comp (by fun_prop)

theorem shared_endpoint_tests_uniform {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (T : ℝ) (hT : 0 < T) (k : ℕ → ℕ)
    (hk : ∀ i, (k i:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (t : ℝ) (hkt : Tendsto (fun i => (k i:ℝ)/fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i)) atTop (𝓝 t)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let Z := fun i => centeredFirstHit ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i) (k i)
    ∀ G : ℝ →ᵇ ℝ, ∀ ε > 0, ∀ᶠ i in atTop,
      ∀ x y : Lattice d, signedHeight e x = signedHeight e y →
        |(∫ P, G (Z i x P.1) ∂sharedConditionedPairLaw ν ℓ x y)-
          (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))| < ε ∧
        |(∫ P, G (Z i y P.2) ∂sharedConditionedPairLaw ν ℓ x y)-
          (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))| < ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let V := 1/(2*commonMeanWidth ν ℓ)
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr hT.le
  have hw (I : Finset unitInterval) : (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T*V) I := by
    simpa only [V,mul_one_div] using hW I
  intro G ε hε
  let A := {p : Lattice d × Lattice d // signedHeight e p.1 = signedHeight e p.2}
  let : Nonempty A := ⟨⟨(0,0),rfl⟩⟩
  have hh : ∀ᶠ i in atTop, ∀ p : A,
      |(∫ P, G (centeredFirstHit ℓ f (θ i) (r i) (k i) p.val.1 P.1)
        ∂sharedConditionedPairLaw ν ℓ p.val.1 p.val.2)-
          (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))| < ε ∧
      |(∫ P, G (centeredFirstHit ℓ f (θ i) (r i) (k i) p.val.2 P.2)
        ∂sharedConditionedPairLaw ν ℓ p.val.1 p.val.2)-
          (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))| < ε := by
    apply uniform_eventually_of_all_sequences
    intro p
    let μ := fun i => sharedConditionedPairLaw ν ℓ (p i).val.1 (p i).val.2
    let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
    obtain ⟨h1,h2⟩ := hlim (fun i => (p i).val.1) (fun i => (p i).val.2) (fun i => (p i).property)
    have he1 := varying_height_path_gaussian_eval μ
      (fun i j P => signedCoordinate f (recordIndexPosition ℓ j (fun a => P.1 a-(p i).val.1))-(j:ℝ)*θ i)
      (fun i j => (((measurable_of_countable (signedCoordinate f)).comp
        (measurable_recordIndexPosition ℓ j)).comp (by fun_prop)).sub_const _)
      r n hn T hT V W h1 hw k hk hkt
    have he2 := varying_height_path_gaussian_eval μ
      (fun i j P => signedCoordinate f (recordIndexPosition ℓ j (fun a => P.2 a-(p i).val.2))-(j:ℝ)*θ i)
      (fun i j => (((measurable_of_countable (signedCoordinate f)).comp
        (measurable_recordIndexPosition ℓ j)).comp (by fun_prop)).sub_const _)
      r n hn T hT V W h2 hw k hk hkt
    let M : ProbabilityMeasure ℝ := ⟨gaussianReal 0 (Real.toNNReal (V*t)),inferInstance⟩
    have ht1 := integral_bounded_test_tendsto μ _ M he1 G
    have ht2 := integral_bounded_test_tendsto μ _ M he2 G
    have hv : V*t = t/(2*commonMeanWidth ν ℓ) := by dsimp [V]; ring
    filter_upwards [(Metric.tendsto_nhds.mp ht1) ε hε,(Metric.tendsto_nhds.mp ht2) ε hε] with i hi hj
    simpa only [M,ProbabilityMeasure.coe_mk,Real.dist_eq,hv,centeredFirstHit] using And.intro hi hj
  filter_upwards [hh] with i hi x y hxy
  exact hi ⟨(x,y),hxy⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma bounded_normal_test_mean {v : ℝ≥0} (G : ℝ →ᵇ ℝ) :
    ‖∫ z, G z ∂gaussianReal 0 v‖ ≤ ‖G‖ := by
  simpa using norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
    (f := fun z => G z) (Filter.Eventually.of_forall (fun z => G.norm_coe_le_norm z))

lemma shared_boundary_endpoint_decorrelation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (T : ℝ) (hT : 0 < T) (k : ℕ → ℕ)
    (hk : ∀ i, (k i:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (t : ℝ) (hkt : Tendsto (fun i => (k i:ℝ)/fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i)) atTop (𝓝 t))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0 < H i)
    (F : ℕ → BoundaryData d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i j, ‖F i j‖ ≤ C)
    (G : ℝ →ᵇ ℝ) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => ∫ P, F i (D i P) *
      (G (centeredFirstHit ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i) (k i)
        (pairSide b (boundaryTerminal (D i P))) (pairSide b (Y i P)))-
        (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let m := ∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))
  let Z := fun i a c (Q : Path d × Path d) =>
    G (centeredFirstHit ℓ f (θ i) (r i) (k i) (pairSide b (a,c)) (pairSide b Q))
  have hZ (i : ℕ) (a c : Lattice d) : Measurable (Z i a c) :=
    G.continuous.measurable.comp ((measurable_centeredFirstHit ℓ f (θ i) (r i) (k i) _).comp
      (measurable_pairSide b))
  have hm : ‖m‖ ≤ ‖G‖ := bounded_normal_test_mean G
  have hZb (i : ℕ) (a c : Lattice d) (Q : Path d × Path d) : ‖Z i a c Q‖ ≤ ‖G‖ :=
    G.norm_coe_le_norm _
  apply shared_boundary_test_decorrelation ν hue e htrans x y hxy H hH F C hC hF
    (fun i a c Q => Z i a c Q-m) (fun i a c => (hZ i a c).sub_const m) (2*‖G‖)
    (fun i a c Q => (norm_sub_le _ _).trans (by linarith [hZb i a c Q]))
  intro ε hε
  filter_upwards [shared_endpoint_tests_uniform ν hue e f hef htrans r hr hn T hT k hk t hkt G ε hε]
    with i hi a c hac
  let : IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ a c) :=
    sharedConditionedPairLaw_probability ν ℓ a c
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans a c))
  have hzi : Integrable (Z i a c) (sharedConditionedPairLaw ν ℓ a c) :=
    Integrable.of_bound (hZ i a c).aestronglyMeasurable ‖G‖ (Filter.Eventually.of_forall (hZb i a c))
  rw [integral_sub hzi (integrable_const m),integral_const]
  simp only [probReal_univ,one_smul]
  have hh := hi a c hac
  cases b
  · exact hh.1
  · exact hh.2

end DirectionalTransience

end

end

end OAI
