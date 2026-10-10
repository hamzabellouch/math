import Mathlib
import OAI.Probability.Ballisticity.Estimates.BoundarySuffixIdentity

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma weighted_test_perturbation {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0 ≤ C)
    (hFb : ∀ i ω, ‖F i ω‖ ≤ C)
    (f : ℝ →ᵇ ℝ) (hf : UniformContinuous f)
    (hclose : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ i).real {ω | ε ≤ |X i ω-Y i ω|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f (X i ω)-f (Y i ω)) ∂μ i) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let a := η/(2*(C+1))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuous_iff.mp hf a ha
  have hh : Tendsto (fun i => C*(2*‖f‖)*(μ i).real {ω | δ ≤ |X i ω-Y i ω|}) atTop (𝓝 0) := by
    simpa using (hclose δ hδ).const_mul (C*(2*‖f‖))
  filter_upwards [hh.eventually_lt_const (show (0:ℝ)<η/2 by positivity)] with i hi
  let A := {ω | δ ≤ |X i ω-Y i ω|}
  have hA : MeasurableSet A := measurableSet_le measurable_const ((hX i).sub (hY i)).abs
  have hg : Integrable (fun ω => C*a+A.indicator (fun _ => C*(2*‖f‖)) ω) (μ i) :=
    (integrable_const _).add ((integrable_const _).indicator hA)
  have hbound : ∀ᵐ ω ∂μ i, ‖F i ω*(f (X i ω)-f (Y i ω))‖ ≤
      C*a+A.indicator (fun _ => C*(2*‖f‖)) ω := by
    exact Eventually.of_forall fun ω => by
      rw [norm_mul]
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]
        have hb := (norm_sub_le (f (X i ω)) (f (Y i ω))).trans
          (add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _))
        have hb' := mul_le_mul (hFb i ω) hb (norm_nonneg _) hC
        nlinarith
      · rw [Set.indicator_of_notMem h,add_zero]
        have hdist : dist (X i ω) (Y i ω) < δ := by
          simpa only [A,Set.mem_ofPred_eq,not_le,Real.dist_eq] using h
        have hb : ‖f (X i ω)-f (Y i ω)‖ ≤ a := by
          simpa only [Real.norm_eq_abs,Real.dist_eq] using (hδf hdist).le
        exact mul_le_mul (hFb i ω) hb (norm_nonneg _) hC
  have hIntegrable := hg.mono' ((hF i).mul ((f.continuous.measurable.comp (hX i)).sub
    (f.continuous.measurable.comp (hY i)))).aestronglyMeasurable hbound
  have hnorm := (norm_integral_le_integral_norm
    (fun sample => F i sample*(f (X i sample)-f (Y i sample)))).trans
    (integral_mono_ae hIntegrable.norm hg hbound)
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hA),
    integral_const,integral_indicator_const _ hA] at hnorm
  simp only [probReal_univ,smul_eq_mul,one_mul] at hnorm
  rw [Real.dist_eq,sub_zero]
  have hac : C*a < η/2 := by
    dsimp [a]
    have hden : 0 < 2*(C+1) := by positivity
    rw [← mul_div_assoc,div_lt_iff₀ hden]
    nlinarith
  change C*(2*‖f‖)*(μ i).real A < η/2 at hi
  rw [Real.norm_eq_abs] at hnorm
  nlinarith

lemma weighted_centered_test_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0 ≤ C)
    (hFb : ∀ i ω, ‖F i ω‖ ≤ C) (f : ℝ →ᵇ ℝ) (hf : UniformContinuous f) (m : ℝ)
    (hclose : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ i).real {ω | ε ≤ |X i ω-Y i ω|}) atTop (𝓝 0))
    (hlim : Tendsto (fun i => ∫ ω, F i ω*(f (Y i ω)-m) ∂μ i) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f (X i ω)-m) ∂μ i) atTop (𝓝 0) := by
  have hi (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (i : ℕ) :
      Integrable (fun ω => F i ω*(f (Z i ω)-m)) (μ i) := by
    apply Integrable.of_bound ((hF i).mul ((f.continuous.measurable.comp (hZ i)).sub_const m)).aestronglyMeasurable
      (C*(‖f‖+‖m‖))
    exact Eventually.of_forall fun ω => by
      change ‖F i ω*(f (Z i ω)-m)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) ((norm_sub_le _ _).trans
        (add_le_add (f.norm_coe_le_norm _) le_rfl)) (norm_nonneg _) hC
  have hp := weighted_test_perturbation μ X Y hX hY F hF C hC hFb f hf hclose
  have he (i : ℕ) : (∫ ω, F i ω*(f (X i ω)-m) ∂μ i) =
      (∫ ω, F i ω*(f (Y i ω)-m) ∂μ i)+(∫ ω, F i ω*(f (X i ω)-f (Y i ω)) ∂μ i) := by
    have heq : (fun ω => F i ω*(f (X i ω)-f (Y i ω))) =
        (fun ω => F i ω*(f (X i ω)-m)-F i ω*(f (Y i ω)-m)) := by funext ω; ring
    rw [heq,integral_sub (hi X hX i) (hi Y hY i)]
    ring
  simp_rw [he]
  simpa using hlim.add hp

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma measurable_centeredFirstHit_variable_start {d : ℕ} (ℓ : Vector d)
    (f : Direction d) (θ r : ℝ) (k : ℕ) :
    Measurable (fun q : Path d × Lattice d => centeredFirstHit ℓ f θ r k q.2 q.1) := by
  apply measurable_from_prod_countable_left
  intro z
  exact measurable_centeredFirstHit ℓ f θ r k z

lemma measurable_boundary_terminal_side {d : ℕ} (ℓ : Vector d) (L : ℝ) (b : Bool) :
    Measurable (fun P : Path d × Path d => pairSide b (boundaryTerminal (boundaryData ℓ L P))) :=
  (measurable_of_countable (fun z : BoundaryData d => pairSide b (boundaryTerminal z))).comp
    (measurable_boundaryData ℓ L)

lemma measurable_boundary_centeredFirstHit {d : ℕ} (ℓ : Vector d)
    (f : Direction d) (θ r : ℝ) (k : ℕ) (L : ℝ) (b : Bool) :
    Measurable (fun P : Path d × Path d => centeredFirstHit ℓ f θ r k
      (pairSide b (boundaryTerminal (boundaryData ℓ L P)))
      (pairSide b (boundarySuffix ℓ L P))) := by
  apply Measurable.div_const
  apply Measurable.sub_const
  apply (measurable_of_countable (signedCoordinate f)).comp
  apply (measurable_recordIndexPosition ℓ k).comp
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp ((measurable_pairSide b).comp
    (measurable_boundarySuffix ℓ L))).sub (measurable_boundary_terminal_side ℓ L b)

theorem shared_deterministic_increment_decorrelation {d : ℕ} (ν : Measure (Row d))
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
    (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => ∫ P, F i (D i P) *
      (G (centeredHitIncrement ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i) (H i) (k i)
        (pairSide b (x i,y i)) (pairSide b P))-
        (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let X := fun i P => centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i)
    (pairSide b (x i,y i)) (pairSide b P)
  let Y := fun i P => centeredFirstHit ℓ f (θ i) (r i) (k i)
    (pairSide b (boundaryTerminal (D i P))) (pairSide b (S i P))
  have hX (i : ℕ) : Measurable (X i) :=
    (measurable_centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) _).comp (measurable_pairSide b)
  have hY (i : ℕ) : Measurable (Y i) :=
    measurable_boundary_centeredFirstHit ℓ f (θ i) (r i) (k i) _ b
  exact weighted_centered_test_transfer μ X Y hX hY (fun i P => F i (D i P))
    (fun i => (measurable_of_countable (F i)).comp (measurable_boundaryData _ _)) C hC
    (fun i P => hF i (D i P)) G hG _
    (fun ε hε => shared_boundary_increment_replacement ν hue e f htrans x y hxy H k hH θ r hr.1 b ε hε)
    (shared_boundary_endpoint_decorrelation ν hue e f hef htrans r hr hn T hT k hk t hkt
      x y hxy H hH F C hC hF G b)

end DirectionalTransience

end

end

end OAI
