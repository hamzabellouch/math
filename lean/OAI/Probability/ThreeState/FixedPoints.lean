import Mathlib
import OAI.Probability.ThreeState.Update

namespace OAI

/-! Continuity of posterior updates and fixed points of the likelihood law. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma continuous_productWeight (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    Continuous (fun m : Fin n → Message => productWeight lam h m i) := by
  apply continuous_finsetProd
  intro j _
  exact (continuous_apply i).comp
    (continuous_subtype_val.comp ((continuous_edgeMessage lam h).comp (continuous_apply j)))

lemma continuous_normalizer (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    Continuous (fun m : Fin n → Message => normalizer lam h m) :=
  (continuous_finsetSum _ (fun i _ => continuous_productWeight lam h n i)).div_const 3

lemma continuousAt_combineMessage (lam : ℝ) (h : Admissible lam) {n : ℕ}
    (m : Fin n → Message) (hm : normalizer lam h m ≠ 0) :
    ContinuousAt (combineMessage lam h) m := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  have hn : ContinuousAt (fun v : Fin n → Message => normalizer lam h v) m :=
    (continuous_normalizer lam h n).continuousAt
  have hw : ContinuousAt (fun v : Fin n → Message => productWeight lam h v i) m :=
    (continuous_productWeight lam h n i).continuousAt
  have ht := hw.div hn hm
  have he : ∀ᶠ v in 𝓝 m, normalizer lam h v ≠ 0 := hn.eventually (eventually_ne_nhds hm)
  have heq : (fun v => productWeight lam h v i / normalizer lam h v) =ᶠ[𝓝 m]
      (fun v => combineMessage lam h v i) := by
    filter_upwards [he] with v hv
    simp only [combineMessage, dite_eq_right hv]
  have hp : productWeight lam h m i / normalizer lam h m = combineMessage lam h m i := by
    simp only [combineMessage, dite_eq_right hm]
  change Tendsto _ (𝓝 m) (𝓝 (productWeight lam h m i / normalizer lam h m)) at ht
  rw [hp] at ht
  exact ht.congr' heq

 
noncomputable def weightedTest (lam : ℝ) (h : Admissible lam) (n : ℕ)
    (f : C(Message,ℝ)) (m : Fin n → Message) : ℝ :=
  normalizer lam h m * f (combineMessage lam h m)

lemma weightedTest_bound (lam : ℝ) (h : Admissible lam) (n : ℕ)
    (f : C(Message,ℝ)) (C : ℝ) (hC : ∀ m, |f m| ≤ C) (m : Fin n → Message) :
    |weightedTest lam h n f m| ≤ C * normalizer lam h m := by
  dsimp only [weightedTest]
  rw [abs_mul, abs_of_nonneg (normalizer_nonneg _ _ _), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _) (normalizer_nonneg _ _ _)

lemma continuous_weightedTest (lam : ℝ) (h : Admissible lam) (n : ℕ)
    (f : C(Message,ℝ)) : Continuous (weightedTest lam h n f) := by
  apply continuous_iff_continuousAt.mpr
  intro m
  by_cases hm : normalizer lam h m = 0
  · obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
    have hh : ∀ v, |weightedTest lam h n f v| ≤ C * normalizer lam h v :=
      weightedTest_bound lam h n f C (fun v => by simpa only [Real.norm_eq_abs] using hC v (Set.mem_univ _))
    have ht : Tendsto (fun v : Fin n → Message => C * normalizer lam h v) (𝓝 m) (𝓝 0) := by
      simpa only [hm, mul_zero] using
        (tendsto_const_nhds.mul (continuous_normalizer lam h n).continuousAt :
          Tendsto (fun v => C * normalizer lam h v) (𝓝 m) (𝓝 (C*normalizer lam h m)))
    have hz : weightedTest lam h n f m = 0 := by simp [weightedTest, hm]
    rw [ContinuousAt, hz]
    exact squeeze_zero_norm (fun v => by simpa only [Real.norm_eq_abs] using hh v) ht
  · exact (continuous_normalizer lam h n).continuousAt.mul
      (f.continuous.continuousAt.comp (continuousAt_combineMessage lam h m hm))

noncomputable def weightedTestMap (lam : ℝ) (h : Admissible lam) (n : ℕ)
    (f : C(Message,ℝ)) : C((Fin n → Message),ℝ) :=
  ⟨weightedTest lam h n f, continuous_weightedTest lam h n f⟩

noncomputable def degreeTest (lam : ℝ) (h : Admissible lam) (n : ℕ)
    (f : C(Message,ℝ)) (Q : ProbabilityMeasure Message) : ℝ :=
  ∫ m, weightedTest lam h n f m ∂(iidMeasure Q n : Measure (Fin n → Message))

lemma continuous_degreeTest (lam : ℝ) (h : Admissible lam) (n : ℕ)
    (f : C(Message,ℝ)) : Continuous (degreeTest lam h n f) :=
  (ProbabilityMeasure.continuous_integral_continuousMap (weightedTestMap lam h n f)).comp
    (continuous_iidMeasure n)

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma mean_sigmaPMF {ι : Type*} {α : ι → Type*} (p : PMF ι) (q : ∀ i, PMF (α i))
    (f : Sigma α → ℝ) (hf : HasMean (sigmaPMF p q) f) :
    mean (sigmaPMF p q) f = mean p (fun i => mean (q i) (fun a => f ⟨i,a⟩)) := by
  change (∑' x, mass (sigmaPMF p q) x * f x) = _
  rw [hf.tsum_sigma]
  unfold mean
  apply tsum_congr
  intro i
  simp only [mass_sigmaPMF, mul_assoc, tsum_mul_left]

lemma degreeTest_likelihood {α : Type*} (law : Spin → PMF α) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) (f : C(Message,ℝ)) :
    degreeTest lam h n f (likelihoodLaw law) =
      mean (iidVector (marginal law) n) (fun v =>
        normalizer lam h (fun j => likelihood law (v j)) *
          f (combineMessage lam h (fun j => likelihood law (v j)))) :=
  integral_iid_likelihood law n (weightedTestMap lam h n f)

 

lemma test_compose_identity {α : Type*} (offspring : PMF ℕ) (law : Spin → PMF α)
    (lam : ℝ) (h : Admissible lam) (f : C(Message,ℝ)) :
    ∫ m, f m ∂(likelihoodLaw (composeLaw offspring law lam h) : Measure Message) =
      mean offspring (fun n => degreeTest lam h n f (likelihoodLaw law)) := by
  rw [integral_likelihoodLaw, mean_test_compose]
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  have hi := hasMean_weighted_compose offspring law lam h f C
    (fun m => by simpa only [Real.norm_eq_abs] using hC m (Set.mem_univ _))
  rw [productReference, mean_sigmaPMF _ _ _ hi]
  apply mean_congr
  intro n
  exact (degreeTest_likelihood law lam h n f).symm

noncomputable def coordinateMap (i : Spin) : C(Message,ℝ) :=
  ⟨fun m => m i, (continuous_apply i).comp continuous_subtype_val⟩

 
def Balanced (Q : ProbabilityMeasure Message) : Prop :=
  ∀ i : Spin, ∫ m, m i ∂(Q : Measure Message) = 1

lemma balanced_likelihoodLaw {α : Type*} (law : Spin → PMF α) : Balanced (likelihoodLaw law) := by
  intro i
  change (∫ m, coordinateMap i m ∂(likelihoodLaw law : Measure Message)) = 1
  rw [integral_likelihoodLaw]
  exact mean_likelihood law i

lemma balanced_limit {Qn : ℕ → ProbabilityMeasure Message} {Q : ProbabilityMeasure Message}
    (hn : ∀ n, Balanced (Qn n)) (hlim : Tendsto Qn atTop (𝓝 Q)) : Balanced Q := by
  intro i
  have hh := ((ProbabilityMeasure.continuous_integral_continuousMap (coordinateMap i)).tendsto Q).comp hlim
  have he : (fun n => ∫ m, coordinateMap i m ∂(Qn n : Measure Message)) = (fun _ : ℕ => (1:ℝ)) :=
    funext (fun n => hn n i)
  simp only [Function.comp_def, he] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

lemma integral_edgeMessage (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (i : Spin) : ∫ m, edgeMessage lam h m i ∂(Q : Measure Message) = 1 := by
  have hi : Integrable (fun m : Message => m i) (Q : Measure Message) :=
    (coordinateMap i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ m, 1+lam*(m i-1) ∂(Q : Measure Message)) = 1
  have hs : Integrable (fun m : Message => m i-1) (Q : Measure Message) :=
    hi.sub (integrable_const (1:ℝ))
  have ht : Integrable (fun m : Message => lam*(m i-1)) (Q : Measure Message) := hs.const_mul lam
  rw [integral_add (integrable_const (1:ℝ)) ht, integral_const_mul,
    integral_sub hi (integrable_const (1:ℝ)), integral_const, hQ i]
  simp

lemma integral_productWeight (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) (i : Spin) :
    ∫ m, productWeight lam h m i ∂(iidMeasure Q n : Measure (Fin n → Message)) = 1 := by
  change (∫ m : Fin n → Message, ∏ j, edgeMessage lam h (m j) i
    ∂Measure.pi (fun _ : Fin n => (Q : Measure Message))) = 1
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (m : Message) => edgeMessage lam h m i)]
  simp [integral_edgeMessage lam h Q hQ i]

lemma integral_normalizer (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) :
    ∫ m, normalizer lam h m ∂(iidMeasure Q n : Measure (Fin n → Message)) = 1 := by
  change (∫ m, (∑ i, productWeight lam h m i)/3 ∂(iidMeasure Q n : Measure (Fin n → Message))) = 1
  rw [integral_div, integral_finsetSum]
  · simp [integral_productWeight lam h Q hQ n]
  · intro i _
    exact (continuous_productWeight lam h n i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma degreeTest_bound (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) (f : C(Message,ℝ)) (C : ℝ) (hC : ∀ m, |f m| ≤ C) :
    |degreeTest lam h n f Q| ≤ C := by
  have hi : Integrable (fun m : Fin n → Message => |weightedTest lam h n f m|)
      (iidMeasure Q n : Measure (Fin n → Message)) :=
    (continuous_weightedTest lam h n f).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun m : Fin n → Message => C*normalizer lam h m)
      (iidMeasure Q n : Measure (Fin n → Message)) :=
    (continuous_const.mul (continuous_normalizer lam h n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    |degreeTest lam h n f Q| ≤ ∫ m, |weightedTest lam h n f m| ∂(iidMeasure Q n : Measure (Fin n → Message)) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ m, C*normalizer lam h m ∂(iidMeasure Q n : Measure (Fin n → Message)) :=
      integral_mono hi hj (weightedTest_bound lam h n f C hC)
    _ = C := by rw [integral_const_mul, integral_normalizer lam h Q hQ n, mul_one]

lemma mean_degreeTest_tendsto (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (f : C(Message,ℝ)) {Qn : ℕ → ProbabilityMeasure Message} {Q : ProbabilityMeasure Message}
    (hn : ∀ n, Balanced (Qn n)) (hlim : Tendsto Qn atTop (𝓝 Q)) :
    Tendsto (fun k => mean offspring (fun n => degreeTest lam h n f (Qn k))) atTop
      (𝓝 (mean offspring (fun n => degreeTest lam h n f Q))) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  apply tendsto_tsum_of_dominated_convergence ((mass_summable offspring).mul_right C)
  · intro n
    exact tendsto_const_nhds.mul (((continuous_degreeTest lam h n f).tendsto Q).comp hlim)
  · apply Eventually.of_forall
    intro k n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg offspring n)]
    exact mul_le_mul_of_nonneg_left (degreeTest_bound lam h (Qn k) (hn k) n f C
      (fun m => by simpa only [Real.norm_eq_abs] using hC m (Set.mem_univ _))) (mass_nonneg offspring n)

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

 
def IsPosteriorFixedPoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) : Prop :=
  Balanced Q ∧ ∀ f : C(Message,ℝ), ∫ m, f m ∂(Q : Measure Message) =
    mean offspring (fun n => degreeTest lam h n f Q)

lemma orderedLaw_succ (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    orderedLaw offspring lam h (n+1) = composeLaw offspring (orderedLaw offspring lam h n) lam h := rfl

lemma ordered_exists_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    ∃ Q : ProbabilityMeasure Message, IsPosteriorFixedPoint offspring lam h Q ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => likelihoodLaw (orderedLaw offspring lam h (φ n))) atTop (𝓝 Q) := by
  obtain ⟨Q,φ,hφ,hleft,hright⟩ := ordered_likelihood_common_subsequence offspring lam h
  refine ⟨Q, ⟨balanced_limit (fun n => balanced_likelihoodLaw _) hleft, ?_⟩,φ,hφ,hleft⟩
  intro f
  have hl := ((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto Q).comp hright
  have hr := mean_degreeTest_tendsto offspring lam h f
    (fun n => balanced_likelihoodLaw (orderedLaw offspring lam h (φ n))) hleft
  have he : (fun n => ∫ m, f m ∂(likelihoodLaw (orderedLaw offspring lam h (φ n+1)) : Measure Message)) =
      (fun n => mean offspring (fun k => degreeTest lam h k f (likelihoodLaw (orderedLaw offspring lam h (φ n))))) := by
    funext n
    rw [orderedLaw_succ, test_compose_identity]
  simp only [Function.comp_def, he] at hl
  exact tendsto_nhds_unique hl hr

noncomputable def messageTV (m : Message) : ℝ := (∑ i : Spin, |m i-1|)/6

lemma continuous_messageTV : Continuous messageTV := by
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).abs

noncomputable def messageTVMap : C(Message,ℝ) := ⟨messageTV, continuous_messageTV⟩

lemma posterior_tv_likelihood {α : Type*} (law : Spin → PMF α) (y : α) :
    (∑ i : Spin, |posterior law y i - 1/3|)/2 = messageTV (likelihood law y) := by
  have he (i : Spin) : |likelihood law y i - 1| = 3 * |posterior law y i - 1/3| := by
    rw [likelihood_apply]
    have hr : 3*posterior law y i-1 = 3*(posterior law y i-1/3) := by ring
    rw [hr, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
  simp only [messageTV, he, ← Finset.mul_sum]
  ring

lemma integral_messageTV_likelihood {α : Type*} (law : Spin → PMF α) :
    ∫ m, messageTV m ∂(likelihoodLaw law : Measure Message) = advantage law := by
  change (∫ m, messageTVMap m ∂(likelihoodLaw law : Measure Message)) = _
  rw [integral_likelihoodLaw]
  unfold mean advantage
  apply tsum_congr
  intro y
  rw [posterior_tv_likelihood]
  rfl

lemma advantage_tendsto_of_likelihood {α : ℕ → Type*} (law : ∀ n, Spin → PMF (α n))
    {Q : ProbabilityMeasure Message} (hlim : Tendsto (fun n => likelihoodLaw (law n)) atTop (𝓝 Q)) :
    Tendsto (fun n => advantage (law n)) atTop (𝓝 (∫ m, messageTV m ∂(Q : Measure Message))) := by
  have hh := ((ProbabilityMeasure.continuous_integral_continuousMap messageTVMap).tendsto Q).comp hlim
  simpa only [Function.comp_def, messageTVMap, ContinuousMap.coe_mk, integral_messageTV_likelihood] using hh

 

lemma exists_fixedpoint_advantage (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    ∃ L : ℝ, ∃ Q : ProbabilityMeasure Message,
      0 ≤ L ∧ Tendsto (fun n => advantage (observedLaw offspring lam h n)) atTop (𝓝 L) ∧
      IsPosteriorFixedPoint offspring lam h Q ∧
      L ≤ ∫ m, messageTV m ∂(Q : Measure Message) := by
  obtain ⟨Q,hQ,φ,hφ,hlim⟩ := ordered_exists_fixedpoint offspring lam h
  have htop := advantage_tendsto_of_likelihood (fun n => orderedLaw offspring lam h (φ n)) hlim
  obtain ⟨L,hL,_hL1,hactual⟩ := observedAdvantage_tendsto offspring lam h
  refine ⟨L,Q,hL,hactual,hQ,?_⟩
  exact le_of_tendsto_of_tendsto (hactual.comp hφ.tendsto_atTop) htop
    (Eventually.of_forall (fun n => orderedAdvantage_dominates offspring lam h (φ n)))

end ThreeState

end OAI
