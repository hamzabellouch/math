import Mathlib
import OAI.Probability.ThreeState.Entropy

namespace OAI

/-! Independent-branch entropy identities and correlation corrections. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma iid_integral_weighted_single (Q : ProbabilityMeasure Message) (n : ℕ)
    (w g : C(Message,ℝ)) (hw : ∫ m, w m ∂(Q : Measure Message) = 1) (a : Fin n) :
    ∫ m : Fin n → Message, (∏ j, w (m j))*g (m a) ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      ∫ m, w m*g m ∂(Q : Measure Message) := by
  have he (m : Fin n → Message) : (∏ j, w (m j))*g (m a) =
      ∏ j, w (m j)*(if j=a then g (m j) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [he]
  change (∫ m : Fin n → Message, ∏ j, w (m j)*(if j=a then g (m j) else 1)
    ∂Measure.pi (fun _ : Fin n => (Q : Measure Message))) = _
  rw [integral_fintype_prod_eq_prod (fun j (m : Message) => w m*(if j=a then g m else 1))]
  have hi (j : Fin n) : (∫ m, w m*(if j=a then g m else 1) ∂(Q : Measure Message)) =
      if j=a then ∫ m, w m*g m ∂(Q : Measure Message) else 1 := by
    by_cases hj : j=a <;> simp [hj, hw]
  simp_rw [hi]
  simp

lemma iid_integral_weighted_pair (Q : ProbabilityMeasure Message) (n : ℕ)
    (w g : C(Message,ℝ)) (hw : ∫ m, w m ∂(Q : Measure Message) = 1) (a b : Fin n) (hab : a ≠ b) :
    ∫ m : Fin n → Message, (∏ j, w (m j))*g (m a)*g (m b) ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      (∫ m, w m*g m ∂(Q : Measure Message))^2 := by
  have he (m : Fin n → Message) : (∏ j, w (m j))*g (m a)*g (m b) =
      ∏ j, w (m j)*(if j=a then g (m j) else 1)*(if j=b then g (m j) else 1) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [he]
  change (∫ m : Fin n → Message, ∏ j, w (m j)*(if j=a then g (m j) else 1)*(if j=b then g (m j) else 1)
    ∂Measure.pi (fun _ : Fin n => (Q : Measure Message))) = _
  rw [integral_fintype_prod_eq_prod (fun j (m : Message) => w m*(if j=a then g m else 1)*(if j=b then g m else 1))]
  have hi (j : Fin n) :
      (∫ m, w m*(if j=a then g m else 1)*(if j=b then g m else 1) ∂(Q : Measure Message)) =
      (if j=a then ∫ m, w m*g m ∂(Q : Measure Message) else 1)*
      (if j=b then ∫ m, w m*g m ∂(Q : Measure Message) else 1) := by
    by_cases hja : j=a
    · subst j
      simp [hab]
    · by_cases hjb : j=b
      · subst j
        simp [hja]
      · simp [hja, hjb, hw]
  simp_rw [hi]
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true, pow_two]

lemma iid_integral_weighted_sum (Q : ProbabilityMeasure Message) (n : ℕ)
    (w g : C(Message,ℝ)) (hw : ∫ m, w m ∂(Q : Measure Message) = 1) :
    ∫ m : Fin n → Message, (∏ j, w (m j))*(∑ j, g (m j)) ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      n*(∫ m, w m*g m ∂(Q : Measure Message)) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [iid_integral_weighted_single Q n w g hw]
    simp
  · intro j _
    exact (show Continuous (fun m : Fin n → Message => (∏ k, w (m k))*g (m j)) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma iid_integral_weighted_sum_sq (Q : ProbabilityMeasure Message) (n : ℕ)
    (w g : C(Message,ℝ)) (hw : ∫ m, w m ∂(Q : Measure Message) = 1) :
    ∫ m : Fin n → Message, (∏ j, w (m j))*(∑ j, g (m j))^2 ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      n*(∫ m, w m*(g m)^2 ∂(Q : Measure Message))+
      (n:ℝ)*(n-1)*(∫ m, w m*g m ∂(Q : Measure Message))^2 := by
  have he (m : Fin n → Message) : (∏ j, w (m j))*(∑ j, g (m j))^2 =
      ∑ a, ∑ b, (∏ j, w (m j))*g (m a)*g (m b) := by
    simp only [pow_two, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  have hi (a b : Fin n) : Integrable
      (fun m : Fin n → Message => (∏ j, w (m j))*g (m a)*g (m b))
      (iidMeasure Q n : Measure (Fin n → Message)) :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum Finset.univ (fun b _ => hi _ b)]
  have hj (a b : Fin n) :
      (∫ m : Fin n → Message, (∏ j, w (m j))*g (m a)*g (m b) ∂(iidMeasure Q n : Measure (Fin n → Message))) =
      (∫ m, w m*g m ∂(Q : Measure Message))^2 +
      if a=b then (∫ m, w m*(g m)^2 ∂(Q : Measure Message))-(∫ m, w m*g m ∂(Q : Measure Message))^2 else 0 := by
    by_cases hab : a=b
    · subst b
      have hp : (fun m : Fin n → Message => (∏ j, w (m j))*g (m a)*g (m a)) =
        (fun m => (∏ j, w (m j))*(g (m a))^2) := by funext m; ring
      rw [hp]
      have hh := iid_integral_weighted_single Q n w (g*g) hw a
      change (∫ m : Fin n → Message, (∏ j, w (m j))*(g (m a)*g (m a)) ∂(iidMeasure Q n : Measure (Fin n → Message))) =
        (∫ m, w m*(g m*g m) ∂(Q : Measure Message)) at hh
      simpa only [pow_two, ite_true, add_sub_cancel] using hh
    · rw [iid_integral_weighted_pair Q n w g hw a b hab]
      simp [hab]
  simp_rw [hj]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma integral_avg {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → Spin → ℝ)
    (hf : ∀ i, Integrable (fun m => f m i) μ) :
    ∫ m, avg (f m) ∂μ = avg (fun i => ∫ m, f m i ∂μ) := by
  unfold avg
  rw [integral_div, integral_finsetSum Finset.univ (fun i _ => hf i)]

lemma integral_permMessage (Q : ProbabilityMeasure Message) (hQ : SpinSymmetric Q)
    (π : Equiv.Perm Spin) (f : Message → ℝ) (hf : Measurable f) :
    ∫ m, f (permMessage π m) ∂(Q : Measure Message) = ∫ m, f m ∂(Q : Measure Message) := by
  have he : Measure.map (permMessage π) (Q : Measure Message) = (Q : Measure Message) :=
    congrArg ProbabilityMeasure.toMeasure (hQ π)
  rw [← integral_map (continuous_permMessage π).measurable.aemeasurable hf.aestronglyMeasurable, he]

lemma symmetric_integral_coordinate (Q : ProbabilityMeasure Message) (hQ : SpinSymmetric Q)
    (f : Message → Spin → ℝ) (hf : ∀ i, Measurable (fun m => f m i))
    (he : ∀ (π : Equiv.Perm Spin) m i, f (permMessage π m) i = f m (π.symm i)) (i j : Spin) :
    ∫ m, f m i ∂(Q : Measure Message) = ∫ m, f m j ∂(Q : Measure Message) := by
  rw [← integral_permMessage Q hQ (Equiv.swap i j) (fun m => f m i) (hf i)]
  apply integral_congr_ae
  filter_upwards with m
  rw [he]
  simp

lemma mLog_perm (π : Equiv.Perm Spin) (m : Message) (i : Spin) :
    mLog (permMessage π m) i = mLog m (π.symm i) := rfl

lemma mCenteredLog_perm (π : Equiv.Perm Spin) (m : Message) (i : Spin) :
    mCenteredLog (permMessage π m) i = mCenteredLog m (π.symm i) := by
  simp only [mCenteredLog, mLog_perm, avg, Equiv.sum_comp π.symm]

lemma edgeMessage_perm (lam : ℝ) (h : Admissible lam) (π : Equiv.Perm Spin) (m : Message) :
    edgeMessage lam h (permMessage π m) = permMessage π (edgeMessage lam h m) := rfl

lemma integral_avg_eq_coordinate (Q : ProbabilityMeasure Message) (hQ : SpinSymmetric Q)
    (f : Message → Spin → ℝ) (hf : ∀ i, Continuous (fun m => f m i))
    (he : ∀ (π : Equiv.Perm Spin) m i, f (permMessage π m) i = f m (π.symm i)) (i : Spin) :
    ∫ m, avg (f m) ∂(Q : Measure Message) = ∫ m, f m i ∂(Q : Measure Message) := by
  rw [integral_avg _ _ (fun j => (hf j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hh (j : Spin) := symmetric_integral_coordinate Q hQ f (fun j => (hf j).measurable) he j i
  simp_rw [hh]
  simp [avg]

lemma integral_edge_centered (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : SpinSymmetric Q) (i : Spin) :
    ∫ m, edgeMessage lam h m i*mCenteredLog (edgeMessage lam h m) i ∂(Q : Measure Message) =
      2*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)) := by
  have hc (j : Spin) : Continuous (fun m => edgeMessage lam h m j*mCenteredLog (edgeMessage lam h m) j) :=
    (((continuous_apply j).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)).mul
      (continuous_mCenteredLog_edge lam h hl0 hl1 j)
  rw [← integral_avg_eq_coordinate Q hQ _ hc]
  · simp_rw [centeredLog_J]
    exact integral_const_mul _ _
  · intro π m j
    rw [edgeMessage_perm, mCenteredLog_perm]
    rfl

lemma integral_edge_centered_sq (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : SpinSymmetric Q) (i : Spin) :
    ∫ m, edgeMessage lam h m i*(mCenteredLog (edgeMessage lam h m) i)^2 ∂(Q : Measure Message) =
      2*(∫ m, entropyB (edgeMessage lam h m) ∂(Q : Measure Message)) := by
  have hc (j : Spin) : Continuous (fun m => edgeMessage lam h m j*(mCenteredLog (edgeMessage lam h m) j)^2) :=
    (((continuous_apply j).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)).mul
      ((continuous_mCenteredLog_edge lam h hl0 hl1 j).pow 2)
  rw [← integral_avg_eq_coordinate Q hQ _ hc]
  · have he (m : Message) : avg (fun j => edgeMessage lam h m j*(mCenteredLog (edgeMessage lam h m) j)^2) =
        2*entropyB (edgeMessage lam h m) := by unfold entropyB; ring
    simp_rw [he]
    exact integral_const_mul _ _
  · intro π m j
    rw [edgeMessage_perm, mCenteredLog_perm]
    rfl

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma weighted_avg_combine (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (v : Spin → ℝ) :
    normalizer lam h m * avg (fun i => combineMessage lam h m i*v i) =
      avg (fun i => productWeight lam h m i*v i) := by
  unfold avg
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, weighted_combineMessage]

lemma weighted_entropyJ (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    normalizer lam h m * entropyJ (combineMessage lam h m) =
      avg (fun i => productWeight lam h m i*mCenteredLog (combineMessage lam h m) i)/2 := by
  have hh := weighted_avg_combine lam h m (mCenteredLog (combineMessage lam h m))
  rw [centeredLog_J] at hh
  linarith

lemma weighted_entropyB (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    normalizer lam h m * entropyB (combineMessage lam h m) =
      avg (fun i => productWeight lam h m i*(mCenteredLog (combineMessage lam h m) i)^2)/2 := by
  rw [entropyB, ← mul_div_assoc, weighted_avg_combine]

noncomputable def edgeCoordinateMap (lam : ℝ) (h : Admissible lam) (i : Spin) : C(Message,ℝ) :=
  ⟨fun m => edgeMessage lam h m i, ((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)⟩

noncomputable def edgeCenteredMap (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (i : Spin) : C(Message,ℝ) :=
  ⟨fun m => mCenteredLog (edgeMessage lam h m) i, continuous_mCenteredLog_edge lam h hl0 hl1 i⟩

lemma integral_degree_entropyJ (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) :
    ∫ m : Fin n → Message, normalizer lam h m*entropyJ (combineMessage lam h m)
      ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      n*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)) := by
  simp_rw [weighted_entropyJ, centeredLog_combine lam h hl0 hl1]
  rw [integral_div, integral_avg]
  · have hi (i : Spin) :
        (∫ m : Fin n → Message, productWeight lam h m i*(∑ j, mCenteredLog (edgeMessage lam h (m j)) i)
          ∂(iidMeasure Q n : Measure (Fin n → Message))) =
        n*(2*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))) := by
      have hh := iid_integral_weighted_sum Q n (edgeCoordinateMap lam h i) (edgeCenteredMap lam h hl0 hl1 i)
        (integral_edgeMessage lam h Q hQ i)
      change _ = n*(∫ m, edgeMessage lam h m i*mCenteredLog (edgeMessage lam h m) i ∂(Q : Measure Message)) at hh
      rw [integral_edge_centered lam h hl0 hl1 Q hs i] at hh
      exact hh
    simp_rw [hi]
    simp [avg]
    ring
  · intro i
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_productWeight lam h n i).mul
      (continuous_finsetSum _ (fun j _ => (continuous_mCenteredLog_edge lam h hl0 hl1 i).comp (continuous_apply j)))

lemma integral_degree_entropyB (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) :
    ∫ m : Fin n → Message, normalizer lam h m*entropyB (combineMessage lam h m)
      ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      n*(∫ m, entropyB (edgeMessage lam h m) ∂(Q : Measure Message))+
      2*(n:ℝ)*(n-1)*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))^2 := by
  simp_rw [weighted_entropyB, centeredLog_combine lam h hl0 hl1]
  rw [integral_div, integral_avg]
  · have hi (i : Spin) :
        (∫ m : Fin n → Message, productWeight lam h m i*(∑ j, mCenteredLog (edgeMessage lam h (m j)) i)^2
          ∂(iidMeasure Q n : Measure (Fin n → Message))) =
        n*(2*(∫ m, entropyB (edgeMessage lam h m) ∂(Q : Measure Message)))+
        (n:ℝ)*(n-1)*(2*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)))^2 := by
      have hh := iid_integral_weighted_sum_sq Q n (edgeCoordinateMap lam h i) (edgeCenteredMap lam h hl0 hl1 i)
        (integral_edgeMessage lam h Q hQ i)
      change _ = n*(∫ m, edgeMessage lam h m i*(mCenteredLog (edgeMessage lam h m) i)^2 ∂(Q : Measure Message))+
        (n:ℝ)*(n-1)*(∫ m, edgeMessage lam h m i*mCenteredLog (edgeMessage lam h m) i ∂(Q : Measure Message))^2 at hh
      rw [integral_edge_centered lam h hl0 hl1 Q hs i, integral_edge_centered_sq lam h hl0 hl1 Q hs i] at hh
      exact hh
    simp_rw [hi]
    simp [avg]
    ring
  · intro i
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_productWeight lam h n i).mul
      ((continuous_finsetSum _ (fun j _ => (continuous_mCenteredLog_edge lam h hl0 hl1 i).comp (continuous_apply j))).pow 2)

lemma additive_entropyJ (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q) (hs : SpinSymmetric Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) :
    ∫ m, entropyJ m ∂(Q : Measure Message) = mean offspring (fun n : ℕ => (n:ℝ))*
      (∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)) := by
  rw [integral_fixedpoint offspring lam h Q hQ _ measurable_entropyJ
    (integrable_entropyJ_fixedpoint offspring lam h hl0 hl1 Q hQ hD)]
  simp_rw [integral_degree_entropyJ lam h hl0 hl1 Q hQ.1 hs]
  exact mean_mul_const _ _ _

lemma hasMean_factorialSecond {offspring : PMF ℕ} (hD2 : HasMean offspring (fun n : ℕ => (n:ℝ)^2)) :
    HasMean offspring (fun n : ℕ => (n:ℝ)*(n-1)) := by
  have hD := hasMean_of_square hD2
  exact (hD2.add (hD.mul_const (-1))).congr (fun n => by ring)

lemma additive_entropyB (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q) (hs : SpinSymmetric Q)
    (hD2 : HasMean offspring (fun n : ℕ => (n:ℝ)^2)) :
    ∫ m, entropyB m ∂(Q : Measure Message) = mean offspring (fun n : ℕ => (n:ℝ))*
      (∫ m, entropyB (edgeMessage lam h m) ∂(Q : Measure Message))+
      2*mean offspring (fun n : ℕ => (n:ℝ)*(n-1))*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))^2 := by
  rw [integral_fixedpoint offspring lam h Q hQ _ measurable_entropyB
    (integrable_entropyB_fixedpoint offspring lam h hl0 hl1 Q hQ hD2)]
  simp_rw [integral_degree_entropyB lam h hl0 hl1 Q hQ.1 hs]
  have he (n : ℕ) :
      (n:ℝ)*(∫ m, entropyB (edgeMessage lam h m) ∂(Q : Measure Message))+
      2*(n:ℝ)*(n-1)*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))^2 =
      (n:ℝ)*(∫ m, entropyB (edgeMessage lam h m) ∂(Q : Measure Message))+
      ((n:ℝ)*(n-1))*(2*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))^2) := by ring
  simp_rw [he]
  rw [mean_add ((hasMean_of_square hD2).mul_const _) ((hasMean_factorialSecond hD2).mul_const _),
    mean_mul_const, mean_mul_const]
  ring

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

noncomputable def correlationEntropy (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (n : ℕ) : ℝ :=
  ∫ m : Fin n → Message, normalizer lam h m * Real.log (normalizer lam h m)
    ∂(iidMeasure Q n : Measure (Fin n → Message))

lemma continuous_log_normalizer (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (n : ℕ) :
    Continuous (fun m : Fin n → Message => Real.log (normalizer lam h m)) :=
  (continuous_normalizer lam h n).log (fun m => ne_of_gt (normalizer_pos lam h hl0 hl1 m))

lemma continuous_entropyI_combine (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (n : ℕ) :
    Continuous (fun m : Fin n → Message => entropyI (combineMessage lam h m)) := by
  apply continuous_avg
  intro i
  have hc := ((continuous_apply i).comp continuous_subtype_val).comp
    (continuous_combineMessage_positive lam h hl0 hl1 n)
  exact hc.mul (hc.log (fun m => ne_of_gt (combineMessage_pos lam h hl0 hl1 m i)))

lemma weighted_entropyI (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) :
    normalizer lam h m * entropyI (combineMessage lam h m) =
      avg (fun i => productWeight lam h m i * (∑ j, mLog (edgeMessage lam h (m j)) i)) -
      normalizer lam h m * Real.log (normalizer lam h m) := by
  rw [entropyI, weighted_avg_combine]
  simp only [mLog, log_combineMessage lam h hl0 hl1, Radial.avg_expand]
  have hn : normalizer lam h m = (productWeight lam h m 0+productWeight lam h m 1+productWeight lam h m 2)/3 := by
    simp [normalizer, Fin.sum_univ_succ]; ring
  rw [hn]
  ring

noncomputable def edgeLogMap (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (i : Spin) : C(Message,ℝ) :=
  ⟨fun m => mLog (edgeMessage lam h m) i, continuous_mLog_edge lam h hl0 hl1 i⟩

lemma integral_degree_entropyI (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (n : ℕ) :
    ∫ m : Fin n → Message, normalizer lam h m*entropyI (combineMessage lam h m)
      ∂(iidMeasure Q n : Measure (Fin n → Message)) =
      n*(∫ m, entropyI (edgeMessage lam h m) ∂(Q : Measure Message))-correlationEntropy lam h Q n := by
  have hc (i : Spin) : Continuous (fun m : Fin n → Message => productWeight lam h m i *
      (∑ j, mLog (edgeMessage lam h (m j)) i)) :=
    (continuous_productWeight lam h n i).mul
      (continuous_finsetSum _ (fun j _ => (continuous_mLog_edge lam h hl0 hl1 i).comp (continuous_apply j)))
  have hz : Continuous (fun m : Fin n → Message => normalizer lam h m*Real.log (normalizer lam h m)) :=
    (continuous_normalizer lam h n).mul (continuous_log_normalizer lam h hl0 hl1 n)
  simp_rw [weighted_entropyI lam h hl0 hl1]
  rw [integral_sub ((continuous_avg _ hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hz.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  congr 1
  rw [integral_avg _ _ (fun i => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hi (i : Spin) := iid_integral_weighted_sum Q n (edgeCoordinateMap lam h i) (edgeLogMap lam h hl0 hl1 i)
    (integral_edgeMessage lam h Q hQ i)
  change ∀ i : Spin, (∫ m : Fin n → Message, productWeight lam h m i*(∑ j, mLog (edgeMessage lam h (m j)) i)
    ∂(iidMeasure Q n : Measure (Fin n → Message))) = n*(∫ m, edgeMessage lam h m i*mLog (edgeMessage lam h m) i
    ∂(Q : Measure Message)) at hi
  simp_rw [hi]
  simp only [entropyI]
  rw [integral_avg]
  · simp only [Radial.avg_expand]; ring
  · intro i
    exact (((edgeCoordinateMap lam h i).continuous).mul (continuous_mLog_edge lam h hl0 hl1 i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma correlationEntropy_nonneg (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (n : ℕ) : 0 ≤ correlationEntropy lam h Q n := by
  have hc : Continuous (fun m : Fin n → Message => normalizer lam h m*Real.log (normalizer lam h m)) :=
    (continuous_normalizer lam h n).mul (continuous_log_normalizer lam h hl0 hl1 n)
  have hi : Integrable (normalizer lam h) (iidMeasure Q n : Measure (Fin n → Message)) := (continuous_normalizer lam h n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs (m : Fin n → Message) : normalizer lam h m-1 ≤ normalizer lam h m*Real.log (normalizer lam h m) := by
    have hz := normalizer_pos lam h hl0 hl1 m
    have hh := Real.one_sub_inv_le_log_of_pos hz
    have hm := mul_le_mul_of_nonneg_left hh hz.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hz)] at hm
    exact hm
  have hh := integral_mono (hi.sub (integrable_const 1)) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hs
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi (integrable_const 1), integral_normalizer lam h Q hQ n] at hh
  simpa [correlationEntropy] using hh

lemma correlationEntropy_bound (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (n : ℕ) : |correlationEntropy lam h Q n| ≤ n*edgeLogBound lam := by
  have hb (m : Fin n → Message) : |Real.log (normalizer lam h m)| ≤ n*edgeLogBound lam :=
    abs_log_of_bounds lam hl0 hl1 n _ (normalizer_bounds lam h hl0 hl1 m).1 (normalizer_bounds lam h hl0 hl1 m).2
  have hc : Continuous (fun m : Fin n → Message => normalizer lam h m*Real.log (normalizer lam h m)) :=
    (continuous_normalizer lam h n).mul (continuous_log_normalizer lam h hl0 hl1 n)
  have hi : Integrable (fun m : Fin n → Message => |normalizer lam h m*Real.log (normalizer lam h m)|)
      (iidMeasure Q n : Measure (Fin n → Message)) := hc.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun m : Fin n → Message => normalizer lam h m*(n*edgeLogBound lam))
      (iidMeasure Q n : Measure (Fin n → Message)) := ((continuous_normalizer lam h n).mul_const (n*edgeLogBound lam)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  calc
    |correlationEntropy lam h Q n| ≤ ∫ m, |normalizer lam h m*Real.log (normalizer lam h m)|
      ∂(iidMeasure Q n : Measure (Fin n → Message)) := abs_integral_le_integral_abs
    _ ≤ ∫ m, normalizer lam h m*(n*edgeLogBound lam) ∂(iidMeasure Q n : Measure (Fin n → Message)) := by
      apply integral_mono hi hj
      intro m
      dsimp only
      rw [abs_mul, abs_of_nonneg (normalizer_nonneg lam h m)]
      exact mul_le_mul_of_nonneg_left (hb m) (normalizer_nonneg lam h m)
    _ = _ := by rw [integral_mul_const, integral_normalizer lam h Q hQ n, one_mul]

lemma hasMean_correlationEntropy (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message) (hQ : Balanced Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) : HasMean offspring (correlationEntropy lam h Q) := by
  apply HasMean.of_abs
  exact (hD.mul_const (edgeLogBound lam)).mono (fun n => abs_nonneg _)
    (correlationEntropy_bound lam h hl0 hl1 Q hQ)

lemma additive_entropyI (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) :
    ∫ m, entropyI m ∂(Q : Measure Message) = mean offspring (fun n : ℕ => (n:ℝ))*
      (∫ m, entropyI (edgeMessage lam h m) ∂(Q : Measure Message))-mean offspring (correlationEntropy lam h Q) := by
  rw [integral_fixedpoint offspring lam h Q hQ _ measurable_entropyI
    (integrable_entropyI_fixedpoint offspring lam h hl0 hl1 Q hQ hD)]
  simp_rw [integral_degree_entropyI lam h hl0 hl1 Q hQ.1]
  have he (n : ℕ) : (n:ℝ)*(∫ m, entropyI (edgeMessage lam h m) ∂(Q : Measure Message))-correlationEntropy lam h Q n =
    (n:ℝ)*(∫ m, entropyI (edgeMessage lam h m) ∂(Q : Measure Message))+correlationEntropy lam h Q n*(-1) := by ring
  simp_rw [he]
  rw [mean_add (hD.mul_const _) ((hasMean_correlationEntropy offspring lam h hl0 hl1 Q hQ.1 hD).mul_const _),
    mean_mul_const, mean_mul_const]
  ring

lemma entropy_identity (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q) (hs : SpinSymmetric Q)
    (hD2 : HasMean offspring (fun n : ℕ => (n:ℝ)^2)) :
    (∫ m, entropyF m ∂(Q : Measure Message)) - mean offspring (fun n : ℕ => (n:ℝ))*
      (∫ m, entropyF (edgeMessage lam h m) ∂(Q : Measure Message)) =
      -3*mean offspring (correlationEntropy lam h Q) +
      (8/5:ℝ)*mean offspring (fun n : ℕ => (n:ℝ)*(n-1))*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))^2 := by
  have hD := hasMean_of_square hD2
  have hi := integrable_entropyI_fixedpoint offspring lam h hl0 hl1 Q hQ hD
  have hj := integrable_entropyJ_fixedpoint offspring lam h hl0 hl1 Q hQ hD
  have hb := integrable_entropyB_fixedpoint offspring lam h hl0 hl1 Q hQ hD2
  have hie : Integrable (fun m => entropyI (edgeMessage lam h m)) (Q : Measure Message) := (continuous_entropyI_edge lam h hl0 hl1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hje : Integrable (fun m => entropyJ (edgeMessage lam h m)) (Q : Measure Message) := (continuous_entropyJ_edge lam h hl0 hl1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbe : Integrable (fun m => entropyB (edgeMessage lam h m)) (Q : Measure Message) := (continuous_entropyB_edge lam h hl0 hl1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlin (f g k : Message → ℝ) (hf : Integrable f (Q : Measure Message))
      (hg : Integrable g (Q : Measure Message)) (hk : Integrable k (Q : Measure Message)) :
      (∫ m, 3*f m-2*g m+(4/5:ℝ)*k m ∂(Q : Measure Message)) =
        3*(∫ m, f m ∂(Q : Measure Message))-2*(∫ m, g m ∂(Q : Measure Message))+
        (4/5:ℝ)*(∫ m, k m ∂(Q : Measure Message)) := by
    have hsub : Integrable (fun m => 3*f m-2*g m) (Q : Measure Message) := (hf.const_mul 3).sub (hg.const_mul 2)
    rw [integral_add hsub (hk.const_mul (4/5:ℝ)), integral_sub (hf.const_mul 3) (hg.const_mul 2)]
    simp only [integral_const_mul]
  simp only [entropyF]
  rw [hlin _ _ _ hi hj hb, hlin _ _ _ hie hje hbe]
  rw [additive_entropyI offspring lam h hl0 hl1 Q hQ hD,
    additive_entropyJ offspring lam h hl0 hl1 Q hQ hs hD,
    additive_entropyB offspring lam h hl0 hl1 Q hQ hs hD2]
  ring

end ThreeState

end OAI
