import Mathlib
import OAI.Probability.ThreeState.DegreePosterior

namespace OAI

/-! Quadratic projections, covariance and truncated correlation estimates. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma symAvg_deviation_mul (a : Message) (i j : Spin) :
    symAvg (fun m => messageDeviation m i*messageDeviation m j) a =
      (if i=j then 2 else -1)*messageX a := by
  fin_cases i <;> fin_cases j <;>
    norm_num [symAvg, symPerm, Fin.sum_univ_succ, messageDeviation,
      Radial.avg_expand, permMessage, Equiv.swap_apply_def, Equiv.trans_apply,
      Equiv.symm_trans_apply, Fin.ext_iff, messageX, Radial.momentX] <;>
    (try rw [message_last a]) <;> ring

lemma continuous_messageDeviation (i : Spin) : Continuous (fun m => messageDeviation m i) :=
  ((continuous_apply i).comp continuous_subtype_val).sub continuous_const

lemma integral_deviation (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (i : Spin) :
    (∫ m, messageDeviation m i ∂(Q : Measure Message)) = 0 := by
  change (∫ m : Message, m i-1 ∂(Q : Measure Message)) = 0
  have hi : Integrable (fun m : Message => m i) (Q : Measure Message) :=
    integrable_continuous_message Q (coordinateMap i).continuous
  rw [integral_sub hi (integrable_const (1:ℝ)), hQ i]
  simp

lemma integral_deviation_mul (Q : ProbabilityMeasure Message) (hs : SpinSymmetric Q) (i j : Spin) :
    (∫ m, messageDeviation m i*messageDeviation m j ∂(Q : Measure Message)) =
      (if i=j then 2 else -1)*posteriorMu Q := by
  rw [← integral_symAvg Q hs (fun m => messageDeviation m i*messageDeviation m j) ((continuous_messageDeviation i).mul (continuous_messageDeviation j))]
  simp only [symAvg_deviation_mul, integral_const_mul, posteriorMu]

noncomputable def edgeDeviationMap (lam : ℝ) (h : Admissible lam) (i : Spin) : C(Message,ℝ) :=
  ⟨fun m => messageDeviation (edgeMessage lam h m) i,
    (continuous_messageDeviation i).comp (continuous_edgeMessage lam h)⟩

lemma edge_deviation (lam : ℝ) (h : Admissible lam) (m : Message) (i : Spin) :
    messageDeviation (edgeMessage lam h m) i = lam*messageDeviation m i := by
  change 1+lam*(m i-1)-1 = lam*(m i-1)
  ring

lemma integral_edge_covariance (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (hs : SpinSymmetric Q) (i j : Spin) :
    (∫ m, edgeMessage lam h m i*messageDeviation (edgeMessage lam h m) j ∂(Q : Measure Message)) =
      lam^2*posteriorMu Q*(if i=j then 2 else -1) := by
  have he (m : Message) : edgeMessage lam h m i*messageDeviation (edgeMessage lam h m) j =
      lam*messageDeviation m j + lam^2*(messageDeviation m i*messageDeviation m j) := by
    rw [edge_deviation]
    change (1+lam*(m i-1))*(lam*(m j-1)) = _
    simp only [messageDeviation]
    ring
  simp_rw [he]
  have hi : Integrable (fun m => lam*messageDeviation m j) (Q : Measure Message) :=
    (integrable_continuous_message Q (continuous_messageDeviation j)).const_mul _
  have hj : Integrable (fun m => lam^2*(messageDeviation m i*messageDeviation m j)) (Q : Measure Message) :=
    (integrable_continuous_message Q ((continuous_messageDeviation i).mul (continuous_messageDeviation j))).const_mul _
  rw [integral_add hi hj,
    integral_const_mul, integral_const_mul, integral_deviation Q hQ,
    integral_deviation_mul Q hs]
  ring

lemma integral_edge_deviation_sq (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hs : SpinSymmetric Q) (i : Spin) :
    (∫ m, (messageDeviation (edgeMessage lam h m) i)^2 ∂(Q : Measure Message)) = 2*lam^2*posteriorMu Q := by
  have he (m : Message) : (messageDeviation (edgeMessage lam h m) i)^2 =
      lam^2*(messageDeviation m i*messageDeviation m i) := by rw [edge_deviation]; ring
  simp_rw [he]
  rw [integral_const_mul, integral_deviation_mul Q hs]
  simp only [ite_true]
  ring

lemma avg_swap (f : Spin → Spin → ℝ) : avg (fun i => avg (f i)) = avg (fun j => avg (fun i => f i j)) := by
  simp only [Radial.avg_expand]
  ring
lemma avg_add (a b : Spin → ℝ) : avg (fun i => a i+b i) = avg a+avg b := by
  simp only [Radial.avg_expand]
  ring
lemma avg_mul_const (a : Spin → ℝ) (c : ℝ) : avg (fun i => a i*c) = avg a*c := by
  simp only [Radial.avg_expand]
  ring
lemma avg_const_mul (c : ℝ) (a : Spin → ℝ) : avg (fun i => c*a i) = c*avg a := by
  simp only [Radial.avg_expand]
  ring
lemma avg_covariance_coeff (j : Spin) : avg (fun i : Spin => (if i=j then (2:ℝ) else -1)^2) = 2 := by
  have he (i : Spin) : (if i=j then (2:ℝ) else -1)^2 = 1+(if i=j then (3:ℝ) else 0) := by
    split_ifs <;> norm_num
  simp only [he, avg, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  norm_num

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

noncomputable def branchSum (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) : ℝ :=
  ∑ j, messageDeviation (edgeMessage lam h (m j)) i
lemma continuous_branchSum (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    Continuous (fun m : Fin n → Message => branchSum lam h m i) := by
  apply continuous_finsetSum
  intro j _
  exact ((continuous_messageDeviation i).comp (continuous_edgeMessage lam h)).comp (continuous_apply j)
lemma avg_branchSum (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    avg (branchSum lam h m) = 0 := by
  have he : avg (branchSum lam h m) = ∑ j, avg (messageDeviation (edgeMessage lam h (m j))) := by
    simp only [branchSum, Radial.avg_expand]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [he]
  simp only [avg_messageDeviation, Finset.sum_const_zero]

lemma weighted_deviation_branchSum (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    normalizer lam h m * avg (fun i => messageDeviation (combineMessage lam h m) i*branchSum lam h m i) =
      avg (fun i => productWeight lam h m i*branchSum lam h m i) := by
  have hh := weighted_avg_combine lam h m (branchSum lam h m)
  have hz := avg_branchSum lam h m
  simp only [messageDeviation, Radial.avg_expand] at *
  nlinarith only [hh, mul_eq_zero_of_right (normalizer lam h m) hz]

lemma integral_projection_cross (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) :
    (∫ m : Fin n → Message, normalizer lam h m *
      (avg (fun i => messageDeviation (combineMessage lam h m) i*branchSum lam h m i)/2)
        ∂(iidMeasure Q n : Measure (Fin n → Message))) = n*(lam^2*posteriorMu Q) := by
  have he (m : Fin n → Message) : normalizer lam h m *
      (avg (fun i => messageDeviation (combineMessage lam h m) i*branchSum lam h m i)/2) =
      avg (fun i => productWeight lam h m i*branchSum lam h m i)/2 := by
    rw [← mul_div_assoc, weighted_deviation_branchSum]
  simp_rw [he]
  rw [integral_div, integral_avg]
  · have hi (i : Spin) :
        (∫ m : Fin n → Message, productWeight lam h m i*branchSum lam h m i
          ∂(iidMeasure Q n : Measure (Fin n → Message))) = (n:ℝ)*(lam^2*posteriorMu Q*2) := by
      have hh := iid_integral_weighted_sum Q n (edgeCoordinateMap lam h i) (edgeDeviationMap lam h i)
        (integral_edgeMessage lam h Q hQ i)
      change _ = n*(∫ m, edgeMessage lam h m i*messageDeviation (edgeMessage lam h m) i ∂(Q : Measure Message)) at hh
      rw [integral_edge_covariance lam h Q hQ hs] at hh
      simpa only [edgeCoordinateMap, edgeDeviationMap, ContinuousMap.coe_mk, productWeight, branchSum, ite_true] using hh
    simp_rw [hi]
    simp [Radial.avg_expand]
    ring
  · intro i
    exact ((continuous_productWeight lam h n i).mul (continuous_branchSum lam h n i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma avg_integral_edge_sq (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hs : SpinSymmetric Q) (i : Spin) :
    avg (fun k => ∫ m, edgeMessage lam h m k*(messageDeviation (edgeMessage lam h m) i)^2 ∂(Q : Measure Message)) =
      2*lam^2*posteriorMu Q := by
  rw [← integral_avg]
  · have he (m : Message) : avg (fun k => edgeMessage lam h m k*(messageDeviation (edgeMessage lam h m) i)^2) =
        (messageDeviation (edgeMessage lam h m) i)^2 := by
      rw [avg_mul_const, average_message, one_mul]
    simp_rw [he]
    exact integral_edge_deviation_sq lam h Q hs i
  · intro k
    exact integrable_continuous_message Q ((edgeCoordinateMap lam h k).continuous.mul ((edgeDeviationMap lam h i).continuous.pow 2))

lemma integral_projection_variance_coordinate (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) (i : Spin) :
    (∫ m : Fin n → Message, normalizer lam h m*(branchSum lam h m i)^2
      ∂(iidMeasure Q n : Measure (Fin n → Message))) =
      2*((n:ℝ)*(lam^2*posteriorMu Q)+(n:ℝ)*(n-1)*(lam^2*posteriorMu Q)^2) := by
  have he (m : Fin n → Message) : normalizer lam h m*(branchSum lam h m i)^2 =
      avg (fun k => productWeight lam h m k*(branchSum lam h m i)^2) := (avg_mul_const _ _).symm
  simp_rw [he]
  rw [integral_avg]
  · have hi (k : Spin) :
        (∫ m : Fin n → Message, productWeight lam h m k*(branchSum lam h m i)^2
          ∂(iidMeasure Q n : Measure (Fin n → Message))) =
        (n:ℝ)*(∫ m, edgeMessage lam h m k*(messageDeviation (edgeMessage lam h m) i)^2 ∂(Q : Measure Message))+
        ((n:ℝ)*(n-1)*(lam^2*posteriorMu Q)^2)*(if k=i then (2:ℝ) else -1)^2 := by
      have hh := iid_integral_weighted_sum_sq Q n (edgeCoordinateMap lam h k) (edgeDeviationMap lam h i)
        (integral_edgeMessage lam h Q hQ k)
      change _ = n*(∫ m, edgeMessage lam h m k*(messageDeviation (edgeMessage lam h m) i)^2 ∂(Q : Measure Message))+
        (n:ℝ)*(n-1)*(∫ m, edgeMessage lam h m k*messageDeviation (edgeMessage lam h m) i ∂(Q : Measure Message))^2 at hh
      rw [integral_edge_covariance lam h Q hQ hs] at hh
      change (∫ m : Fin n → Message, productWeight lam h m k*(branchSum lam h m i)^2
        ∂(iidMeasure Q n : Measure (Fin n → Message))) = _ at hh
      rw [hh]
      ring
    simp_rw [hi]
    rw [avg_add, avg_const_mul, avg_const_mul, avg_integral_edge_sq lam h Q hs, avg_covariance_coeff]
    ring
  · intro k
    exact ((continuous_productWeight lam h n k).mul ((continuous_branchSum lam h n i).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integral_projection_variance (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) :
    (∫ m : Fin n → Message, normalizer lam h m*(avg (fun i => (branchSum lam h m i)^2)/2)
      ∂(iidMeasure Q n : Measure (Fin n → Message))) =
      (n:ℝ)*(lam^2*posteriorMu Q)+(n:ℝ)*(n-1)*(lam^2*posteriorMu Q)^2 := by
  have he (m : Fin n → Message) : normalizer lam h m*(avg (fun i => (branchSum lam h m i)^2)/2) =
      avg (fun i => normalizer lam h m*(branchSum lam h m i)^2)/2 := by rw [avg_const_mul]; ring
  simp_rw [he]
  rw [integral_div, integral_avg]
  · simp_rw [integral_projection_variance_coordinate lam h Q hQ hs]
    simp [Radial.avg_expand]
    ring
  · intro i
    exact ((continuous_normalizer lam h n).mul ((continuous_branchSum lam h n i).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma weighted_vector_quadratic {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (M : Measure α) [IsFiniteMeasure M]
    (w : α → ℝ) (hw : Continuous w) (hw0 : ∀ a, 0 ≤ w a)
    (f g : α → Spin → ℝ) (hf : ∀ i, Continuous (fun a => f a i)) (hg : ∀ i, Continuous (fun a => g a i)) (t : ℝ) :
    0 ≤ (∫ a, w a*(avg (fun i => (f a i)^2)/2) ∂M)*t^2-
      2*(∫ a, w a*(avg (fun i => f a i*g a i)/2) ∂M)*t+
      (∫ a, w a*(avg (fun i => (g a i)^2)/2) ∂M) := by
  have hA : Integrable (fun a => w a*(avg (fun i => (f a i)^2)/2)) M :=
    (hw.mul ((continuous_avg _ (fun i => (hf i).pow 2)).div_const 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun a => w a*(avg (fun i => (g a i)^2)/2)) M :=
    (hw.mul ((continuous_avg _ (fun i => (hg i).pow 2)).div_const 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hC : Integrable (fun a => w a*(avg (fun i => f a i*g a i)/2)) M :=
    (hw.mul ((continuous_avg _ (fun i => (hf i).mul (hg i))).div_const 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : 0 ≤ ∫ a, w a*(avg (fun i => (t*f a i-g a i)^2)/2) ∂M := by
    apply integral_nonneg
    intro a
    apply mul_nonneg (hw0 a)
    rw [Radial.avg_expand]
    positivity
  have he (a : α) : w a*(avg (fun i => (t*f a i-g a i)^2)/2) =
      t^2*(w a*(avg (fun i => (f a i)^2)/2))+(-2*t)*(w a*(avg (fun i => f a i*g a i)/2))+
        w a*(avg (fun i => (g a i)^2)/2) := by simp only [Radial.avg_expand]; ring
  simp_rw [he] at hp
  have hAC : Integrable (fun a => t^2*(w a*(avg (fun i => (f a i)^2)/2))+
      (-2*t)*(w a*(avg (fun i => f a i*g a i)/2))) M := (hA.const_mul _).add (hC.const_mul _)
  rw [integral_add hAC hB,
    integral_add (hA.const_mul _) (hC.const_mul _), integral_const_mul, integral_const_mul] at hp
  nlinarith only [hp]

lemma degree_projection_quadratic (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) (t : ℝ) :
    0 ≤ posteriorMu (degreePosterior lam h Q hQ n)*t^2-2*((n:ℝ)*(lam^2*posteriorMu Q))*t+
      ((n:ℝ)*(lam^2*posteriorMu Q)+(n:ℝ)*(n-1)*(lam^2*posteriorMu Q)^2) := by
  have hh := weighted_vector_quadratic (iidMeasure Q n : Measure (Fin n → Message)) (normalizer lam h)
    (continuous_normalizer lam h n) (normalizer_nonneg lam h)
    (fun m i => messageDeviation (combineMessage lam h m) i) (branchSum lam h)
    (fun i => (continuous_messageDeviation i).comp (continuous_combineMessage_positive lam h hl0 hl1 n))
    (continuous_branchSum lam h n) t
  rw [integral_projection_cross lam h Q hQ hs, integral_projection_variance lam h Q hQ hs] at hh
  have he : (∫ m : Fin n → Message, normalizer lam h m *
      (avg (fun i => (messageDeviation (combineMessage lam h m) i)^2)/2)
      ∂(iidMeasure Q n : Measure (Fin n → Message))) = posteriorMu (degreePosterior lam h Q hQ n) := by
    change _ = ∫ m, messageX m ∂degreeOutput lam h Q n
    rw [integral_degreeOutput lam h Q n messageX continuous_messageX.measurable]
    rfl
  rwa [he] at hh

lemma degree_projection (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q) (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)*(lam^2*posteriorMu Q)/(1+((n:ℝ)-1)*(lam^2*posteriorMu Q)) ≤
      posteriorMu (degreePosterior lam h Q hQ n) := by
  let beta := lam^2*posteriorMu Q
  have hb : 0 ≤ beta := mul_nonneg (sq_nonneg _) (posteriorMu_nonneg Q)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hd : 0<1+((n:ℝ)-1)*beta := by positivity
  by_cases hb0 : beta=0
  · change (n:ℝ)*beta/(1+((n:ℝ)-1)*beta) ≤ _
    simp only [hb0, mul_zero, zero_div]
    exact posteriorMu_nonneg _
  · have hbpos : 0<beta := lt_of_le_of_ne hb (Ne.symm hb0)
    have hnb : 0<(n:ℝ)*beta := mul_pos hn0 hbpos
    have hp := degree_projection_quadratic lam h hl0 hl1 Q hQ hs n
    have hdisc := discrim_le_zero (show ∀ t, 0 ≤ posteriorMu (degreePosterior lam h Q hQ n)*(t*t)+
        (-2*((n:ℝ)*beta))*t+((n:ℝ)*beta+(n:ℝ)*(n-1)*beta^2) by intro t; simpa [beta, pow_two, sub_eq_add_neg] using hp t)
    simp only [discrim] at hdisc
    change (n:ℝ)*beta/(1+((n:ℝ)-1)*beta) ≤ _
    apply (div_le_iff₀ hd).mpr
    apply (mul_le_mul_iff_right₀ hnb).mp
    nlinarith only [hdisc]

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma truncated_quadratic_lower {A B L u C : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hLu : L ≤ u) (hC : 0 ≤ C) (hCu : A*u-B*Real.sqrt u ≤ C) :
    A*L-B*Real.sqrt L ≤ C := by
  by_cases ht : A*L-B*Real.sqrt L ≤ 0
  · exact ht.trans hC
  · have hl := Real.sq_sqrt hL
    have hu := Real.sq_sqrt (hL.trans hLu)
    have hroot := Real.sqrt_le_sqrt hLu
    have hf : 0 ≤ A*Real.sqrt L-B := by
      by_contra hh
      have hp : Real.sqrt L*(A*Real.sqrt L-B) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (le_of_lt (lt_of_not_ge hh))
      apply ht
      nlinarith only [hp, congrArg (fun x => A*x) hl]
    have hg : 0 ≤ A*(Real.sqrt u+Real.sqrt L)-B := by
      nlinarith only [hf, mul_nonneg hA (Real.sqrt_nonneg u)]
    have hp := mul_nonneg (sub_nonneg.mpr hroot) hg
    nlinarith only [hp, congrArg (fun x => A*x) hl, congrArg (fun x => A*x) hu, hCu]

noncomputable def pairCorrelation (lam : ℝ) (h : Admissible lam) (Q P : ProbabilityMeasure Message) : ℝ :=
  ∫ a, pairIncrement lam h Q a ∂(P : Measure Message)

lemma pairCorrelation_nonneg (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q P : ProbabilityMeasure Message) (hQ : Balanced Q) : 0 ≤ pairCorrelation lam h Q P :=
  integral_nonneg (pairIncrement_nonneg lam h hl0 hl1 Q hQ)

lemma pairCorrelation_lower (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q P : ProbabilityMeasure Message) (hs : SpinSymmetric Q) :
    3*lam^2*posteriorMu Q*posteriorMu P-lam^3*posteriorEta Q*posteriorEta P ≤ 3*pairCorrelation lam h Q P := by
  have hi : Integrable (fun a => lam^2*posteriorMu Q*messageX a-lam^3*posteriorEta Q*messageY a/3) (P : Measure Message) :=
    ((integrable_continuous_message P continuous_messageX).const_mul _).sub
      (((integrable_continuous_message P continuous_messageY).const_mul _).div_const _)
  have hh := integral_mono hi (integrable_continuous_message P (continuous_pairIncrement lam h hl0 hl1 Q))
    (pairIncrement_lower lam h hl0 hl1 Q hs)
  have hix : Integrable (fun a => lam^2*posteriorMu Q*messageX a) (P : Measure Message) :=
    (integrable_continuous_message P continuous_messageX).const_mul _
  have hiy : Integrable (fun a => lam^3*posteriorEta Q*messageY a/3) (P : Measure Message) :=
    ((integrable_continuous_message P continuous_messageY).const_mul _).div_const _
  rw [integral_sub hix hiy, integral_div, integral_const_mul, integral_const_mul] at hh
  change lam^2*posteriorMu Q*posteriorMu P-lam^3*posteriorEta Q*posteriorEta P/3 ≤ pairCorrelation lam h Q P at hh
  linarith

lemma eta_product_lower_control (Q P : ProbabilityMeasure Message) (he : 0 ≤ posteriorEta Q)
    (hn : posteriorNu P ≤ posteriorNu Q) :
    posteriorEta Q*posteriorEta P ≤ Real.sqrt (posteriorMu Q)*posteriorNu Q*Real.sqrt (posteriorMu P) := by
  have hQ := posteriorEta_upper Q
  have hP := posteriorEta_upper P
  rw [Real.sqrt_mul (posteriorMu_nonneg Q)] at hQ
  rw [Real.sqrt_mul (posteriorMu_nonneg P)] at hP
  have hP' : posteriorEta P ≤ Real.sqrt (posteriorMu P)*Real.sqrt (posteriorNu Q) :=
    hP.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn) (Real.sqrt_nonneg _))
  have hh : posteriorEta Q*posteriorEta P ≤
      (Real.sqrt (posteriorMu Q)*Real.sqrt (posteriorNu Q))*(Real.sqrt (posteriorMu P)*Real.sqrt (posteriorNu Q)) :=
    (mul_le_mul_of_nonneg_left hP' he).trans
      (mul_le_mul_of_nonneg_right hQ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have heq : (Real.sqrt (posteriorMu Q)*Real.sqrt (posteriorNu Q))*(Real.sqrt (posteriorMu P)*Real.sqrt (posteriorNu Q)) =
      Real.sqrt (posteriorMu Q)*posteriorNu Q*Real.sqrt (posteriorMu P) := by
    calc
      _ = Real.sqrt (posteriorMu Q)*(Real.sqrt (posteriorNu Q))^2*Real.sqrt (posteriorMu P) := by ring
      _ = _ := by rw [Real.sq_sqrt (posteriorNu_nonneg Q)]
  rwa [heq] at hh

lemma pairCorrelation_truncated (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q P : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q)
    (he : 0 ≤ posteriorEta Q) (hn : posteriorNu P ≤ posteriorNu Q) {L : ℝ} (hL : 0 ≤ L) (hLP : L ≤ posteriorMu P) :
    3*lam^2*posteriorMu Q*L-lam^3*Real.sqrt (posteriorMu Q)*posteriorNu Q*Real.sqrt L ≤
      3*pairCorrelation lam h Q P := by
  have hm := posteriorMu_nonneg Q
  have hh := pairCorrelation_lower lam h hl0 hl1 Q P hs
  have hg := mul_le_mul_of_nonneg_left (eta_product_lower_control Q P he hn) (pow_nonneg hl0 3)
  apply truncated_quadratic_lower (show 0 ≤ 3*lam^2*posteriorMu Q by positivity) hL hLP
    (mul_nonneg (by norm_num) (pairCorrelation_nonneg lam h hl0 hl1 Q P hQ))
  nlinarith only [hh,hg]

end ThreeState

end OAI
