import Mathlib
import OAI.Probability.JammingConcavity.RowBoundedTerminal

namespace OAI

/-! Gaussian Derivative Martingale. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma rowTiltStep_affine {f h : ℝ → ℝ} {a T x : ℝ}
    (hw : Integrable (fun z => Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (hh : Integrable (fun z => h (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (A B : ℝ) : rowTiltStep a T f x (fun y => A*h y+B) = A*rowTiltStep a T f x h+B := by
  have hZ := (integral_exp_pos hw).ne'
  simp only [rowTiltStep]
  simp_rw [add_mul, mul_assoc]
  rw [integral_add (hh.const_mul A) (hw.const_mul B), integral_const_mul, integral_const_mul]
  field_simp

lemma rowTiltStep_linear {f h k : ℝ → ℝ} {a T x : ℝ}
    (hh : Integrable (fun z => h (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (hk : Integrable (fun z => k (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (A B : ℝ) : rowTiltStep a T f x (fun y => A*h y+B*k y) =
      A*rowTiltStep a T f x h+B*rowTiltStep a T f x k := by
  simp only [rowTiltStep]
  simp_rw [add_mul, mul_assoc]
  rw [integral_add (hh.const_mul A) (hk.const_mul B), integral_const_mul, integral_const_mul]
  ring

lemma decoratedGaussian_ofReal {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (m : ℝ) (ms : List ℝ) (hms : ∀ a ∈ m::ms, 0 < a ∧ a < 1)
    (d : ℕ → ℝ≥0) {h : ℝ → ℝ} (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y, |h y| ≤ B) (hn : ∀ y, 0 ≤ h y) (x : ℝ) :
    (∫⁻ a, ENNReal.ofReal (h (x+a)) ∂decoratedTransition m ms (rowGaussianLaw d) u x) =
      ENNReal.ofReal (rowTiltStep m (d 0) (gaussianRowComposition
        (rowGaussianBlocks ms (fun j => d (j+1))) u) x h) := by
  have ht : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => hms a (by simp [ha])
  obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu (rowGaussianBlocks ms (fun j => d (j+1)))
    (rowGaussianBlocks_valid ms (fun a ha => ⟨(ht a ha).1.le,(ht a ha).2.le⟩) _)
  have hg := (rowBounded_exp_growth hK m).1
  have hf := hK.diff.continuous.measurable
  have hw := rowTiltStep_weight_integrable hf hg (d 0) x
  have hi := rowTiltStep_product_integrable hf hg hh hB hb (d 0) x
  have hc := integral_exp_pos hw
  have hratio := decoratedTransition_lintegral_ratio m (ne_of_gt (hms m (by simp)).1) ms
    (rowGaussianLaw d) (fun j => inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d j)))) hu.diff.continuous.measurable
    (rowGaussian_recursion hu (m::ms) hms d).2 ((hh.comp (show Measurable (fun a : ℝ => x+a) by fun_prop)).ennreal_ofReal) x
  dsimp only [Function.comp_apply] at hratio
  rw [hratio]
  change (∫⁻ a, ENNReal.ofReal (h (x+a))*ENNReal.ofReal
    (Real.exp (m*familyRecursion ms (rowGaussianLaw (fun j => d (j+1))) u (x+a)))
      ∂gaussianReal 0 (d 0)) / ENNReal.ofReal (∫ a, Real.exp
    (m*familyRecursion ms (rowGaussianLaw (fun j => d (j+1))) u (x+a)) ∂gaussianReal 0 (d 0)) = _
  rw [(rowGaussian_recursion hu ms ht _).1]
  rw [rowGaussian_lintegral (d 0) (by fun_prop), rowGaussian_integral (d 0) (by fun_prop)]
  simp_rw [← ENNReal.ofReal_mul (hn _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun z => mul_nonneg (hn _) (Real.exp_pos _).le))]
  exact (ENNReal.ofReal_div_of_pos hc).symm

lemma rowAffine_bound {f : ℝ → ℝ} {L A B : ℝ} (hf : ∀ y, |deriv f y| ≤ L)
    (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1) (y : ℝ) :
    0 ≤ A*deriv f y+B ∧ A*deriv f y+B ≤ 1 := by
  have hh : |A*deriv f y| ≤ |A| * L := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _)
  constructor <;> linarith [le_abs_self (A*deriv f y), neg_abs_le (A*deriv f y)]

lemma rowSinglePattern_valid {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (h1 : ∀ x, φ x ≤ 1)
    (k : ℕ) : ValidMarkedReplicaPattern k (rowSinglePattern φ k) := by
  induction k with
  | zero => exact ⟨by change 0 < (1:ℕ); norm_num,hφ,h1⟩
  | succ k ih =>
    refine ⟨List.cons_ne_nil _ _,?_⟩
    intro b hb
    change b ∈ [rowSinglePattern φ k] at hb
    rw [List.mem_singleton] at hb
    exact hb ▸ ih

lemma rowPairPattern_valid {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (h1 : ∀ x, φ x ≤ 1)
    (k j : ℕ) : ValidMarkedReplicaPattern k (rowPairPattern φ k j) := by
  induction k generalizing j with
  | zero => exact ⟨by change 0 < (2:ℕ); norm_num,hφ.pow_const 2,fun x => pow_le_one₀ bot_le (h1 x)⟩
  | succ k ih =>
    cases j with
    | zero =>
      refine ⟨List.cons_ne_nil _ _,?_⟩
      intro b hb
      change b ∈ [rowSinglePattern φ k,rowSinglePattern φ k] at hb
      have hb' : b = rowSinglePattern φ k := by simpa only [List.mem_cons,List.mem_nil_iff,or_false,or_self] using hb
      subst b
      exact rowSinglePattern_valid hφ h1 k
    | succ j =>
      refine ⟨List.cons_ne_nil _ _,?_⟩
      intro b hb
      change b ∈ [rowPairPattern φ k j] at hb
      have hb' : b = rowPairPattern φ k j := List.mem_singleton.mp hb
      subst b
      exact ih j

lemma familyReplicaMean_single_affine {u : ℝ → ℝ} {L H A B : ℝ}
    (hu : RowBoundedTerminal u L H) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1) (d : ℕ → ℝ≥0) (x : ℝ) :
    familyReplicaMean ms (rowSinglePattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length)
      (rowGaussianLaw d) u x = ENNReal.ofReal (A*deriv (gaussianRowComposition (rowGaussianBlocks ms d) u) x+B) := by
  induction ms generalizing d x with
  | nil => rfl
  | cons m ms ih =>
    have ht : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => hms a (by simp [ha])
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu (rowGaussianBlocks ms (fun j => d (j+1)))
      (rowGaussianBlocks_valid ms (fun a ha => ⟨(ht a ha).1.le,(ht a ha).2.le⟩) _)
    simp only [List.length_cons,rowSinglePattern,familyReplicaMean,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one]
    change (∫⁻ a, familyReplicaMean ms _ (rowGaussianLaw (fun j => d (j+1))) u (x+a) ∂_) = _
    simp_rw [ih ht]
    rw [decoratedGaussian_ofReal hu m ms hms d (by fun_prop) zero_le_one
      (fun y => (abs_of_nonneg (rowAffine_bound hK.slope hA hB y).1).trans_le
        (rowAffine_bound hK.slope hA hB y).2)
      (fun y => (rowAffine_bound hK.slope hA hB y).1) x]
    rw [rowTiltStep_affine
      (rowTiltStep_weight_integrable hK.diff.continuous.measurable (rowBounded_exp_growth hK m).1 _ x)
      (rowTiltStep_product_integrable hK.diff.continuous.measurable (rowBounded_exp_growth hK m).1
        (measurable_deriv _) hu.L_nonneg hK.slope _ x)]
    rw [rowGaussianBlocks,gaussianRowComposition,((rowBoundedOperator_derivatives hK m (d 0)).1 x).deriv]

lemma rowTiltStep_three {f h k : ℝ → ℝ} {a T x : ℝ}
    (hw : Integrable (fun z => Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (hh : Integrable (fun z => h (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (hk : Integrable (fun z => k (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1))
    (A B C : ℝ) : rowTiltStep a T f x (fun y => A*h y+B*k y+C) =
      A*rowTiltStep a T f x h+B*rowTiltStep a T f x k+C := by
  have hZ := (integral_exp_pos hw).ne'
  simp only [rowTiltStep]
  simp_rw [add_mul, mul_assoc]
  have hadd := integral_add ((hh.const_mul A).add (hk.const_mul B)) (hw.const_mul C)
  simp only [Pi.add_apply] at hadd
  rw [hadd,
    integral_add (hh.const_mul A) (hk.const_mul B), integral_const_mul, integral_const_mul,
    integral_const_mul]
  field_simp

def rowAffineMoment (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) (j : ℕ) (A B x : ℝ) : ℝ :=
  A^2*rowDerivativeDepthMoment rs u j x+2*A*B*deriv (gaussianRowComposition rs u) x+B^2

lemma rowAffineMoment_measurable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (j : ℕ) (A B : ℝ) : Measurable (rowAffineMoment rs u j A B) :=
  (((measurable_rowDerivativeDepthMoment hu rs hrs j).const_mul (A^2)).add
    ((measurable_deriv _).const_mul (2*A*B))).add_const (B^2)

lemma rowAffineMoment_nonneg {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (j : ℕ) (A B x : ℝ) : 0 ≤ rowAffineMoment rs u j A B x := by
  have he := rowDerivativeDepthMoment_monotone hu rs hrs x (Nat.zero_le j)
  simp only [rowDerivativeDepthMoment.eq_1] at he
  have hh := mul_le_mul_of_nonneg_left he (sq_nonneg A)
  dsimp [rowAffineMoment]
  nlinarith [sq_nonneg (A*deriv (gaussianRowComposition rs u) x+B)]

lemma rowAffineMoment_bound {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (j : ℕ) (A B x : ℝ) :
    |rowAffineMoment rs u j A B x| ≤ A^2*L^2+|2*A*B| * L+B^2 := by
  obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs hrs
  have hd := rowDerivativeDepthMoment_bounds hu rs hrs j x
  rw [abs_of_nonneg (rowAffineMoment_nonneg hu rs hrs j A B x)]
  dsimp [rowAffineMoment]
  have hp := mul_le_mul_of_nonneg_left hd.2 (sq_nonneg A)
  have hq : 2*A*B*deriv (gaussianRowComposition rs u) x ≤ |2*A*B| * L :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK.slope x) (abs_nonneg _))
  linarith

lemma familyReplicaMean_pair_affine {u : ℝ → ℝ} {L H A B : ℝ}
    (hu : RowBoundedTerminal u L H) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1) (d : ℕ → ℝ≥0) (j : ℕ) (x : ℝ) :
    familyReplicaMean ms (rowPairPattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length j)
      (rowGaussianLaw d) u x = ENNReal.ofReal (rowAffineMoment (rowGaussianBlocks ms d) u j A B x) := by
  induction ms generalizing d j x with
  | nil =>
    change (ENNReal.ofReal (A*deriv u x+B))^2 = _
    rw [pow_two, ← ENNReal.ofReal_mul (rowAffine_bound hu.slope hA hB x).1]
    congr 1
    simp only [rowAffineMoment,rowDerivativeDepthMoment_nil,rowGaussianBlocks,gaussianRowComposition]
    ring
  | cons m ms ih =>
    have ht : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => hms a (by simp [ha])
    have hrs := rowGaussianBlocks_valid ms (fun a ha => ⟨(ht a ha).1.le,(ht a ha).2.le⟩) (fun j => d (j+1))
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu _ hrs
    cases j with
    | zero =>
      have hs := familyReplicaMean_single_affine hu hA hB (m::ms) hms d x
      simp only [List.length_cons,rowSinglePattern,familyReplicaMean,List.map_cons,List.map_nil,
        List.prod_cons,List.prod_nil,mul_one] at hs
      simp only [List.length_cons,rowPairPattern,familyReplicaMean,List.map_cons,List.map_nil,
        List.prod_cons,List.prod_nil,mul_one]
      rw [hs]
      obtain ⟨K',hK'⟩ := rowBoundedComposition_terminal hu (rowGaussianBlocks (m::ms) d)
        (rowGaussianBlocks_valid _ (fun a ha => ⟨(hms a ha).1.le,(hms a ha).2.le⟩) _)
      rw [← ENNReal.ofReal_mul (rowAffine_bound hK'.slope hA hB x).1]
      congr 1
      simp only [rowAffineMoment,rowDerivativeDepthMoment]
      ring
    | succ j =>
      simp only [List.length_cons,rowPairPattern,familyReplicaMean,List.map_cons,List.map_nil,
        List.prod_cons,List.prod_nil,mul_one]
      change (∫⁻ a, familyReplicaMean ms _ (rowGaussianLaw (fun i => d (i+1))) u (x+a) ∂_) = _
      simp_rw [ih ht]
      have hL := hu.L_nonneg
      rw [decoratedGaussian_ofReal hu m ms hms d (rowAffineMoment_measurable hu _ hrs j A B)
        (by positivity : 0 ≤ A^2*L^2+|2*A*B| * L+B^2)
        (rowAffineMoment_bound hu _ hrs j A B) (rowAffineMoment_nonneg hu _ hrs j A B) x]
      unfold rowAffineMoment
      have hg := (rowBounded_exp_growth hK m).1
      have hf := hK.diff.continuous.measurable
      rw [rowTiltStep_three (rowTiltStep_weight_integrable hf hg _ x)
        (rowTiltStep_product_integrable hf hg (measurable_rowDerivativeDepthMoment hu _ hrs j)
          (sq_nonneg L) (fun y => by
            rw [abs_of_nonneg (rowDerivativeDepthMoment_bounds hu _ hrs j y).1]
            exact (rowDerivativeDepthMoment_bounds hu _ hrs j y).2) _ x)
        (rowTiltStep_product_integrable hf hg (measurable_deriv _) hu.L_nonneg hK.slope _ x)]
      rw [rowGaussianBlocks, rowDerivativeDepthMoment, gaussianRowComposition,
        ((rowBoundedOperator_derivatives hK m (d 0)).1 x).deriv]

end MicroscopicJamming

namespace MicroscopicJamming
lemma familySample_pair_affine {u : ℝ → ℝ} {L H A B : ℝ}
    (hu : RowBoundedTerminal u L H) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (hord : ms.Pairwise (· < ·)) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (j : ℕ) (x : ℝ) :
    (∫⁻ ω, familySampleMean ms (rowPairPattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length j)
      u x ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
    ENNReal.ofReal (rpcPatternProduct ms 0 (markedReplicaShape ms.length
      (rowPairPattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length j))) *
      ENNReal.ofReal (rowAffineMoment (rowGaussianBlocks ms d) u j A B x) := by
  have hν (j : ℕ) : IsProbabilityMeasure (rowGaussianLaw d j) :=
    inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d j)))
  have hφ : Measurable (fun y => ENNReal.ofReal (A*deriv u y+B)) := by fun_prop
  have h1 : ∀ y, ENNReal.ofReal (A*deriv u y+B) ≤ 1 := fun y =>
    (ENNReal.ofReal_le_ofReal (rowAffine_bound hu.slope hA hB y).2).trans_eq (by norm_num)
  have he := (familySample ℝ inferInstance inferInstance inferInstance inferInstance ms hord hms
    (rowGaussianLaw d) hν u hu.diff.continuous.measurable (rowGaussian_recursion hu ms hms d).2).2
      _ (rowPairPattern_valid hφ h1 ms.length j) 0 le_rfl (fun a ha => (hms a ha).1) x
  let := familyCascadeLaw_probability ms.length (rowGaussianLaw d) hν
  simpa only [Real.rpow_zero,ENNReal.ofReal_one,one_mul,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,
    one_smul,div_one,familyReplicaMean_pair_affine hu hA hB ms hms d j x] using he

 theorem rowGaussianPair : RowGaussianPairStatement := by
  intro u L H hu hL hH hb ms hord hms d Δ j hj x
  have hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),
    hu'.differentiable (by norm_num),hL,hH,fun y => (hb y).1,fun y => (hb y).2⟩
  have hv := rowBoundedOperator_terminal ht (by norm_num : (0:ℝ) ≤ 1) le_rfl (Δ:ℝ)
  have hc : 0 < L+1 := by linarith
  let A : ℝ := 1/(2*(L+1))
  let B : ℝ := 1/2
  have hA : |A| * L ≤ B := by dsimp [A,B]; rw [abs_of_pos (by positivity), one_div_mul_eq_div]; apply (div_le_iff₀ (by positivity : 0 < 2*(L+1))).mpr; linarith
  have hB : B+|A| * L ≤ 1 := by dsimp [B] at *; linarith
  have he := familySample_pair_affine hv hA hB ms hord hms d j x
  have htst : (fun y => ENNReal.ofReal (A*deriv (gaussianRowOperator 1 Δ u) y+B)) =
      rowDerivativeTest L (gaussianRowOperator 1 Δ u) := by
    funext y; unfold rowDerivativeTest A B; congr 1; field_simp; ring
  rw [htst] at he
  change _ = _
  refine he.trans ?_
  congr 2
  unfold rowAffineMoment A B
  field_simp
  ring
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma rowSinglePattern_shape (φ ψ : ℝ → ℝ≥0∞) (k : ℕ) :
    markedReplicaShape k (rowSinglePattern φ k) = markedReplicaShape k (rowSinglePattern ψ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ([markedReplicaShape k (rowSinglePattern φ k)] : List (ReplicaPattern k)) =
      [markedReplicaShape k (rowSinglePattern ψ k)]
    rw [ih]

lemma rowPairPattern_shape (φ ψ : ℝ → ℝ≥0∞) (k j : ℕ) :
    markedReplicaShape k (rowPairPattern φ k j) = markedReplicaShape k (rowPairPattern ψ k j) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    cases j <;> simp only [rowPairPattern,markedReplicaShape,List.map_cons,List.map_nil,
      rowSinglePattern_shape φ ψ k,ih] <;> rfl

def rowAffineIidObservable (ms : List ℝ) (u : ℝ → ℝ) (j : ℕ) (A B x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length) (ℓ : Fin 2 → CascadePath ms.length) : ℝ :=
  if cascadeSharedEdges ms.length (ℓ 0) (ℓ 1) = j then
    (A*deriv u (familyPathMark ms.length x ω (ℓ 0))+B)*
      (A*deriv u (familyPathMark ms.length x ω (ℓ 1))+B) else 0

def rowAffineIidMean (ms : List ℝ) (u : ℝ → ℝ) (j : ℕ) (A B x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length) : ℝ :=
  ∫ ℓ : Fin 2 → CascadePath ms.length, rowAffineIidObservable ms u j A B x ω ℓ
    ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)

lemma rowAffineIidObservable_bound {u : ℝ → ℝ} {L A B : ℝ}
    (hu : ∀ y, |deriv u y| ≤ L) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length)
    (ℓ : Fin 2 → CascadePath ms.length) :
    0 ≤ rowAffineIidObservable ms u j A B x ω ℓ ∧ rowAffineIidObservable ms u j A B x ω ℓ ≤ 1 := by
  unfold rowAffineIidObservable
  split_ifs
  · exact ⟨mul_nonneg (rowAffine_bound hu hA hB _).1 (rowAffine_bound hu hA hB _).1,
      (mul_le_mul (rowAffine_bound hu hA hB _).2 (rowAffine_bound hu hA hB _).2
        (rowAffine_bound hu hA hB _).1 zero_le_one).trans_eq (by ring)⟩
  · exact ⟨le_rfl,zero_le_one⟩

lemma rowAffineIidObservable_integrable {u : ℝ → ℝ} {L A B : ℝ}
    (hu : ∀ y, |deriv u y| ≤ L) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) :
    Integrable (rowAffineIidObservable ms u j A B x ω)
      (Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)) := by
  let := familySampleLeafLaw_probability ms u x ω
  apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall (fun ℓ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rowAffineIidObservable_bound hu hA hB ms j x ω ℓ).1]
    exact (rowAffineIidObservable_bound hu hA hB ms j x ω ℓ).2)

lemma rowAffineIidMean_eq {u : ℝ → ℝ} {L A B : ℝ}
    (hu : ∀ y, |deriv u y| ≤ L) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (hj : j ≤ ms.length) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) :
    rowAffineIidMean ms u j A B x ω =
      (familySampleMean ms (rowPairPattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length j) u x ω).toReal := by
  rw [rowAffineIidMean,integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun ℓ => (rowAffineIidObservable_bound hu hA hB ms j x ω ℓ).1))
    (measurable_of_countable _).aestronglyMeasurable,
    rowPairSemantic_proved ms _ j hj u x ω]
  congr 1
  apply lintegral_congr
  intro ℓ
  simp only [rowAffineIidObservable,rowPairIidObservable]
  split_ifs
  · exact ENNReal.ofReal_mul (rowAffine_bound hu hA hB _).1
  · exact ENNReal.ofReal_zero

lemma rowAffineIidMean_bound {u : ℝ → ℝ} {L A B : ℝ}
    (hu : ∀ y, |deriv u y| ≤ L) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) :
    0 ≤ rowAffineIidMean ms u j A B x ω ∧ rowAffineIidMean ms u j A B x ω ≤ 1 := by
  let := familySampleLeafLaw_probability ms u x ω
  constructor
  · exact integral_nonneg (fun ℓ => (rowAffineIidObservable_bound hu hA hB ms j x ω ℓ).1)
  · exact (integral_mono (rowAffineIidObservable_integrable hu hA hB ms j x ω)
      (integrable_const 1) (fun ℓ => (rowAffineIidObservable_bound hu hA hB ms j x ω ℓ).2)).trans_eq (by simp)

lemma rowAffineIidMean_measurable {u : ℝ → ℝ} {L A B : ℝ}
    (hmu : Measurable u) (hu : ∀ y, |deriv u y| ≤ L) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (hj : j ≤ ms.length) (x : ℝ) :
    Measurable (rowAffineIidMean ms u j A B x) := by
  have hφ : Measurable (fun y => ENNReal.ofReal (A*deriv u y+B)) := by fun_prop
  have hφ1 : ∀ y, ENNReal.ofReal (A*deriv u y+B) ≤ 1 := fun y =>
    (ENNReal.ofReal_le_ofReal (rowAffine_bound hu hA hB y).2).trans_eq (by norm_num)
  have he : rowAffineIidMean ms u j A B x = fun ω =>
      (familySampleMean ms (rowPairPattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length j) u x ω).toReal :=
    funext (rowAffineIidMean_eq hu hA hB ms j hj x)
  rw [he]
  exact ((measurable_familySampleMean ms hmu _ (rowPairPattern_valid hφ hφ1 ms.length j)).comp
    (measurable_const.prodMk measurable_id)).ennreal_toReal

lemma rowAffineIidMean_integrable {u : ℝ → ℝ} {L A B : ℝ}
    (hmu : Measurable u) (hu : ∀ y, |deriv u y| ≤ L) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (hj : j ≤ ms.length) (x : ℝ)
    (μ : Measure (FamilyCascadeTree ℝ ms.length)) [IsFiniteMeasure μ] :
    Integrable (rowAffineIidMean ms u j A B x) μ := by
  apply (integrable_const (1:ℝ)).mono' (rowAffineIidMean_measurable hmu hu hA hB ms j hj x).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rowAffineIidMean_bound hu hA hB ms j x ω).1]
    exact (rowAffineIidMean_bound hu hA hB ms j x ω).2)

lemma rowAffineIidMean_expectation {u : ℝ → ℝ} {L H A B : ℝ}
    (hu : RowBoundedTerminal u L H) (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (hord : ms.Pairwise (· < ·)) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (j : ℕ) (hj : j ≤ ms.length) (x : ℝ) :
    (∫ ω, rowAffineIidMean ms u j A B x ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      rpcPatternProduct ms 0 (markedReplicaShape ms.length (rowPairPattern (fun _ => 1) ms.length j)) *
        rowAffineMoment (rowGaussianBlocks ms d) u j A B x := by
  have hν (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  let := familyCascadeLaw_probability ms.length (rowGaussianLaw d) hν
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun ω => (rowAffineIidMean_bound hu.slope hA hB ms j x ω).1))
    (rowAffineIidMean_measurable hu.diff.continuous.measurable hu.slope hA hB ms j hj x).aestronglyMeasurable]
  have he (ω : FamilyCascadeTree ℝ ms.length) : ENNReal.ofReal (rowAffineIidMean ms u j A B x ω) =
      familySampleMean ms (rowPairPattern (fun y => ENNReal.ofReal (A*deriv u y+B)) ms.length j) u x ω := by
    rw [rowPairSemantic_proved ms _ j hj u x ω]
    rw [rowAffineIidMean,ofReal_integral_eq_lintegral_ofReal
      (rowAffineIidObservable_integrable hu.slope hA hB ms j x ω)
      (Eventually.of_forall (fun ℓ => (rowAffineIidObservable_bound hu.slope hA hB ms j x ω ℓ).1))]
    apply lintegral_congr
    intro ℓ
    simp only [rowAffineIidObservable,rowPairIidObservable]
    split_ifs
    · exact ENNReal.ofReal_mul (rowAffine_bound hu.slope hA hB _).1
    · exact ENNReal.ofReal_zero
  simp_rw [he]
  rw [familySample_pair_affine hu hA hB ms hord hms d j x, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (rpcPatternProduct_nonneg ms hord hms 0 (fun m hm => (hms m hm).1) _),
    ENNReal.toReal_ofReal (rowAffineMoment_nonneg hu _
      (rowGaussianBlocks_valid ms (fun m hm => ⟨(hms m hm).1.le,(hms m hm).2.le⟩) d) j A B x),
    rowPairPattern_shape _ (fun _ => 1)]

end MicroscopicJamming

namespace MicroscopicJamming
lemma rowSignedPairObservable_polarization (ms : List ℝ) (u : ℝ → ℝ) (j : ℕ) (A B x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length) (ℓ : Fin 2 → CascadePath ms.length) :
    (2*A^2)*rowSignedPairObservable ms u j x ω ℓ =
      rowAffineIidObservable ms u j A B x ω ℓ + rowAffineIidObservable ms u j (-A) B x ω ℓ -
        2*rowAffineIidObservable ms u j 0 B x ω ℓ := by
  unfold rowSignedPairObservable rowAffineIidObservable
  split_ifs <;> ring

lemma rowSignedPairObservable_integrable {u : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hu : ∀ y, |deriv u y| ≤ L)
    (ms : List ℝ) (j : ℕ) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) :
    Integrable (rowSignedPairObservable ms u j x ω)
      (Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)) := by
  let := familySampleLeafLaw_probability ms u x ω
  apply (integrable_const (L^2)).mono' (measurable_of_countable _).aestronglyMeasurable
  apply Eventually.of_forall
  intro ℓ
  unfold rowSignedPairObservable
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (hu _) (hu _) (abs_nonneg _) hL).trans_eq (pow_two L).symm
  · simp [sq_nonneg L]

lemma rowSignedPairMean_polarization {u : ℝ → ℝ} {L A B : ℝ}
    (hL : 0 ≤ L) (hu : ∀ y, |deriv u y| ≤ L)
    (hA : |A| * L ≤ B) (hB : B+|A| * L ≤ 1)
    (ms : List ℝ) (j : ℕ) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) :
    (2*A^2)*(∫ ℓ, rowSignedPairObservable ms u j x ω ℓ
      ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)) =
      rowAffineIidMean ms u j A B x ω + rowAffineIidMean ms u j (-A) B x ω -
        2*rowAffineIidMean ms u j 0 B x ω := by
  have hBn : 0 ≤ B := (mul_nonneg (abs_nonneg _) hL).trans hA
  have hB1 : B ≤ 1 := by linarith [mul_nonneg (abs_nonneg A) hL]
  have hnA : |-A| * L ≤ B := by simpa using hA
  have hnB : B+|-A| * L ≤ 1 := by simpa using hB
  have hzA : |(0:ℝ)| * L ≤ B := by simpa using hBn
  have hzB : B+|(0:ℝ)| * L ≤ 1 := by simpa using hB1
  have hp := rowAffineIidObservable_integrable hu hA hB ms j x ω
  have hn := rowAffineIidObservable_integrable hu hnA hnB ms j x ω
  have hz := rowAffineIidObservable_integrable hu hzA hzB ms j x ω
  rw [← integral_const_mul]
  simp_rw [rowSignedPairObservable_polarization ms u j A B]
  have hsub := integral_sub (hp.add hn) (hz.const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub,integral_add hp hn,integral_const_mul]
  rfl

lemma rowSignedPair_expectation {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (hord : ms.Pairwise (· < ·)) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (j : ℕ) (hj : j ≤ ms.length) (x : ℝ) :
    (∫ ω, (∫ ℓ, rowSignedPairObservable ms u j x ω ℓ
      ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω))
        ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      rpcPatternProduct ms 0 (markedReplicaShape ms.length (rowPairPattern (fun _ => 1) ms.length j)) *
        rowDerivativeDepthMoment (rowGaussianBlocks ms d) u j x := by
  have hν (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  let := familyCascadeLaw_probability ms.length (rowGaussianLaw d) hν
  let A : ℝ := 1/(2*(L+1))
  let B : ℝ := 1/2
  have hAp : 0 < A := by dsimp [A]; positivity [hu.L_nonneg]
  have hA : |A| * L ≤ B := by
    dsimp [A,B]
    rw [abs_of_pos (by positivity [hu.L_nonneg]),one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity [hu.L_nonneg] : 0 < 2*(L+1))).mpr
    linarith
  have hB : B+|A| * L ≤ 1 := by dsimp [B] at *; linarith
  have hnA : |-A| * L ≤ B := by simpa using hA
  have hnB : B+|-A| * L ≤ 1 := by simpa using hB
  have hzA : |(0:ℝ)| * L ≤ B := by norm_num [B]
  have hzB : B+|(0:ℝ)| * L ≤ 1 := by norm_num [B]
  have hp := rowAffineIidMean_integrable hu.diff.continuous.measurable hu.slope hA hB ms j hj x
    (familyCascadeLaw ms.length (rowGaussianLaw d))
  have hn := rowAffineIidMean_integrable hu.diff.continuous.measurable hu.slope hnA hnB ms j hj x
    (familyCascadeLaw ms.length (rowGaussianLaw d))
  have hz := rowAffineIidMean_integrable hu.diff.continuous.measurable hu.slope hzA hzB ms j hj x
    (familyCascadeLaw ms.length (rowGaussianLaw d))
  have he : (2*A^2)*(∫ ω, (∫ ℓ, rowSignedPairObservable ms u j x ω ℓ
      ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω))
        ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      (∫ ω, rowAffineIidMean ms u j A B x ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) +
      (∫ ω, rowAffineIidMean ms u j (-A) B x ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) -
        2*(∫ ω, rowAffineIidMean ms u j 0 B x ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) := by
    rw [← integral_const_mul]
    simp_rw [rowSignedPairMean_polarization hu.L_nonneg hu.slope hA hB]
    have hsub := integral_sub (hp.add hn) (hz.const_mul 2)
    simp only [Pi.add_apply] at hsub
    rw [hsub,integral_add hp hn,integral_const_mul]
  rw [rowAffineIidMean_expectation hu hA hB ms hord hms d j hj x,
    rowAffineIidMean_expectation hu hnA hnB ms hord hms d j hj x,
    rowAffineIidMean_expectation hu hzA hzB ms hord hms d j hj x] at he
  dsimp [rowAffineMoment] at he
  apply (mul_left_cancel₀ (show 2*A^2 ≠ 0 by positivity))
  calc
    _ = _ := he
    _ = _ := by ring

theorem rowSignedPair : RowSignedPairStatement := by
  intro u L H hu hL hH hb ms hord hms d Δ j hj x
  have hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),
    hu'.differentiable (by norm_num),hL,hH,fun y => (hb y).1,fun y => (hb y).2⟩
  have hv := rowBoundedOperator_terminal ht (by norm_num : (0:ℝ) ≤ 1) le_rfl (Δ:ℝ)
  exact rowSignedPair_expectation hv ms hord hms d j hj x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma rowSinglePattern_size (φ : ℝ → ℝ≥0∞) (k : ℕ) :
    replicaPatternSize k (markedReplicaShape k (rowSinglePattern φ k)) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rowSinglePattern,markedReplicaShape,replicaPatternSize,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using ih

lemma rowPairPattern_size (φ : ℝ → ℝ≥0∞) (k j : ℕ) :
    replicaPatternSize k (markedReplicaShape k (rowPairPattern φ k j)) = 2 := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    cases j <;> simp only [rowPairPattern,markedReplicaShape,replicaPatternSize,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,rowSinglePattern_size,ih]

lemma partitionProduct_one (m η : ℝ) : partitionProduct m η [1] = 1 := by
  norm_num [partitionProduct]

lemma partitionProduct_two (m η : ℝ) : partitionProduct m η [2] = (1-m)/(1-η) := by
  norm_num [partitionProduct,Nat.Ico_succ_singleton]
  ring

lemma partitionProduct_one_one (m η : ℝ) : partitionProduct m η [1,1] = (m-η)/(1-η) := by
  norm_num [partitionProduct,Nat.Ico_succ_singleton]

lemma rpcPatternProduct_single (ms : List ℝ) (η : ℝ) (φ : ℝ → ℝ≥0∞) :
    rpcPatternProduct ms η (markedReplicaShape ms.length (rowSinglePattern φ ms.length)) = 1 := by
  induction ms generalizing η with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.length_cons,rowSinglePattern,markedReplicaShape,rpcPatternProduct,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,rowSinglePattern_size,
      partitionProduct_one,ih]

noncomputable def rowPairWeight (ms : List ℝ) (η : ℝ) (j : ℕ) : ℝ :=
  rpcPatternProduct ms η (markedReplicaShape ms.length (rowPairPattern (fun _ => 1) ms.length j))

lemma rowPairWeight_nil (η : ℝ) (j : ℕ) : rowPairWeight [] η j = 1 := rfl

lemma rowPairWeight_cons_zero (m : ℝ) (ms : List ℝ) (η : ℝ) :
    rowPairWeight (m::ms) η 0 = (m-η)/(1-η) := by
  simp only [rowPairWeight,List.length_cons,rowPairPattern,markedReplicaShape,rpcPatternProduct,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,rowSinglePattern_size,
    partitionProduct_one_one,rpcPatternProduct_single,mul_one]

lemma rowPairWeight_cons_succ (m : ℝ) (ms : List ℝ) (η : ℝ) (j : ℕ) :
    rowPairWeight (m::ms) η (j+1) = (1-m)/(1-η)*rowPairWeight ms m j := by
  simp only [rowPairWeight,List.length_cons,rowPairPattern,markedReplicaShape,rpcPatternProduct,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,rowPairPattern_size,
    partitionProduct_two]

lemma rpcStepLevel_le_length (ms : List ℝ) (s : ℝ) : rpcStepLevel ms s ≤ ms.length :=
  List.length_filter_le _ _

lemma rpcStepLevel_of_lt_head (m : ℝ) (ms : List ℝ) (hms : ∀ a ∈ ms, m < a)
    (s : ℝ) (hs : s < m) : rpcStepLevel (m::ms) s = 0 := by
  unfold rpcStepLevel
  have he : (m::ms).filter (fun a => a ≤ s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha he
    have hle : a ≤ s := of_decide_eq_true he
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (not_lt_of_ge hle) hs
    · exact (not_lt_of_ge hle) (hs.trans (hms a ha))
  rw [he]
  rfl

lemma rpcStepLevel_of_le_head (m : ℝ) (ms : List ℝ) (s : ℝ) (hs : m ≤ s) :
    rpcStepLevel (m::ms) s = rpcStepLevel ms s+1 := by
  simp [rpcStepLevel,hs]

lemma rpcStepTest_intervalIntegrable (ms : List ℝ) (F : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s => F (rpcStepLevel ms s)) volume a b := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
    change IsFiniteMeasure (volume.restrict (Set.Ioc (min a b) (max a b)))
    infer_instance
  apply (integrable_const (∑ j ∈ Finset.range (ms.length+1), ‖F j‖)).mono'
    (((measurable_of_countable F).comp (measurable_rpcStepLevel ms)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro s
  exact Finset.single_le_sum (fun j hj => norm_nonneg (F j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (rpcStepLevel_le_length ms s)))

lemma integral_rpcStepTest_weights (ms : List ℝ) (hord : ms.Pairwise (· < ·))
    (hms : ∀ m ∈ ms, m < 1) (η : ℝ) (hη : η < 1) (hηms : ∀ m ∈ ms, η < m) (F : ℕ → ℝ) :
    (∫ s in η..1, F (rpcStepLevel ms s)) =
      (1-η)*∑ j ∈ Finset.range (ms.length+1), rowPairWeight ms η j * F j := by
  induction ms generalizing η F with
  | nil => simp [rpcStepLevel,rowPairWeight,rpcPatternProduct,intervalIntegral.integral_const,smul_eq_mul]
  | cons m ms ih =>
    have hm1 : m < 1 := hms m (by simp)
    have hηm : η < m := hηms m (by simp)
    have htail := (List.pairwise_cons.mp hord).1
    have hleft : (∫ s in η..m, F (rpcStepLevel (m::ms) s)) = (m-η)*F 0 := by
      calc
        _ = ∫ _ in η..m, F 0 := intervalIntegral.integral_congr_Ioo_of_le hηm.le
          (fun s hs => by rw [rpcStepLevel_of_lt_head m ms htail s hs.2])
        _ = _ := by simp [intervalIntegral.integral_const,smul_eq_mul]
    have hright : (∫ s in m..1, F (rpcStepLevel (m::ms) s)) =
        ∫ s in m..1, F (rpcStepLevel ms s+1) :=
      intervalIntegral.integral_congr_Ioo_of_le hm1.le
        (fun s hs => by rw [rpcStepLevel_of_le_head m ms s hs.1.le])
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (rpcStepTest_intervalIntegrable (m::ms) F η m)
      (rpcStepTest_intervalIntegrable (m::ms) F m 1),hleft,hright,
      ih (List.pairwise_cons.mp hord).2 (fun a ha => hms a (by simp [ha])) m hm1 htail (fun j => F (j+1))]
    simp only [List.length_cons]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [rowPairWeight_cons_zero,rowPairWeight_cons_succ]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    have hn : 1-η ≠ 0 := sub_ne_zero.mpr hη.ne'
    field_simp
    ring
end MicroscopicJamming

end

end OAI
