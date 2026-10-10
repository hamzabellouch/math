import Mathlib
import OAI.Probability.ParisiFinite.BoundedOf

namespace OAI

/-! Square Kernel. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiGuerra
open ParisiFinite SKQAOA SKGaussian ParisiInterpolation

def squareKernel (n : ℕ) (q : ℝ) (σ τ : Configuration n) : ℝ := (overlap σ τ-q)^2

lemma replica_frontier (n : ℕ) (β : ℝ≥0) (hβ : 0 < β)
    (cs : List (MovingCoordinate (Configuration n → ℝ))) (q t : ℝ) :
    replicaObserve β hβ cs t (frontierKernel n q t) =
      (Real.sin t*Real.cos t*(n:ℝ)/2) • replicaObserve β hβ cs t (squareKernel n q) -
        BoundedContinuousFunction.const (Configuration n → ℝ)
          (Real.sin t*Real.cos t*((n:ℝ)/2*q^2+1/2)) := by
  have he : frontierKernel n q t =
      (Real.sin t*Real.cos t*(n:ℝ)/2) • squareKernel n q -
        (fun _ _ => Real.sin t*Real.cos t*((n:ℝ)/2*q^2+1/2)) := by
    ext σ τ
    simp only [frontierKernel, squareKernel, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, map_sub, map_smul, replicaObserve_const]

 

def siteCorrection (n : ℕ) (β : ℝ≥0) (hβ : 0 < β) :
    Schedule → ℝ → ℝ → ℝ → BoundedContinuousFunction (Configuration n → ℝ) ℝ
  | [], q, a, t => ((β:ℝ)-a) • replicaObserve β hβ [] t (squareKernel n q)
  | l::ls, q, a, t => ((l.1:ℝ)-a) • replicaObserve β hβ (siteCoordinates n (l::ls)) t (squareKernel n q) +
      prefixTransport (traceField β hβ) (siteCoordinates n ls) (siteBlock n l) t
        (siteCorrection n β hβ ls (q+l.2) l.1 t)

def jumpSquares (β : ℝ) : Schedule → ℝ → ℝ → ℝ
  | [], q, a => (β-a)*q^2
  | l::ls, q, a => ((l.1:ℝ)-a)*q^2 + jumpSquares β ls (q+l.2) l.1

lemma jumpSquares_eq (β : ℝ) (ls : Schedule) (q a : ℝ) :
    jumpSquares β ls q a = β*(q+width ls)^2-a*q^2-4*penalty q ls := by
  induction ls generalizing q a with
  | nil => simp [jumpSquares, width, penalty]; ring
  | cons l ls ih =>
    simp only [jumpSquares, ih, width, List.map_cons, List.sum_cons, penalty]
    ring

lemma site_remainder {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (q a t : ℝ) (vs : Noise (Configuration n → ℝ))
    (hv : kernelNoise vs = frontierKernel n q t) :
    hierarchyRemainder (traceField β hβ) β (siteCoordinates n ls) t a vs =
      (Real.sin t*Real.cos t*(n:ℝ)/2) • siteCorrection n β hβ ls q a t -
        BoundedContinuousFunction.const (Configuration n → ℝ)
          (Real.sin t*Real.cos t*((n:ℝ)/2*jumpSquares β ls q a+((β:ℝ)-a)/2)) := by
  induction ls generalizing q a vs with
  | nil =>
    change ((β:ℝ)-a) • noiseGradient (traceField β hβ) vs = _
    have hg := noiseGradient_replica β hβ [] t vs
    change noiseGradient (traceField β hβ) vs = _ at hg
    rw [hg, hv, replica_frontier]
    simp only [siteCorrection, jumpSquares]
    ext x
    simp only [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.const_apply, smul_eq_mul]
    ring
  | cons l ls ih =>
    have hh := remainder_nonempty_constant_prefix (traceField β hβ) β a l.1
      (dummyCoordinate l.1) (List.ofFn (fun i : Fin n => MovingCoordinate.cosine l.1
        (fun σ => Real.sqrt l.2*spin σ i))) (siteCoordinates n ls) t vs (siteBlock_gamma n l)
    change hierarchyRemainder (traceField β hβ) β (siteCoordinates n (l::ls)) t a vs =
      ((l.1:ℝ)-a) • noiseGradient ((hierarchy (traceField β hβ) (siteCoordinates n (l::ls))).field t) vs +
      prefixTransport (traceField β hβ) (siteCoordinates n ls) (siteBlock n l) t
        (hierarchyRemainder (traceField β hβ) β (siteCoordinates n ls) t l.1 (allNoise (siteBlock n l) t vs)) at hh
    rw [hh, noiseGradient_replica, hv, replica_frontier]
    have hv' : kernelNoise (allNoise (siteBlock n l) t vs) = frontierKernel n (q+l.2) t := by
      rw [kernelNoise_allNoise, hv, frontier_add_site hn]
    rw [ih (q+l.2) l.1 _ hv', map_sub, map_smul, prefixTransport_const]
    simp only [siteCorrection, jumpSquares]
    ext x
    simp only [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply, smul_eq_mul]
    ring

 

def OrderedFrom (β a : ℝ) : Schedule → Prop
  | [] => a ≤ β
  | l::ls => a ≤ l.1 ∧ OrderedFrom β l.1 ls

lemma orderedFrom_of_pairwise {β a : ℝ} {ls : Schedule}
    (hp : ls.Pairwise (fun l k => l.1 ≤ k.1))
    (ha : a ≤ β) (hl : ∀ l ∈ ls, a ≤ l.1) (hb : ∀ l ∈ ls, (l.1:ℝ) ≤ β) :
    OrderedFrom β a ls := by
  induction ls generalizing a with
  | nil => exact ha
  | cons l ls ih =>
    rw [List.pairwise_cons] at hp
    exact ⟨hl l (by simp), ih hp.2 (hb l (by simp))
      (fun k hk => by exact_mod_cast hp.1 k hk) (fun k hk => hb k (by simp [hk]))⟩

lemma admissible_ordered {β : ℝ≥0} {ls : Schedule} (h : Admissible β ls) : OrderedFrom β 0 ls :=
  orderedFrom_of_pairwise h.2.1 β.coe_nonneg (fun l _ => l.1.coe_nonneg) h.2.2

lemma siteCorrection_nonneg (n : ℕ) (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule)
    (q a t : ℝ) (h : OrderedFrom β a ls) : ∀ x, 0 ≤ siteCorrection n β hβ ls q a t x := by
  induction ls generalizing q a with
  | nil =>
    intro x
    exact mul_nonneg (sub_nonneg.mpr h) (replicaObserve_nonneg β hβ [] t (fun _ _ => sq_nonneg _) x)
  | cons l ls ih =>
    intro x
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr h.1)
        (replicaObserve_nonneg β hβ (siteCoordinates n (l::ls)) t (fun _ _ => sq_nonneg _) x))
      (prefixTransport_nonneg (traceField β hβ) (siteCoordinates n ls) (siteBlock n l) t
        (ih (q+l.2) l.1 h.2) x)
end ParisiGuerra

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiGuerra
open ParisiFinite SKQAOA SKGaussian ParisiInterpolation

lemma frontier_add_coordinates {n : ℕ} (hn : 0 < n) (ls : Schedule) (q t : ℝ) :
    frontierKernel n q t + coordinatesKernel (siteCoordinates n ls) t =
      frontierKernel n (q+width ls) t := by
  induction ls generalizing q with
  | nil => simp [siteCoordinates, coordinatesKernel_nil, width]
  | cons l ls ih =>
    change frontierKernel n q t + coordinatesKernel (siteBlock n l ++ siteCoordinates n ls) t = _
    rw [coordinatesKernel_append, ← add_assoc, frontier_add_site hn, ih]
    congr 1
    simp [width, add_assoc]

lemma complete_covariance {n : ℕ} (hn : 0 < n) (ls : Schedule) (t : ℝ) :
    kernelNoise (allNoise (coordinates n ls) t []) = frontierKernel n (width ls) t := by
  rw [kernelNoise_allNoise]
  simp only [kernelNoise, zero_add]
  rw [coordinates, coordinatesKernel_append, costBlock_frontier hn, frontier_add_coordinates hn]
  simp only [zero_add]

lemma complete_diagonal {n : ℕ} (hn : 0 < n) (ls : Schedule) (hw : width ls=1) (t : ℝ) :
    diagonalNoise (allNoise (coordinates n ls) t []) =
      fun _ => -(Real.sin t*Real.cos t)*((n:ℝ)+1)/2 := by
  ext σ
  rw [← kernelNoise_diagonal, complete_covariance hn, hw]
  unfold frontierKernel overlap
  rw [overlapSum_self, div_self (Nat.cast_ne_zero.mpr hn.ne')]
  ring

 
def correction (n : ℕ) (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule) (t : ℝ) : ℝ :=
  prefixTransport (traceField β hβ) (siteCoordinates n ls) (costBlock n) t
    (siteCorrection n β hβ ls 0 0 t) 0

lemma correction_nonneg (n : ℕ) (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule)
    (hl : Admissible β ls) (t : ℝ) : 0 ≤ correction n β hβ ls t :=
  prefixTransport_nonneg _ _ _ t (siteCorrection_nonneg n β hβ ls 0 0 t (admissible_ordered hl)) 0

lemma complete_remainder {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hw : width ls=1) (t : ℝ) :
    hierarchyRemainder (traceField β hβ) β (coordinates n ls) t 0 [] 0 =
      Real.sin t*Real.cos t*(n:ℝ)/2 * correction n β hβ ls t -
        Real.sin t*Real.cos t*((n:ℝ)/2*((β:ℝ)-4*penalty 0 ls)+(β:ℝ)/2) := by
  have hv : kernelNoise (allNoise (costBlock n) t []) = frontierKernel n 0 t := by
    rw [kernelNoise_allNoise]
    simp only [kernelNoise, zero_add, costBlock_frontier hn]
  have he := remainder_constant_prefix (traceField β hβ) β 0 (costBlock n) (siteCoordinates n ls) t [] (costBlock_gamma n)
  change hierarchyRemainder (traceField β hβ) β (coordinates n ls) t 0 [] = _ at he
  simp only [NNReal.coe_zero] at he
  rw [site_remainder hn β hβ ls 0 0 t _ hv, map_sub, map_smul, prefixTransport_const] at he
  rw [he, jumpSquares_eq, hw]
  simp only [zero_add, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero,
    BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.const_apply, smul_eq_mul, correction]

 

lemma hasDerivAt_pressureCurve {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hw : width ls=1) (t : ℝ) :
    HasDerivAt (pressureCurve n β ls)
      (-2*(n:ℝ)*Real.sin t*Real.cos t*penalty 0 ls -
        (n:ℝ)/2*Real.sin t*Real.cos t*correction n β hβ ls t) t := by
  have hd := hierarchy_derivative_sum_rule β hβ (coordinates n ls) t 0
  rw [complete_diagonal hn ls hw, spinObserve_const, complete_remainder hn β hβ ls hw] at hd
  convert hd using 1
  · rfl
  · simp only [BoundedContinuousFunction.const_apply]
    ring
end ParisiGuerra

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiGuerra
open ParisiFinite SKQAOA SKGaussian ParisiInterpolation

lemma continuous_dot_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : FieldFamily E) (x : E) : Continuous (fun t => F.dot t x) :=
  F.continuousDot.comp (continuous_id.prodMk continuous_const)

lemma continuous_weighted_correction {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hw : width ls=1) :
    Continuous (fun t => Real.sin t*Real.cos t*correction n β hβ ls t) := by
  let d := fun t => (hierarchy (traceField β hβ) (coordinates n ls)).dot t 0
  have hc : Continuous d := continuous_dot_at (hierarchy (traceField β hβ) (coordinates n ls)) 0
  have he (t : ℝ) : d t = -2*(n:ℝ)*Real.sin t*Real.cos t*penalty 0 ls -
      (n:ℝ)/2*Real.sin t*Real.cos t*correction n β hβ ls t :=
    (hasDerivAt_hierarchyValue (traceField β hβ) (coordinates n ls) t 0).unique
      (hasDerivAt_pressureCurve hn β hβ ls hw t)
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hf : (fun t => Real.sin t*Real.cos t*correction n β hβ ls t) =
      fun t => (-2*(n:ℝ)*Real.sin t*Real.cos t*penalty 0 ls-d t)*2/(n:ℝ) := by
    funext t
    rw [he t]
    field_simp [hn']
    ring
  rw [hf]
  have hh : Continuous (fun t => -2*(n:ℝ)*Real.sin t*Real.cos t*penalty 0 ls) := by fun_prop
  exact ((hh.sub hc).mul_const 2).div_const _

lemma hasDerivAt_correctedCurve {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hw : width ls=1) (t : ℝ) :
    HasDerivAt (fun s => pressureCurve n β ls s + (n:ℝ)*penalty 0 ls*(Real.sin s)^2)
      (-(n:ℝ)/2*(Real.sin t*Real.cos t*correction n β hβ ls t)) t := by
  convert (hasDerivAt_pressureCurve hn β hβ ls hw t).add
    (((Real.hasDerivAt_sin t).pow 2).const_mul ((n:ℝ)*penalty 0 ls)) using 1
  first | rfl | ring

 

lemma curve_sum_rule {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hw : width ls=1) :
    pressureCurve n β ls (Real.pi/2) = pressureCurve n β ls 0 - (n:ℝ)*penalty 0 ls -
      (n:ℝ)/2*∫ t in (0:ℝ)..(Real.pi/2), Real.sin t*Real.cos t*correction n β hβ ls t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_correctedCurve hn β hβ ls hw t)
    (((continuous_weighted_correction hn β hβ ls hw).const_mul (-(n:ℝ)/2)).intervalIntegrable 0 (Real.pi/2))
  rw [intervalIntegral.integral_const_mul] at h
  simp only [Real.sin_pi_div_two, one_pow, mul_one, Real.sin_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, add_zero] at h
  linarith

lemma integrated_correction_nonneg (n : ℕ) (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule)
    (hl : Admissible β ls) :
    0 ≤ ∫ t in (0:ℝ)..(Real.pi/2), Real.sin t*Real.cos t*correction n β hβ ls t := by
  apply intervalIntegral.integral_nonneg (by positivity)
  intro t ht
  apply mul_nonneg
  · apply mul_nonneg
    · exact Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans (by linarith [Real.pi_pos]))
    · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
  · exact correction_nonneg n β hβ ls hl t

lemma curve_upper_bound {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hl : Admissible β ls) :
    pressureCurve n β ls (Real.pi/2) ≤ pressureCurve n β ls 0 - (n:ℝ)*penalty 0 ls := by
  rw [curve_sum_rule hn β hβ ls hl.1]
  exact sub_le_self _ (mul_nonneg (by positivity) (integrated_correction_nonneg n β hβ ls hl))
end ParisiGuerra

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma hierarchyValue_append (f : E → ℝ) (pre tail : List (MovingCoordinate E)) (t : ℝ) :
    hierarchyValue f (pre++tail) t = hierarchyValue (hierarchyValue f tail t) pre t := by
  induction pre with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, hierarchyValue, ih]
end ParisiFinite
namespace ParisiGuerra
open ParisiFinite SKQAOA SKGaussian ParisiInterpolation

def siteField (n : ℕ) (x : Fin n → ℝ) (σ : Configuration n) : ℝ := ∑ i, x i*spin σ i

lemma siteField_zero (n : ℕ) : siteField n 0 = 0 := by ext σ; simp [siteField]

lemma siteField_update (n : ℕ) (x : Fin n → ℝ) (i : Fin n) (s z : ℝ) :
    siteField n x + z • (fun σ => s*spin σ i) = siteField n (Function.update x i (x i+s*z)) := by
  ext σ
  simp only [siteField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  have he : (∑ j ∈ Finset.univ.erase i, Function.update x i (x i+s*z) j*spin σ j) =
      ∑ j ∈ Finset.univ.erase i, x j*spin σ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  ring

lemma site_sum_update {n : ℕ} (fs : Fin n → ℝ → ℝ) (x : Fin n → ℝ) (i : Fin n) (y : ℝ) :
    (∑ j, fs j (Function.update x i y j)) = fs i y + ∑ j ∈ Finset.univ.erase i, fs j (x j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

 
lemma ambientStep_site {n : ℕ} {L : ℝ≥0} {g : ℝ → ℝ} (hg : LipschitzWith L g)
    (a s : ℝ) (f : (Configuration n → ℝ) → ℝ) (fs : Fin n → ℝ → ℝ) (i : Fin n)
    (hfi : fs i = g) (hf : ∀ x, f (siteField n x) = ∑ j, fs j (x j)) (x : Fin n → ℝ) :
    ambientStep a (fun σ => s*spin σ i) f (siteField n x) =
      step a s g (x i) + ∑ j ∈ Finset.univ.erase i, fs j (x j) := by
  unfold ambientStep
  have he (z : ℝ) : f (siteField n x+z • (fun σ => s*spin σ i)) =
      g (x i+s*z)+∑ j ∈ Finset.univ.erase i, fs j (x j) := by
    rw [siteField_update, hf, site_sum_update, hfi]
  simp_rw [he]
  exact logMean_add_const (integrable_shift hg (x i) s) (integrable_exp_shift hg a (x i) s) _

lemma siteList_endpoint {n : ℕ} {L : ℝ≥0} {g : ℝ → ℝ} (hg : LipschitzWith L g)
    (a : ℝ≥0) (s : ℝ) (f : (Configuration n → ℝ) → ℝ)
    (hf : ∀ x, f (siteField n x) = ∑ j, g (x j)) (is : List (Fin n)) (hi : is.Nodup)
    (x : Fin n → ℝ) :
    hierarchyValue f (is.map (fun i => MovingCoordinate.cosine a (fun σ => s*spin σ i))) 0 (siteField n x) =
      ∑ j, (if j ∈ is then step a s g else g) (x j) := by
  induction is generalizing x with
  | nil => simpa only [List.map_nil, hierarchyValue, List.not_mem_nil, ite_false] using hf x
  | cons i is ih =>
    have hi' := List.nodup_cons.mp hi
    change ambientStep a ((Real.cos 0) • (fun σ => s*spin σ i))
      (hierarchyValue f (is.map (fun j => MovingCoordinate.cosine a (fun σ => s*spin σ j))) 0)
      (siteField n x) = _
    rw [Real.cos_zero, one_smul]
    rw [ambientStep_site hg a s _ (fun j => if j∈is then step a s g else g) i
      (by simp [hi'.1]) (fun y => ih hi'.2 y)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [List.mem_cons, true_or, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [hji, false_or]

lemma siteBlock_endpoint {n : ℕ} {L : ℝ≥0} {g : ℝ → ℝ} (hg : LipschitzWith L g)
    (l : ℝ≥0 × ℝ≥0) (f : (Configuration n → ℝ) → ℝ)
    (hf : ∀ x, f (siteField n x) = ∑ j, g (x j)) (x : Fin n → ℝ) :
    hierarchyValue f (siteBlock n l) 0 (siteField n x) =
      ∑ j, step l.1 (Real.sqrt l.2) g (x j) := by
  change ambientStep l.1 ((0 : ℝ) • (0 : Configuration n → ℝ)) (hierarchyValue f
    (List.ofFn (fun i : Fin n => MovingCoordinate.cosine l.1 (fun σ => Real.sqrt l.2*spin σ i))) 0) (siteField n x) = _
  rw [zero_smul, ambientStep_zero_direction]
  have he : (List.finRange n).map (fun i => MovingCoordinate.cosine l.1 (fun σ => Real.sqrt l.2*spin σ i)) =
      List.ofFn (fun i : Fin n => MovingCoordinate.cosine l.1 (fun σ => Real.sqrt l.2*spin σ i)) := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  rw [← he, siteList_endpoint hg l.1 (Real.sqrt l.2) f hf _ (List.nodup_finRange n)]
  simp

lemma spinTrace_site (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    spinTrace β (siteField n x) = ∑ i, terminal β (x i) := by
  have he : (fun σ => β*siteField n x σ) = fun σ => ∑ i, (β*x i)*spin σ i := by
    ext σ
    simp only [siteField, Finset.mul_sum, mul_assoc]
  rw [spinTrace, he, logPartition_site]
  simp only [terminal, Finset.sum_div]

lemma siteCoordinates_endpoint (n : ℕ) {β : ℝ} (hβ : 0 < β) (ls : Schedule) (x : Fin n → ℝ) :
    hierarchyValue (spinTrace β) (siteCoordinates n ls) 0 (siteField n x) =
      ∑ i, recursion β ls (x i) := by
  induction ls generalizing x with
  | nil => exact spinTrace_site n β x
  | cons l ls ih =>
    change hierarchyValue (spinTrace β) (siteBlock n l++siteCoordinates n ls) 0 (siteField n x) = _
    rw [hierarchyValue_append, siteBlock_endpoint (recursion_lipschitz hβ ls) l _ ih]
    rfl

lemma costBlock_zero {n : ℕ} (f : (Configuration n → ℝ) → ℝ) :
    hierarchyValue f (costBlock n) 0 = f := by
  apply hierarchyValue_zero_scales
  intro c hc
  simp only [costBlock, List.mem_cons, List.mem_ofFn] at hc
  rcases hc with rfl | ⟨i,rfl⟩
  · rfl
  · exact Real.sin_zero

 

lemma pressureCurve_zero (n : ℕ) {β : ℝ} (hβ : 0 < β) (ls : Schedule) :
    pressureCurve n β ls 0 = (n:ℝ)*recursion β ls 0 := by
  unfold pressureCurve coordinates
  rw [hierarchyValue_append, costBlock_zero, ← siteField_zero n, siteCoordinates_endpoint n hβ]
  simp
end ParisiGuerra

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
open SKGaussian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integrable_gaussian_linear {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    {k : ℕ} (v : Fin k → E) (x : E) :
    Integrable (fun z : Fin k → ℝ => f (x+∑ i, z i • v i)) (standardLaw k) := by
  have hm : Integrable (fun z : Fin k → ℝ => |f x|+(L:ℝ)*∑ i, |z i| *‖v i‖) (standardLaw k) := by
    apply (integrable_const _).add
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i _
    exact (integrable_coordinate i).norm.mul_const _
  apply hm.mono' (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with z
  have h := hf.norm_sub_le (x+∑ i, z i • v i) x
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at h
  have hsum : ‖∑ i, z i • v i‖ ≤ ∑ i, |z i| *‖v i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le (Finset.univ) (fun i => z i • v i)
  have htri := abs_add_le (f (x+∑ i, z i • v i)-f x) (f x)
  rw [sub_add_cancel] at htri
  simp only [Real.norm_eq_abs, Function.comp_apply]
  nlinarith [L.coe_nonneg]

 
lemma integral_gaussian_fin_cons {k : ℕ} {F : (Fin (k+1) → ℝ) → ℝ}
    (hF : Integrable F (standardLaw (k+1))) :
    (∫ z, F z ∂standardLaw (k+1)) =
      ∫ s : ℝ, ∫ z : Fin k → ℝ, F (Fin.cons s z) ∂standardLaw k ∂gaussianReal 0 1 := by
  let T := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) 0).symm
  have hm : MeasurePreserving T ((gaussianReal 0 1).prod (standardLaw k)) (standardLaw (k+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => gaussianReal 0 1) 0).symm
  have hi : Integrable (fun p => F (T p)) ((gaussianReal 0 1).prod (standardLaw k)) :=
    (hm.integrable_comp hF.aestronglyMeasurable).mpr hF
  have he (p : ℝ × (Fin k → ℝ)) : T p = Fin.cons p.1 p.2 := by
    simp [T, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [← hm.integral_comp' F, integral_prod _ hi]
  simp_rw [he]

 

lemma hierarchyValue_gaussian {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    {k : ℕ} (v : Fin k → E) (x : E) :
    hierarchyValue f (List.ofFn (fun i => MovingCoordinate.sine 0 (v i))) (Real.pi/2) x =
      ∫ z, f (x+∑ i, z i • v i) ∂standardLaw k := by
  induction k generalizing x with
  | zero => simp [hierarchyValue]
  | succ k ih =>
    rw [List.ofFn_succ]
    change ambientStep 0 ((Real.sin (Real.pi/2)) • v 0)
      (hierarchyValue f (List.ofFn (fun i : Fin k => MovingCoordinate.sine 0 (v i.succ))) (Real.pi/2)) x = _
    rw [Real.sin_pi_div_two, one_smul]
    simp only [ambientStep, logMean_zero]
    simp_rw [ih]
    rw [integral_gaussian_fin_cons (integrable_gaussian_linear hf v x)]
    apply integral_congr_ae
    filter_upwards with s
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    abel
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiGuerra
open ParisiFinite SKQAOA SKGaussian ParisiInterpolation

lemma siteCoordinates_zero_width (n : ℕ) (ls : Schedule) (f : (Configuration n → ℝ) → ℝ) :
    hierarchyValue f (siteCoordinates n ls) (Real.pi/2) = f := by
  apply hierarchyValue_zero_scales
  intro c hc
  simp only [siteCoordinates, List.mem_flatMap] at hc
  obtain ⟨l, _, hc⟩ := hc
  simp only [siteBlock, List.mem_cons, List.mem_ofFn] at hc
  rcases hc with rfl | ⟨i,rfl⟩
  · rfl
  · exact Real.cos_pi_div_two

lemma costBlock_expectation (n : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    hierarchyValue (spinTrace β) (costBlock n) (Real.pi/2) 0 = pressure β n / β := by
  change ambientStep 0 ((0:ℝ) • (0:Configuration n → ℝ))
    (hierarchyValue (spinTrace β) (List.ofFn (fun k : Fin (Fintype.card (Edge n)) =>
      MovingCoordinate.sine 0 (fun σ => skCoeff n σ ((Fintype.equivFin (Edge n)).symm k)))) (Real.pi/2)) 0 = _
  rw [zero_smul, ambientStep_zero_direction, hierarchyValue_gaussian (spinTrace_lipschitz hβ)]
  have he (z : Fin (Fintype.card (Edge n)) → ℝ) :
      (0:Configuration n → ℝ)+∑ k, z k • (fun σ => skCoeff n σ ((Fintype.equivFin (Edge n)).symm k)) =
        linearField (fun σ k => skCoeff n σ ((Fintype.equivFin (Edge n)).symm k)) z := by
    ext σ
    simp [linearField, mul_comm]
  simp_rw [he]
  rw [integral_reindex_field (skCoeff n) (spinTrace β)]
  simp_rw [spinTrace, field_skCoeff]
  rw [integral_div]
  rfl

 

lemma pressureCurve_pi_div_two (n : ℕ) {β : ℝ} (hβ : β ≠ 0) (ls : Schedule) :
    pressureCurve n β ls (Real.pi/2) = pressure β n / β := by
  unfold pressureCurve coordinates
  rw [hierarchyValue_append, siteCoordinates_zero_width, costBlock_expectation n hβ]

 

lemma freeEnergy_sum_rule {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hw : width ls=1) :
    freeEnergy β n = functional β ls -
      (1/2:ℝ)*∫ t in (0:ℝ)..(Real.pi/2), Real.sin t*Real.cos t*correction n β hβ ls t := by
  have hβ' : (0:ℝ) < β := hβ
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h := curve_sum_rule hn β hβ ls hw
  rw [pressureCurve_pi_div_two n hβ'.ne', pressureCurve_zero n hβ'] at h
  unfold freeEnergy functional
  calc
    pressure β n / (n:ℝ) / β = (pressure β n / β) / (n:ℝ) := by ring
    _ = _ := by rw [h]; field_simp [hn']

lemma freeEnergy_le_functional {n : ℕ} (hn : 0 < n) (β : ℝ≥0) (hβ : 0 < β)
    (ls : Schedule) (hl : Admissible β ls) : freeEnergy β n ≤ functional β ls := by
  rw [freeEnergy_sum_rule hn β hβ ls hl.1]
  exact sub_le_self _ (mul_nonneg (by norm_num) (integrated_correction_nonneg n β hβ ls hl))

lemma limitingFreeEnergy_le_functional (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule)
    (hl : Admissible β ls) : limitingFreeEnergy β ≤ functional β ls :=
  le_of_tendsto (tendsto_freeEnergy hβ) ((eventually_gt_atTop 0).mono fun _ hn =>
    freeEnergy_le_functional hn β hβ ls hl)
end ParisiGuerra

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace SKCavity
open SKGaussian SKQAOA ParisiInterpolation

 
def kernel {ι κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (s t : ι) : ℝ :=
  ∑ k, A s k * A t k

lemma squared_increment {ι κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (s t : ι) :
    (∑ k, (A s k-A t k)^2) = kernel A s s+kernel A t t-2*kernel A s t := by
  simp only [kernel, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma kernel_scale {ι κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (a : ℝ) (s t : ι) :
    kernel (fun s k => a*A s k) s t = a^2*kernel A s t := by
  simp only [kernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

lemma expected_logPartition_eq_of_kernel {ι κ κ' : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Fintype κ'] (A : ι → κ → ℝ) (B : ι → κ' → ℝ)
    (h : ∀ s t, kernel A s t = kernel B s t) :
    (∫ z, logPartition (field A z) ∂gaussianLaw κ) =
      ∫ z, logPartition (field B z) ∂gaussianLaw κ' := by
  have he (s t : ι) : (∑ k, (A s k-A t k)^2) = ∑ k, (B s k-B t k)^2 := by
    simp only [squared_increment, h]
  exact le_antisymm (expected_field_logPartition_le A B (fun s t => (he s t).le))
    (expected_field_logPartition_le B A (fun s t => (he s t).ge))

 
def coreScale (n : ℕ) : ℝ := Real.sqrt n / Real.sqrt (n+1)
 
def cavityScale (n : ℕ) : ℝ := (Real.sqrt (n+1))⁻¹

lemma coreScale_sq (n : ℕ) : coreScale n ^ 2 = (n:ℝ)/(n+1) := by
  unfold coreScale
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (by positivity)]

lemma cavityScale_sq (n : ℕ) : cavityScale n ^ 2 = 1/((n:ℝ)+1) := by
  unfold cavityScale
  rw [inv_pow, Real.sq_sqrt (by positivity), one_div]

lemma scales_sum (n : ℕ) : coreScale n ^ 2+cavityScale n ^ 2=1 := by
  rw [coreScale_sq, cavityScale_sq]
  field_simp

 
def cavityCoeff (n : ℕ) (σ : Configuration (n+1)) : Edge n ⊕ Fin n → ℝ :=
  Sum.elim (fun e => coreScale n*skCoeff n (restrictLeft σ) e)
    (fun i => cavityScale n*spin σ (Fin.last n)*spin (restrictLeft σ) i)

lemma overlapSum_last (n : ℕ) (σ τ : Configuration (n+1)) :
    overlapSum σ τ = overlapSum (restrictLeft σ) (restrictLeft τ)+
      spin σ (Fin.last n)*spin τ (Fin.last n) := by
  unfold overlapSum
  exact Fin.sum_univ_castSucc _

lemma cavityCoeff_kernel {n : ℕ} (hn : 0 < n) (σ τ : Configuration (n+1)) :
    kernel (cavityCoeff n) σ τ = kernel (skCoeff (n+1)) σ τ := by
  have hb : (∑ e : Edge n,
      (coreScale n*skCoeff n (restrictLeft σ) e)*(coreScale n*skCoeff n (restrictLeft τ) e)) =
      coreScale n^2 * (overlapSum (restrictLeft σ) (restrictLeft τ)^2-(n:ℝ))/(2*n) := by
    change kernel (fun s e => coreScale n*skCoeff n s e) (restrictLeft σ) (restrictLeft τ) = _
    rw [kernel_scale, kernel, coeff_covariance hn]
    ring
  have hz : (∑ i : Fin n,
      (cavityScale n*spin σ (Fin.last n)*spin (restrictLeft σ) i)*
        (cavityScale n*spin τ (Fin.last n)*spin (restrictLeft τ) i)) =
      cavityScale n^2*(spin σ (Fin.last n)*spin τ (Fin.last n))*
        overlapSum (restrictLeft σ) (restrictLeft τ) := by
    simp only [overlapSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ k, cavityCoeff n σ k*cavityCoeff n τ k) = _
  simp only [cavityCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [hb, hz, kernel, coeff_covariance (Nat.succ_pos n), overlapSum_last,
    coreScale_sq, cavityScale_sq]
  have hs : (spin σ (Fin.last n)*spin τ (Fin.last n))^2=1 := by
    rw [mul_pow, spin_sq, spin_sq, one_mul]
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  push_cast
  field_simp [hn']
  nlinarith only [hs]

 

def correctedCoeff (n : ℕ) (σ : Configuration n) : Edge n ⊕ Edge n → ℝ :=
  Sum.elim (fun e => coreScale n*skCoeff n σ e) (fun e => cavityScale n*skCoeff n σ e)

lemma correctedCoeff_kernel (n : ℕ) (σ τ : Configuration n) :
    kernel (correctedCoeff n) σ τ = kernel (skCoeff n) σ τ := by
  change (∑ k, correctedCoeff n σ k*correctedCoeff n τ k)=_
  simp only [correctedCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  change kernel (fun s e => coreScale n*skCoeff n s e) σ τ+
    kernel (fun s e => cavityScale n*skCoeff n s e) σ τ=_
  rw [kernel_scale, kernel_scale, ← add_mul, scales_sum, one_mul]

lemma expected_cavity_pressure {n : ℕ} (hn : 0 < n) (β : ℝ) :
    (∫ z, logPartition (fun σ => β*field (cavityCoeff n) z σ)
      ∂gaussianLaw (Edge n ⊕ Fin n))=pressure β (n+1) := by
  simp_rw [← field_scale]
  rw [expected_logPartition_eq_of_kernel _ (fun σ e => β*skCoeff (n+1) σ e)
    (fun σ τ => by rw [kernel_scale, kernel_scale, cavityCoeff_kernel hn])]
  simp_rw [field_scale, field_skCoeff]
  rfl

lemma expected_corrected_pressure (n : ℕ) (β : ℝ) :
    (∫ z, logPartition (fun σ => β*field (correctedCoeff n) z σ)
      ∂gaussianLaw (Edge n ⊕ Edge n))=pressure β n := by
  simp_rw [← field_scale]
  rw [expected_logPartition_eq_of_kernel _ (fun σ e => β*skCoeff n σ e)
    (fun σ τ => by rw [kernel_scale, kernel_scale, correctedCoeff_kernel])]
  simp_rw [field_scale, field_skCoeff]
  rfl
end SKCavity

end

end OAI
