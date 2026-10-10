import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.TransverseZeroKernel
import OAI.Geometry.SmoothYau.Smoothness.RepresentedWeightedQuinticSmooth

namespace OAI

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples.BoundedAlgebra
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def power (p : A →L[ℝ] A →L[ℝ] A) (e x : A) : ℕ → A :=
  Nat.rec e (fun _ y => p x y)

lemma norm_power (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U r : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hr : 0 ≤ r) {x : A} (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖power p e x n‖ ≤ K ^ n * U * r ^ n := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  induction n with
  | zero => simpa only [power, Nat.rec_zero, pow_zero, one_mul, mul_one] using hU
  | succ n ih =>
    change ‖p x (power p e x n)‖ ≤ _
    calc
      _ ≤ ‖p‖ * ‖x‖ * ‖power p e x n‖ := p.le_opNorm₂ _ _
      _ ≤ K * r * (K ^ n * U * r ^ n) := by gcongr
      _ = K ^ (n + 1) * U * r ^ (n + 1) := by ring

lemma power_difference (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U r : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hr : 0 ≤ r) {x y : A}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖power p e x (n + 1) - power p e y (n + 1)‖ ≤
      (n + 1 : ℝ) * K ^ (n + 1) * U * r ^ n * ‖x - y‖ := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  induction n with
  | zero =>
    change ‖p x e - p y e‖ ≤ _
    rw [← sub_apply, ← map_sub]
    calc
      _ ≤ ‖p‖ * ‖x - y‖ * ‖e‖ := p.le_opNorm₂ _ _
      _ ≤ K * ‖x - y‖ * U := by gcongr
      _ = ((0 : ℕ) + 1 : ℝ) * K ^ (0 + 1) * U * r ^ 0 * ‖x - y‖ := by ring
  | succ n ih =>
    have hid : power p e x (n + 1 + 1) - power p e y (n + 1 + 1) =
        p x (power p e x (n + 1) - power p e y (n + 1)) +
        p (x - y) (power p e y (n + 1)) := by
      simp only [power, map_sub, sub_apply]
      abel
    rw [hid]
    calc
      _ ≤ ‖p‖ * ‖x‖ * ‖power p e x (n + 1) - power p e y (n + 1)‖ +
          ‖p‖ * ‖x - y‖ * ‖power p e y (n + 1)‖ :=
        (norm_add_le _ _).trans (add_le_add (p.le_opNorm₂ _ _) (p.le_opNorm₂ _ _))
      _ ≤ K * r * ((n + 1 : ℝ) * K ^ (n + 1) * U * r ^ n * ‖x - y‖) +
          K * ‖x - y‖ * (K ^ (n + 1) * U * r ^ (n + 1)) := by
        gcongr
        exact norm_power p e hK hU hr hy (n + 1)
      _ = (↑(n + 1) + 1 : ℝ) * K ^ (n + 1 + 1) * U * r ^ (n + 1) * ‖x - y‖ := by
        push_cast
        ring

lemma power_difference_small (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U δ : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : A}
    (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) (n : ℕ) :
    ‖power p e x (n + 2) - power p e y (n + 2)‖ ≤
      (n + 2 : ℝ) * K ^ (n + 2) * U * δ * ‖x - y‖ := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  have hpow : δ ^ (n + 1) ≤ δ := by
    calc
      _ = δ * δ ^ n := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hδ hδ1) hδ
      _ = δ := mul_one _
  calc
    _ ≤ (↑(n + 1) + 1 : ℝ) * K ^ (n + 1 + 1) * U * δ ^ (n + 1) * ‖x - y‖ :=
      power_difference p e hK hU hδ hx hy (n + 1)
    _ = (n + 2 : ℝ) * K ^ (n + 2) * U * δ ^ (n + 1) * ‖x - y‖ := by push_cast; ring
    _ ≤ (n + 2 : ℝ) * K ^ (n + 2) * U * δ * ‖x - y‖ := by gcongr

def remainder (p : A →L[ℝ] A →L[ℝ] A) (e h : A) : A :=
  (10 : ℝ) • power p e h 2 + (10 : ℝ) • power p e h 3 +
    (5 : ℝ) • power p e h 4 + power p e h 5

def remainderConstant (K U : ℝ) : ℝ :=
  20 * K ^ 2 * U + 30 * K ^ 3 * U + 20 * K ^ 4 * U + 5 * K ^ 5 * U

lemma remainder_zero (p : A →L[ℝ] A →L[ℝ] A) (e : A) : remainder p e 0 = 0 := by
  have hz (n : ℕ) : power p e 0 (n + 1) = 0 := by
    change p 0 _ = 0
    simp
  simp only [remainder, hz, smul_zero, add_zero]

lemma remainder_lipschitz (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U δ : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : A}
    (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖remainder p e x - remainder p e y‖ ≤ remainderConstant K U * δ * ‖x - y‖ := by
  have hid : remainder p e x - remainder p e y =
      (10 : ℝ) • (power p e x 2 - power p e y 2) +
      (10 : ℝ) • (power p e x 3 - power p e y 3) +
      (5 : ℝ) • (power p e x 4 - power p e y 4) +
      (power p e x 5 - power p e y 5) := by simp only [remainder, smul_sub]; abel
  rw [hid]
  have hn (c : ℝ) (hc : 0 ≤ c) (v : A) : ‖c • v‖ = c * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ 10 * ‖power p e x 2 - power p e y 2‖ +
        10 * ‖power p e x 3 - power p e y 3‖ +
        5 * ‖power p e x 4 - power p e y 4‖ + ‖power p e x 5 - power p e y 5‖ := by
      calc
        _ ≤ ‖(10 : ℝ) • (power p e x 2 - power p e y 2) +
          (10 : ℝ) • (power p e x 3 - power p e y 3) +
          (5 : ℝ) • (power p e x 4 - power p e y 4)‖ +
          ‖power p e x 5 - power p e y 5‖ := norm_add_le _ _
        _ ≤ (‖(10 : ℝ) • (power p e x 2 - power p e y 2) +
          (10 : ℝ) • (power p e x 3 - power p e y 3)‖ +
          ‖(5 : ℝ) • (power p e x 4 - power p e y 4)‖) +
          ‖power p e x 5 - power p e y 5‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (‖(10 : ℝ) • (power p e x 2 - power p e y 2)‖ +
          ‖(10 : ℝ) • (power p e x 3 - power p e y 3)‖ +
          ‖(5 : ℝ) • (power p e x 4 - power p e y 4)‖) +
          ‖power p e x 5 - power p e y 5‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by rw [hn 10 (by norm_num), hn 10 (by norm_num), hn 5 (by norm_num)]
    _ ≤ 10 * (2 * K ^ 2 * U * δ * ‖x - y‖) +
        10 * (3 * K ^ 3 * U * δ * ‖x - y‖) +
        5 * (4 * K ^ 4 * U * δ * ‖x - y‖) + 5 * K ^ 5 * U * δ * ‖x - y‖ := by
      gcongr
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 0
        norm_num at h
        exact h
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 1
        norm_num at h
        exact h
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 2
        norm_num at h
        exact h
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 3
        norm_num at h
        exact h
    _ = remainderConstant K U * δ * ‖x - y‖ := by unfold remainderConstant; ring

def polynomial (p : A →L[ℝ] A →L[ℝ] A) (e c s h : A) : A :=
  (c - s) + p ((5 : ℝ) • (c - e) - (s - e)) h + p c (remainder p e h)

lemma polynomial_zero_bound (p : A →L[ℝ] A →L[ℝ] A) (e : A) {c s : A} {ε C : ℝ}
    (hc : ‖c - e‖ ≤ C * ε) (hs : ‖s - e‖ ≤ ε) :
    ‖polynomial p e c s 0‖ ≤ (C + 1) * ε := by
  simp only [polynomial, map_zero, remainder_zero, add_zero]
  have hid : c - s = (c - e) - (s - e) := by abel
  rw [hid]
  calc
    _ ≤ ‖c - e‖ + ‖s - e‖ := norm_sub_le _ _
    _ ≤ C * ε + ε := add_le_add hc hs
    _ = (C + 1) * ε := by ring

lemma polynomial_lipschitz (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U ε δ C V : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) {c s : A}
    (hc : ‖c - e‖ ≤ C * ε) (hs : ‖s - e‖ ≤ ε) (hc' : ‖c‖ ≤ V)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : A} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖polynomial p e c s x - polynomial p e c s y‖ ≤
      (K * (5 * C + 1) * ε + K * V * remainderConstant K U * δ) * ‖x - y‖ := by
  have hK0 := (norm_nonneg p).trans hK
  have hV0 := (norm_nonneg c).trans hc'
  have hlin : ‖(5 : ℝ) • (c - e) - (s - e)‖ ≤ (5 * C + 1) * ε := by
    calc
      _ ≤ ‖(5 : ℝ) • (c - e)‖ + ‖s - e‖ := norm_sub_le _ _
      _ = 5 * ‖c - e‖ + ‖s - e‖ := by rw [norm_smul]; norm_num
      _ ≤ 5 * (C * ε) + ε := by gcongr
      _ = (5 * C + 1) * ε := by ring
  have hid : polynomial p e c s x - polynomial p e c s y =
      p ((5 : ℝ) • (c - e) - (s - e)) (x - y) + p c (remainder p e x - remainder p e y) := by
    simp only [polynomial, map_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖p‖ * ‖(5 : ℝ) • (c - e) - (s - e)‖ * ‖x - y‖ +
        ‖p‖ * ‖c‖ * ‖remainder p e x - remainder p e y‖ :=
      (norm_add_le _ _).trans (add_le_add (p.le_opNorm₂ _ _) (p.le_opNorm₂ _ _))
    _ ≤ K * ((5 * C + 1) * ε) * ‖x - y‖ +
        K * V * (remainderConstant K U * δ * ‖x - y‖) := by
      gcongr
      exact remainder_lipschitz p e hK hU hδ hδ1 hx hy
    _ = (K * (5 * C + 1) * ε + K * V * remainderConstant K U * δ) * ‖x - y‖ := by ring

variable [CompleteSpace A]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem solve (R : B →L[ℝ] A) (I D : A →L[ℝ] B) (P : A → A)
    (Λ δ L Z : ℝ) (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hP : ∀ x y, ‖x‖ ≤ δ → ‖y‖ ≤ δ → ‖P x - P y‖ ≤ L * ‖x - y‖)
    (hP0 : ‖P 0‖ ≤ Z)
    (hsmall : ‖R‖ * (‖D‖ + Λ * ‖I‖ * L) ≤ 1 / 2)
    (hstart : ‖R‖ * Λ * ‖I‖ * Z ≤ δ / 2) :
    ∃ h : A, ‖h‖ ≤ δ ∧ h = R (D h - Λ • I (P h)) := by
  let T : A → A := fun h => R (D h - Λ • I (P h))
  have hTlip (x y : A) (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
      ‖T x - T y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have hid : T x - T y = R (D (x - y) - Λ • I (P x - P y)) := by
      simp only [T, map_sub, smul_sub]; abel
    rw [hid]
    calc
      _ ≤ ‖R‖ * ‖D (x - y) - Λ • I (P x - P y)‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (‖D‖ * ‖x - y‖ + Λ * (‖I‖ * ‖P x - P y‖)) := by
        gcongr
        calc
          _ ≤ ‖D (x - y)‖ + ‖Λ • I (P x - P y)‖ := norm_sub_le _ _
          _ = ‖D (x - y)‖ + Λ * ‖I (P x - P y)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΛ]
          _ ≤ _ := add_le_add (D.le_opNorm _) (mul_le_mul_of_nonneg_left (I.le_opNorm _) hΛ)
      _ ≤ ‖R‖ * (‖D‖ * ‖x - y‖ + Λ * (‖I‖ * (L * ‖x - y‖))) := by
        gcongr
        exact hP x y hx hy
      _ = (‖R‖ * (‖D‖ + Λ * ‖I‖ * L)) * ‖x - y‖ := by ring
      _ ≤ (1 / 2 : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hTzero : ‖T 0‖ ≤ δ / 2 := by
    simp only [T, map_zero, zero_sub, map_neg, norm_neg]
    calc
      _ ≤ ‖R‖ * ‖Λ • I (P 0)‖ := R.le_opNorm _
      _ = ‖R‖ * (Λ * ‖I (P 0)‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΛ]
      _ ≤ ‖R‖ * (Λ * (‖I‖ * Z)) := by gcongr; exact (I.le_opNorm _).trans (by gcongr)
      _ = ‖R‖ * Λ * ‖I‖ * Z := by ring
      _ ≤ δ / 2 := hstart
  let S : Set A := Metric.closedBall 0 δ
  have hS : ∀ x : A, x ∈ S ↔ ‖x‖ ≤ δ := by intro x; simp [S, dist_eq_norm]
  have hmaps : MapsTo T S S := by
    intro x hx
    apply (hS _).2
    calc
      ‖T x‖ ≤ ‖T x - T 0‖ + ‖T 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (1 / 2 : ℝ) * ‖x - 0‖ + δ / 2 :=
        add_le_add (hTlip x 0 ((hS _).1 hx) (by simpa using hδ)) hTzero
      _ ≤ δ := by simpa only [sub_zero] using (by linarith [(hS _).1 hx] :
        (1 / 2 : ℝ) * ‖x‖ + δ / 2 ≤ δ)
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict T S S) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x.val) (T y.val) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist x.val y.val
    simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    exact hTlip x y ((hS _).1 x.property) ((hS _).1 y.property)
  have hcomplete : IsComplete S := Metric.isClosed_closedBall.isComplete
  obtain ⟨h, hh, hfixed, -, -⟩ := hcontract.exists_fixedPoint' hcomplete hmaps
    ((hS 0).2 (by simpa using hδ)) (edist_ne_top 0 (T 0))
  exact ⟨h, (hS _).1 hh, hfixed.symm⟩
end YauCounterexamples.BoundedAlgebra

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)
local instance realH_smulCommClass_fp (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance realH_isScalarTower_fp (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩

omit [T2Space M] in
lemma realValue_norm_bound (s : ℝ) (u : A.realH s) (x : M) :
    |A.realValue s u x| ≤ ‖A.representative s‖ * ‖u‖ :=
  (Complex.abs_re_le_norm _).trans (((A.representative s u).norm_coe_le_norm x).trans
    ((A.representative s).le_opNorm u))

omit [T2Space M] in
lemma realValue_power (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (e h : A.realH (2 * (l : ℝ))) (he : ∀ x, A.realValue (2 * (l : ℝ)) e x = 1)
    (n : ℕ) (x : M) :
    A.realValue (2 * (l : ℝ)) (BoundedAlgebra.power (A.realProduct l ht) e h n) x =
      A.realValue (2 * (l : ℝ)) h x ^ n := by
  induction n with
  | zero => exact (he x).trans (pow_zero _).symm
  | succ n ih =>
    change A.realValue _ (A.realProduct l ht h (BoundedAlgebra.power (A.realProduct l ht) e h n)) x = _
    rw [A.realValue_product, ih, pow_succ]
    exact mul_comm _ _

omit [T2Space M] in
lemma realValue_polynomial (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (e c s h : A.realH (2 * (l : ℝ))) (he : ∀ x, A.realValue (2 * (l : ℝ)) e x = 1)
    (x : M) :
    A.realValue (2 * (l : ℝ)) (BoundedAlgebra.polynomial (A.realProduct l ht) e c s h) x =
      A.realValue (2 * (l : ℝ)) c x * (1 + A.realValue (2 * (l : ℝ)) h x) ^ 5 -
        A.realValue (2 * (l : ℝ)) s x * (1 + A.realValue (2 * (l : ℝ)) h x) -
          4 * A.realValue (2 * (l : ℝ)) h x := by
  simp only [BoundedAlgebra.polynomial, BoundedAlgebra.remainder, A.realValue_sub,
    A.realValue_add, A.realValue_smul, A.realValue_product, A.realValue_power l ht e h he, he]
  ring

end CompactMetricAtlas
end YauCounterexamples

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)
local instance realH_smulCommClass_pf (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance realH_isScalarTower_pf (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩

theorem exists_positive_factor_of_bounds
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b s : M → ℝ) (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ s) (hbpos : ∀ x, 0 < b x)
    (e c σ β : A.realH (2 * ((k + 1 : ℕ) : ℝ)))
    (he : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) e x = 1)
    (hc : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) c x = b x ^ 3)
    (hσ : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) σ x = s x)
    (hβ : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) β x = b x - 1)
    (Λ δ K U ε C V : ℝ) (hΛ : 0 < Λ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hK : ‖A.realProduct (k + 1) ht‖ ≤ K) (hU : ‖e‖ ≤ U)
    (hcsmall : ‖c - e‖ ≤ C * ε) (hσsmall : ‖σ - e‖ ≤ ε) (hcsize : ‖c‖ ≤ V)
    (hα : ∀ i, 1 ≤ 4 * Λ * (A.localInverse i).radius ^ 2)
    (herr : A.errorBound B (4 * Λ) ≤ 1 / 2)
    (hsmall : ‖A.realResolvent B (4 * Λ) (by positivity) hα herr‖ *
      (‖A.realDivergence B β‖ + Λ * ‖A.realInclusion‖ *
        (K * (5 * C + 1) * ε + K * V * BoundedAlgebra.remainderConstant K U * δ)) ≤ 1 / 2)
    (hstart : ‖A.realResolvent B (4 * Λ) (by positivity) hα herr‖ * Λ *
      ‖A.realInclusion‖ * ((C + 1) * ε) ≤ δ / 2)
    (hpositive : ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ * δ < 1) :
    ∃ u : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g b u x = Λ * b x ^ 3 * u x ^ 5 - Λ * s x * u x) ∧
      (∀ x, |u x - 1| ≤ ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ * δ) ∧
      ∃ h : A.realH (2 * ((k + 1 : ℕ) : ℝ)), ‖h‖ ≤ δ ∧
        ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x = u x - 1 := by
  let p := A.realProduct (k + 1) ht
  let P := BoundedAlgebra.polynomial p e c σ
  let R := A.realResolvent B (4 * Λ) (by positivity) hα herr
  have hp (x y : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
      ‖P x - P y‖ ≤ (K * (5 * C + 1) * ε + K * V * BoundedAlgebra.remainderConstant K U * δ) * ‖x - y‖ :=
    BoundedAlgebra.polynomial_lipschitz p e hK hU hcsmall hσsmall hcsize hδ hδ1 hx hy
  have hp0 : ‖P 0‖ ≤ (C + 1) * ε := BoundedAlgebra.polynomial_zero_bound p e hcsmall hσsmall
  obtain ⟨h, hh, hfixed⟩ := BoundedAlgebra.solve R A.realInclusion (A.realDivergence B β) P
    Λ δ _ _ hΛ.le hδ hp hp0 hsmall hstart
  let u : M → ℝ := fun x => 1 + A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x
  have hu2 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u := contMDiff_const.add (A.realValue_C2 h)
  have hub (x : M) : |u x - 1| ≤ ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ * δ := by
    dsimp only [u]
    rw [add_sub_cancel_left]
    have hn : 0 ≤ ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ := (A.representative (2 * ((k + 1 : ℕ) : ℝ))).opNorm_nonneg
    exact (A.realValue_norm_bound _ h x).trans (mul_le_mul_of_nonneg_left hh hn)
  have hup (x : M) : 0 < u x := by
    have h := (abs_le.mp (hub x)).1
    linarith
  have heq (x : M) : weightedLaplacian g b u x = Λ * b x ^ 3 * u x ^ 5 - Λ * s x * u x := by
    have hres := A.realResolvent_value B (4 * Λ) (by positivity) hα herr
      (A.realDivergence B β h - Λ • A.realInclusion (P h)) x
    change (4 * Λ) * A.realValue _ (R _) x - laplaceBeltrami g (A.realValue _ (R _)) x = _ at hres
    rw [← hfixed] at hres
    simp only [A.realValue_sub, A.realValue_smul, A.realValue_inclusion,
      A.realDivergence_value] at hres
    have hpv := A.realValue_polynomial (k + 1) ht e c σ h he x
    change A.realValue _ (P h) x = _ at hpv
    rw [hpv, hc, hσ] at hres
    have hβfun : A.realValue (2 * ((k + 1 : ℕ) : ℝ)) β = fun y => b y - 1 := funext hβ
    rw [hβfun] at hres
    dsimp only [u]
    rw [weightedLaplacian_shift (hb.of_le (by decide)) (A.realValue_C2 h)]
    linear_combination -hres
  have hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) ((e + h : A.realH _).val) : M → ℂ) =
      fun x => (u x : ℂ) := by
    funext x
    rw [← A.ofReal_realValue, A.realValue_add, he]
  have husmooth := A.represented_weighted_quintic_smooth hd hb hsmooth hbpos hu2 Λ heq
    ((e + h : A.realH _).val) hv
  exact ⟨u, husmooth, hup, heq, hub, h, hh, fun x => by dsimp [u]; ring⟩

end CompactMetricAtlas
end YauCounterexamples

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples.BoundedAlgebra
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cubicPerturbation (p : X →L[ℝ] X →L[ℝ] X) (e x : X) : X :=
  e + (3 : ℝ) • x + (3 : ℝ) • power p e x 2 + power p e x 3

lemma cubicPerturbation_bound (p : X →L[ℝ] X →L[ℝ] X) (e : X) {K U ε : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x : X} (hx : ‖x‖ ≤ ε) :
    ‖cubicPerturbation p e x - e‖ ≤ (3 + 3 * K ^ 2 * U + K ^ 3 * U) * ε := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  have hpow (n : ℕ) : ε ^ (n + 1) ≤ ε := by
    calc ε ^ (n + 1) = ε * ε ^ n := by ring
         _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hε hε1) hε
         _ = ε := mul_one _
  have h2 := norm_power p e hK hU hε hx 2
  have h3 := norm_power p e hK hU hε hx 3
  have h2' : ‖power p e x 2‖ ≤ K ^ 2 * U * ε :=
    h2.trans (mul_le_mul_of_nonneg_left (hpow 1) (by positivity))
  have h3' : ‖power p e x 3‖ ≤ K ^ 3 * U * ε :=
    h3.trans (mul_le_mul_of_nonneg_left (hpow 2) (by positivity))
  have heq : cubicPerturbation p e x - e =
      (3 : ℝ) • x + (3 : ℝ) • power p e x 2 + power p e x 3 := by
    unfold cubicPerturbation
    abel
  rw [heq]
  calc
    _ ≤ (‖(3 : ℝ) • x‖ + ‖(3 : ℝ) • power p e x 2‖) + ‖power p e x 3‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = 3 * ‖x‖ + 3 * ‖power p e x 2‖ + ‖power p e x 3‖ := by
      rw [norm_smul, norm_smul]; norm_num
    _ ≤ 3 * ε + 3 * (K ^ 2 * U * ε) + K ^ 3 * U * ε := by gcongr
    _ = _ := by ring
end YauCounterexamples.BoundedAlgebra

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma realValue_cubic (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (e h : A.realH (2 * (l : ℝ))) (he : ∀ x, A.realValue (2 * (l : ℝ)) e x = 1)
    (x : M) :
    A.realValue (2 * (l : ℝ)) (BoundedAlgebra.cubicPerturbation (A.realProduct l ht) e h) x =
      (1 + A.realValue (2 * (l : ℝ)) h x) ^ 3 := by
  simp only [BoundedAlgebra.cubicPerturbation, A.realValue_add, A.realValue_smul,
    A.realValue_power l ht e h he, he]
  ring

lemma realDivergence_norm_bound (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    ‖A.realDivergence B b‖ ≤
      (‖A.realLaplacian B‖ * ‖A.realProduct (k + 1) ht‖ +
        2 * ‖A.realProduct k hs‖ * ‖A.realInclusion‖ * ‖A.realLaplacian B‖) / 2 * ‖b‖ :=
  boundedDivergence_norm _ _ _ _ _
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
