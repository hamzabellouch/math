import OAI.Dynamics.SmoothObstruction.Charts

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.RelativeProduct

variable {R : Type*}

/-- Later times multiply on the left, as in the manuscript. -/
def segment [Monoid R] (A : ℕ → R) (s : ℕ) : ℕ → R
  | 0 => 1
  | n + 1 => A (s + n) * segment A s n

@[simp] theorem segment_zero [Monoid R] (A : ℕ → R) (s : ℕ) :
    segment A s 0 = 1 := rfl

@[simp] theorem segment_succ [Monoid R] (A : ℕ → R) (s n : ℕ) :
    segment A s (n + 1) = A (s + n) * segment A s n := rfl

/-- Exact variation-of-constants expansion; no commutativity is used. -/
theorem difference [Ring R] (A B : ℕ → R) (s n : ℕ) :
    segment B s n - segment A s n =
      ∑ j ∈ Finset.range n,
        segment A (s + j + 1) (n - (j + 1)) *
          (B (s + j) - A (s + j)) * segment B s j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, segment_zero, one_mul]
    have hsum :
        (∑ j ∈ Finset.range n,
          segment A (s + j + 1) (n + 1 - (j + 1)) *
            (B (s + j) - A (s + j)) * segment B s j) =
          A (s + n) * (segment B s n - segment A s n) := by
      rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j < n := Finset.mem_range.mp hj
      have hlen : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
      have hidx : s + j + 1 + (n - (j + 1)) = s + n := by omega
      rw [hlen, segment_succ, hidx]
      simp only [mul_assoc]
    rw [hsum, segment_succ, segment_succ]
    noncomm_ring

/-- Uniform subinterval bounds yield a relative error, rather than a
bound obtained by multiplying one-step bounds. -/
theorem norm_difference_le [NormedRing R] (A B : ℕ → R)
    (s m : ℕ) (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hA : ∀ t k : ℕ, s ≤ t → t + k ≤ s + m → ‖segment A t k‖ ≤ L)
    (hBA : ∀ t : ℕ, s ≤ t → t < s + m → ‖B t - A t‖ ≤ δ) :
    ‖segment B s m - segment A s m‖ ≤ L * ((1 + L * δ) ^ m - 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hB (j : ℕ) (hj : j < m) :
        ‖segment B s j‖ ≤ L * (1 + L * δ) ^ j := by
      have herr := ih j hj (fun t k ht hk => hA t k ht (by omega))
        (fun t ht htm => hBA t ht (by omega))
      calc
        ‖segment B s j‖ = ‖(segment B s j - segment A s j) + segment A s j‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖segment B s j - segment A s j‖ + ‖segment A s j‖ := norm_add_le _ _
        _ ≤ L * ((1 + L * δ) ^ j - 1) + L :=
          add_le_add herr (hA s j le_rfl (by omega))
        _ = L * (1 + L * δ) ^ j := by ring
    rw [difference]
    calc
      ‖∑ j ∈ Finset.range m,
          segment A (s + j + 1) (m - (j + 1)) *
            (B (s + j) - A (s + j)) * segment B s j‖
          ≤ ∑ j ∈ Finset.range m,
            ‖segment A (s + j + 1) (m - (j + 1)) *
              (B (s + j) - A (s + j)) * segment B s j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range m, L * δ * (L * (1 + L * δ) ^ j) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j < m := Finset.mem_range.mp hj
        calc
          _ ≤ ‖segment A (s + j + 1) (m - (j + 1))‖ *
              ‖B (s + j) - A (s + j)‖ * ‖segment B s j‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ L * δ * (L * (1 + L * δ) ^ j) := by
            gcongr
            · exact hA (s + j + 1) (m - (j + 1)) (by omega) (by omega)
            · exact hBA (s + j) (by omega) (by omega)
            · exact hB j hjm
      _ = L * ((1 + L * δ) ^ m - 1) := by
        have hgeom := geom_sum_mul (1 + L * δ) m
        simp only [add_sub_cancel_left] at hgeom
        rw [← hgeom, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Scalar normalization of a whole interval. -/
theorem segment_smul [NormedRing R] [NormedAlgebra ℝ R]
    (A : ℕ → R) (c : ℝ) (s n : ℕ) :
    segment (fun t => c • A t) s n = c ^ n • segment A s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [segment_succ, ih, smul_mul_smul_comm, pow_succ']

private theorem exp_cancel (σ a : ℝ) (n : ℕ) :
    Real.exp (-σ) ^ n * Real.exp (σ * n + a) = Real.exp a := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- The relative perturbation bound with its exact exponential weight. -/
theorem norm_difference_le_exp_exact [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℕ → R) (s m : ℕ) (σ a δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ t k : ℕ, s ≤ t → t + k ≤ s + m →
      ‖segment A t k‖ ≤ Real.exp (σ * k + a))
    (hBA : ∀ t : ℕ, s ≤ t → t < s + m → ‖B t - A t‖ ≤ δ) :
    ‖segment B s m - segment A s m‖ ≤
      Real.exp (σ * m + a) * ((1 + δ * Real.exp (a - σ)) ^ m - 1) := by
  let c := Real.exp (-σ)
  have hc : 0 < c := Real.exp_pos _
  have hnorm (D : ℕ → R) (t k : ℕ) :
      ‖segment (fun i => c • D i) t k‖ = c ^ k * ‖segment D t k‖ := by
    rw [segment_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc.le k)]
  have hnormsub (t k : ℕ) :
      ‖segment (fun i => c • B i) t k - segment (fun i => c • A i) t k‖ =
        c ^ k * ‖segment B t k - segment A t k‖ := by
    rw [segment_smul, segment_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hc.le k)]
  have hAnorm (t k : ℕ) (ht : s ≤ t) (hk : t + k ≤ s + m) :
      ‖segment (fun i => c • A i) t k‖ ≤ Real.exp a := by
    rw [hnorm]
    calc
      _ ≤ c ^ k * Real.exp (σ * k + a) :=
        mul_le_mul_of_nonneg_left (hA t k ht hk) (pow_nonneg hc.le k)
      _ = Real.exp a := exp_cancel σ a k
  have hBAnorm (t : ℕ) (ht : s ≤ t) (htm : t < s + m) :
      ‖c • B t - c • A t‖ ≤ c * δ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hBA t ht htm) hc.le
  have herr := norm_difference_le (fun t => c • A t) (fun t => c • B t)
    s m (Real.exp a) (c * δ) (Real.exp_pos a).le (mul_nonneg hc.le hδ)
    hAnorm hBAnorm
  rw [hnormsub] at herr
  have hcoef : Real.exp a * (c * δ) = δ * Real.exp (a - σ) := by
    dsimp [c]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hcoef] at herr
  apply (mul_le_mul_iff_right₀ (pow_pos hc m)).mp
  simpa only [← mul_assoc, c, exp_cancel] using herr

/-- Quantitative core of the source exterior-product perturbation lemma.
Applying this to exterior powers with one-step error `δ = C * ε` gives
exactly its stated finite-product bound. -/
theorem norm_difference_le_exp [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℕ → R) (s m : ℕ) (σ a δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ t k : ℕ, s ≤ t → t + k ≤ s + m →
      ‖segment A t k‖ ≤ Real.exp (σ * k + a))
    (hBA : ∀ t : ℕ, s ≤ t → t < s + m → ‖B t - A t‖ ≤ δ) :
    ‖segment B s m - segment A s m‖ ≤
      Real.exp (σ * m + a) * ((1 + δ * Real.exp (a + |σ|)) ^ m - 1) := by
  refine (norm_difference_le_exp_exact A B s m σ a δ hδ hA hBA).trans ?_
  gcongr
  linarith [neg_le_abs σ]

end SmoothObstruction.RelativeProduct

namespace SmoothObstruction.RelativeProduct
open Finset
variable {R : Type*} [NormedRing R]

lemma segment_norm_le (A : ℕ → R) (s n : ℕ) (hOne : ‖(1:R)‖≤1) {K : ℝ} (hK : 0≤K)
    (hA : ∀ t,s≤t → t<s+n → ‖A t‖≤K) : ‖segment A s n‖≤K^n := by
  induction n with
  | zero => simpa only [segment_zero,pow_zero] using hOne
  | succ n ih =>
    rw [segment_succ,pow_succ]
    exact (norm_mul_le _ _).trans (by
      simpa only [mul_comm] using mul_le_mul (hA _ (by omega) (by omega))
        (ih (fun t ht ht' => hA t ht (by omega))) (norm_nonneg _) hK)

/-- Ordinary C¹ telescoping on a short interval. Unlike the long-window
relative exterior estimate this bound pays the one-step bound, precisely
where the manuscript permits an exp(CL) loss. -/
lemma short_difference (A B : ℕ → R) (N : ℕ) (hOne : ‖(1:R)‖≤1) {K δ : ℝ}
    (hK : 1≤K) (hδ : 0≤δ)
    (hA : ∀ t<N,‖A t‖≤K) (hB : ∀ t<N,‖B t‖≤K)
    (hBA : ∀ t<N,‖B t-A t‖≤δ) :
    ‖segment B 0 N-segment A 0 N‖≤N*K^N*δ := by
  rw [difference]
  calc
    _≤∑ j∈range N,‖segment A (0+j+1) (N-(j+1))*(B (0+j)-A (0+j))*segment B 0 j‖ := norm_sum_le _ _
    _≤∑ j∈range N,K^N*δ := by
      apply sum_le_sum
      intro j hj
      have hjN := mem_range.mp hj
      have hAl := segment_norm_le A (j+1) (N-(j+1)) hOne (by linarith : 0≤K)
        (fun t _ ht => hA t (by omega))
      have hBj := segment_norm_le B 0 j hOne (by linarith : 0≤K)
        (fun t _ ht => hB t (by omega))
      calc
        _≤‖segment A (j+1) (N-(j+1))‖*‖B j-A j‖*‖segment B 0 j‖ := by
          simpa only [Nat.zero_add] using
            (norm_mul_le (segment A (j+1) (N-(j+1))*(B j-A j)) (segment B 0 j)).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _≤K^(N-(j+1))*δ*K^j := by
          apply mul_le_mul _ hBj (norm_nonneg _) (by positivity)
          exact mul_le_mul hAl (hBA j hjN) (norm_nonneg _) (by positivity)
        _=K^(N-(j+1)+j)*δ := by rw [pow_add]; ring
        _≤K^N*δ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by omega)) hδ
    _=N*K^N*δ := by simp only [sum_const,card_range,nsmul_eq_mul]; ring
end SmoothObstruction.RelativeProduct

namespace SmoothObstruction.ShortDerivative
open Set Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual nonautonomous coordinate composition. -/
def iterate (f : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | n+1 => f n ∘ iterate f n

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma orbit_eq_iterate (f : ℕ → E → E) (x : ℕ → E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1)) : ∀ t≤N,iterate f t (x 0)=x t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    change f t (iterate f t (x 0))=x (t+1)
    rw [ih (by omega),hx t (by omega)]

lemma derivative_iterate (f : ℕ → E → E) (x : ℕ → E)
    (A : ℕ → E →L[ℝ] E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hd : ∀ t<N,HasFDerivAt (f t) (A t) (x t)) :
    HasFDerivAt (iterate f N) (RelativeProduct.segment A 0 N) (x 0) := by
  induction N with
  | zero => exact hasFDerivAt_id _
  | succ N ih =>
    have hN := ih (fun t ht => hx t (by omega)) (fun t ht => hd t (by omega))
    have he := orbit_eq_iterate f x (N+1) hx N (by omega)
    have hdN := hd N (by omega)
    rw [←he] at hdN
    have h := hdN.comp (x 0) hN
    simpa only [iterate,RelativeProduct.segment_succ,Nat.zero_add,ContinuousLinearMap.mul_def] using h

/-- Nearby genuine coordinate orbits have exponentially close short
products, under uniform first and second derivative bounds on convex
patches. No derivative of the long iterate is bounded by fiat. -/
theorem short_c1_stability (f : ℕ → E → E) (x y : ℕ → E)
    (s : ℕ → Set E) (N : ℕ) {K D : ℝ} (hK : 1≤K) (hD : 0≤D)
    (hx : ∀ t<N,f t (x t)=x (t+1)) (hy : ∀ t<N,f t (y t)=y (t+1))
    (hxs : ∀ t<N,x t∈s t) (hys : ∀ t<N,y t∈s t)
    (hs : ∀ t<N,Convex ℝ (s t))
    (hf : ∀ t<N,∀ a∈s t,DifferentiableAt ℝ (f t) a)
    (hff : ∀ t<N,∀ a∈s t,DifferentiableAt ℝ (fderiv ℝ (f t)) a)
    (hfirst : ∀ t<N,∀ a∈s t,‖fderiv ℝ (f t) a‖≤K)
    (hsecond : ∀ t<N,∀ a∈s t,‖fderiv ℝ (fderiv ℝ (f t)) a‖≤D) :
    (∀ t≤N,‖y t-x t‖≤K^t*‖y 0-x 0‖) ∧
    ‖fderiv ℝ (iterate f N) (y 0)-fderiv ℝ (iterate f N) (x 0)‖≤
      N*D*K^(2*N)*‖y 0-x 0‖ := by
  have hdist : ∀ t≤N,‖y t-x t‖≤K^t*‖y 0-x 0‖ := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      rw [←hy t (by omega),←hx t (by omega)]
      have hh := (hs t (by omega)).norm_image_sub_le_of_norm_fderiv_le
        (hf t (by omega)) (hfirst t (by omega)) (hxs t (by omega)) (hys t (by omega))
      exact hh.trans (by
        calc
          _≤K*(K^t*‖y 0-x 0‖) := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
          _=K^(t+1)*‖y 0-x 0‖ := by rw [pow_succ]; ring)
  refine ⟨hdist,?_⟩
  let A := fun t => fderiv ℝ (f t) (x t)
  let B := fun t => fderiv ℝ (f t) (y t)
  have hAx := derivative_iterate f x A N hx (fun t ht => (hf t ht _ (hxs t ht)).hasFDerivAt)
  have hBy := derivative_iterate f y B N hy (fun t ht => (hf t ht _ (hys t ht)).hasFDerivAt)
  rw [hAx.fderiv,hBy.fderiv]
  have hdiff : ∀ t<N,‖B t-A t‖≤D*K^N*‖y 0-x 0‖ := by
    intro t ht
    have hh := (hs t ht).norm_image_sub_le_of_norm_fderiv_le (hff t ht) (hsecond t ht) (hxs t ht) (hys t ht)
    exact hh.trans (by
      calc
        D*‖y t-x t‖≤D*(K^t*‖y 0-x 0‖) := mul_le_mul_of_nonneg_left (hdist t ht.le) hD
        _≤D*(K^N*‖y 0-x 0‖) := by gcongr
        _=D*K^N*‖y 0-x 0‖ := by ring)
  have hb := RelativeProduct.short_difference A B N ContinuousLinearMap.norm_id_le hK
    (by positivity : 0≤D*K^N*‖y 0-x 0‖)
    (fun t ht => hfirst t ht _ (hxs t ht)) (fun t ht => hfirst t ht _ (hys t ht)) hdiff
  convert hb using 1
  rw [show 2*N=N+N by omega,pow_add]
  ring
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.ShortDerivative
open Set Metric
open scoped ContDiff
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Fintype ι]

/-- Bootstrap nearby genuine local-map orbits into the carried domains,
using only one-sided C2 bounds on a convex closed model (in particular a
half-space). No extension across the boundary is assumed.
The only smallness required is C^N times the initial displacement; no
long-iterate derivative estimate or continued domain membership is assumed. -/
theorem uniform_short_boundary (f : ι → E → E) (K U : ι → Set E)
    (H : Set E) (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hH : IsClosed H) (hconvH : Convex ℝ H) (hKU : ∀ i,K i⊆U i)
    (huniq : ∀ i,UniqueDiffOn ℝ (U i∩H))
    (hf : ∀ i,ContDiffOn ℝ ∞ (f i) (U i∩H)) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ (a : ℕ → ι) (x y : ℕ → E) (N : ℕ),
      (∀ t<N,x t∈K (a t)) →
      (∀ t<N,x t∈interior H ∧ y t∈interior H) →
      (∀ t<N,f (a t) (x t)=x (t+1)) →
      (∀ t<N,f (a t) (y t)=y (t+1)) →
      C^N*‖y 0-x 0‖ ≤ r →
      (∀ t≤N,‖y t-x t‖ ≤ C^t*‖y 0-x 0‖) ∧
      (∀ t<N,y t∈U (a t)) ∧
      ‖fderiv ℝ (iterate (fun t => f (a t)) N) (y 0)-
        fderiv ℝ (iterate (fun t => f (a t)) N) (x 0)‖ ≤
        N*C*C^(2*N)*‖y 0-x 0‖ := by
  obtain ⟨r,C,hr,hC,hbounds⟩ := CarriedCharts.uniform_c2_boundary f K U H hK hU hH hKU huniq hf
  refine ⟨r,C,hr,hC,fun a x y N hxs hint hx hy hsmall => ?_⟩
  have hdist : ∀ t≤N,‖y t-x t‖ ≤ C^t*‖y 0-x 0‖ := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have htp : t<N := by omega
      have hb := hbounds (a t) (x t) (hxs t htp)
      have hyb : y t∈closedBall (x t) r := by
        rw [mem_closedBall,dist_eq_norm]
        exact (ih (by omega)).trans ((mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hC (by omega : t≤N)) (norm_nonneg _)).trans hsmall)
      have hxb : x t∈closedBall (x t) r := mem_closedBall_self hr.le
      rw [←hx t htp,←hy t htp]
      have hstep := ((convex_closedBall (x t) r).inter hconvH.interior).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => (hb.2 z hz.1 hz.2).1.differentiableAt (by simp))
        (fun z hz => (hb.2 z hz.1 hz.2).2.1) ⟨hxb,(hint t htp).1⟩ ⟨hyb,(hint t htp).2⟩
      exact hstep.trans (by
        calc
          C*‖y t-x t‖ ≤ C*(C^t*‖y 0-x 0‖) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
          _=C^(t+1)*‖y 0-x 0‖ := by rw [pow_succ]; ring)
  have hyball (t : ℕ) (ht : t<N) : y t∈closedBall (x t) r := by
    rw [mem_closedBall,dist_eq_norm]
    exact (hdist t ht.le).trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC ht.le) (norm_nonneg _)).trans hsmall)
  refine ⟨hdist,fun t ht => (hbounds (a t) (x t) (hxs t ht)).1 (hyball t ht),?_⟩
  exact (short_c1_stability (fun t => f (a t)) x y
    (fun t => closedBall (x t) r∩interior H) N
    hC (by linarith : 0≤C) hx hy
    (fun t ht => ⟨mem_closedBall_self hr.le,(hint t ht).1⟩)
    (fun t ht => ⟨hyball t ht,(hint t ht).2⟩)
    (fun t _ => (convex_closedBall (x t) r).inter hconvH.interior)
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).1.differentiableAt (by simp))
    (fun t ht z hz => (((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).1.fderiv_right
      (m:=∞) (by simp)).differentiableAt (by simp))
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).2.1)
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).2.2)).2
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.ShortDerivative
open Set Metric
open scoped ContDiff
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Fintype ι]

/-- Bootstrap nearby genuine local-map orbits into the carried domains,
using only one-sided C2 bounds on a convex closed model (in particular a
half-space). No extension across the boundary is assumed.
The only smallness required is C^N times the initial displacement; no
long-iterate derivative estimate or continued domain membership is assumed. -/
theorem uniform_short_interior (f : ι → E → E) (K U : ι → Set E)
    (H : Set E) (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hH : IsClosed H) (hconvH : Convex ℝ H) (hKU : ∀ i,K i⊆U i)
    (huniq : ∀ i,UniqueDiffOn ℝ (U i∩H))
    (hf : ∀ i,ContDiffOn ℝ ∞ (f i) (U i∩H))
    (hmaps : ∀ i,MapsTo (f i) (U i∩interior H) (interior H)) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ (a : ℕ → ι) (x y : ℕ → E) (N : ℕ),
      (∀ t<N,x t∈K (a t)) →
      (∀ t<N,x t∈interior H) → y 0∈interior H →
      (∀ t<N,f (a t) (x t)=x (t+1)) →
      (∀ t<N,f (a t) (y t)=y (t+1)) →
      C^N*‖y 0-x 0‖ ≤ r →
      (∀ t≤N,‖y t-x t‖ ≤ C^t*‖y 0-x 0‖ ∧ y t∈interior H) ∧
      (∀ t<N,y t∈U (a t)) ∧
      ‖fderiv ℝ (iterate (fun t => f (a t)) N) (y 0)-
        fderiv ℝ (iterate (fun t => f (a t)) N) (x 0)‖ ≤
        N*C*C^(2*N)*‖y 0-x 0‖ := by
  obtain ⟨r,C,hr,hC,hbounds⟩ := CarriedCharts.uniform_c2_boundary f K U H hK hU hH hKU huniq hf
  refine ⟨r,C,hr,hC,fun a x y N hxs hxi hyi hx hy hsmall => ?_⟩
  have hcontrol : ∀ t≤N,‖y t-x t‖ ≤ C^t*‖y 0-x 0‖ ∧ y t∈interior H := by
    intro t ht
    induction t with
    | zero => exact ⟨by simp,hyi⟩
    | succ t ih =>
      have htp : t<N := by omega
      have hi := ih (by omega)
      have hb := hbounds (a t) (x t) (hxs t htp)
      have hyb : y t∈closedBall (x t) r := by
        rw [mem_closedBall,dist_eq_norm]
        exact hi.1.trans ((mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hC (by omega : t≤N)) (norm_nonneg _)).trans hsmall)
      have hxb : x t∈closedBall (x t) r := mem_closedBall_self hr.le
      constructor
      · rw [←hx t htp,←hy t htp]
        have hstep := ((convex_closedBall (x t) r).inter hconvH.interior).norm_image_sub_le_of_norm_fderiv_le
          (fun z hz => (hb.2 z hz.1 hz.2).1.differentiableAt (by simp))
          (fun z hz => (hb.2 z hz.1 hz.2).2.1) ⟨hxb,hxi t htp⟩ ⟨hyb,hi.2⟩
        exact hstep.trans (by
          calc
            C*‖y t-x t‖ ≤ C*(C^t*‖y 0-x 0‖) :=
              mul_le_mul_of_nonneg_left hi.1 (by linarith)
            _=C^(t+1)*‖y 0-x 0‖ := by rw [pow_succ]; ring)
      · rw [←hy t htp]
        exact hmaps (a t) ⟨hb.1 hyb,hi.2⟩
  have hdist := fun t ht => (hcontrol t ht).1
  have hint := fun t ht => And.intro (hxi t ht) (hcontrol t ht.le).2
  have hyball (t : ℕ) (ht : t<N) : y t∈closedBall (x t) r := by
    rw [mem_closedBall,dist_eq_norm]
    exact (hdist t ht.le).trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC ht.le) (norm_nonneg _)).trans hsmall)
  refine ⟨hcontrol,fun t ht => (hbounds (a t) (x t) (hxs t ht)).1 (hyball t ht),?_⟩
  exact (short_c1_stability (fun t => f (a t)) x y
    (fun t => closedBall (x t) r∩interior H) N
    hC (by linarith : 0≤C) hx hy
    (fun t ht => ⟨mem_closedBall_self hr.le,(hint t ht).1⟩)
    (fun t ht => ⟨hyball t ht,(hint t ht).2⟩)
    (fun t _ => (convex_closedBall (x t) r).inter hconvH.interior)
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).1.differentiableAt (by simp))
    (fun t ht z hz => (((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).1.fderiv_right
      (m:=∞) (by simp)).differentiableAt (by simp))
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).2.1)
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).2.2)).2
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The C1 comparison is for genuine manifold orbits in one fixed carried
chart sequence. Neither continued chart membership nor staying in the
interior is assumed for the perturbed orbit: both are proved. The constants
are uniform over every sequence of reference charts, orbit and length. -/
theorem actual_short_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ (c : ℕ → ι) (x y : M) (N : ℕ),
      (∀ t≤N,S^[t] x∈K (c t)) → I.IsInteriorPoint x → I.IsInteriorPoint y →
      y∈(chartAt H (a (c 0))).source →
      C ^ N*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ ≤ r →
      (∀ t≤N,S^[t] y∈(chartAt H (a (c t))).source ∧
        ‖(extChartAt I (a (c t))) (S^[t] y)-(extChartAt I (a (c t))) (S^[t] x)‖ ≤
          C ^ t*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖) ∧
      ‖fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) y)-
        fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) x)‖ ≤
          N*C*C ^ (2*N)*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ := by
  let L (ij : ι×ι) := (extChartAt I (a ij.1)) '' (K ij.1∩S ⁻¹' K ij.2)
  have hcomp (ij : ι×ι) : IsCompact (L ij) :=
    ((hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a ij.1)).mono (fun x hx => by
        simpa only [extChartAt_source] using hKU _ hx.1))
  have hsub (ij : ι×ι) : L ij⊆domainU I S (a ij.1) (a ij.2) := by
    rintro z ⟨x,hx,rfl⟩
    exact map_mem_domainU I S (a ij.1) (a ij.2) x ⟨hKU _ hx.1,hKU _ hx.2⟩
  obtain ⟨r,C,hr,hC,hh⟩ := ShortDerivative.uniform_short_interior
    (fun ij : ι×ι => localMap I S (a ij.1) (a ij.2)) L
    (fun ij => domainU I S (a ij.1) (a ij.2)) (range I) hcomp
    (fun ij => isOpen_domainU I S (a ij.1) (a ij.2)) hclosed I.convex_range hsub
    (fun ij => by simpa only [inter_comm] using
      I.uniqueDiffOn.inter (isOpen_domainU I S (a ij.1) (a ij.2)))
    (fun ij => contDiffOn_localMap I S (a ij.1) (a ij.2))
    (fun ij => localMap_maps_interior I S (a ij.1) (a ij.2))
  refine ⟨r,C,hr,hC,fun c x y N hxs hxi hyi hy0 hsmall => ?_⟩
  let f : ℕ → E (d:=d) → E (d:=d) := fun t => localMap I S (a (c t)) (a (c (t+1)))
  let X : ℕ → E (d:=d) := fun t => (extChartAt I (a (c t))) (S^[t] x)
  let Y : ℕ → E (d:=d) := fun t => ShortDerivative.iterate f t ((extChartAt I (a (c 0))) y)
  have hXi : ∀ t,I.IsInteriorPoint (S^[t] x) := by
    intro t
    induction t with
    | zero => exact hxi
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((S.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  have hXL : ∀ t<N,X t∈L (c t,c (t+1)) := by
    intro t ht
    have hnext : S (S^[t] x) ∈ K (c (t+1)) := by
      simpa only [Function.iterate_succ_apply'] using hxs (t+1) (by omega)
    exact ⟨S^[t] x,⟨hxs t ht.le,hnext⟩,rfl⟩
  have hXint : ∀ t<N,X t∈interior (range I) := fun t ht =>
    (interior_coord I _ _ (hKU _ (hxs t ht.le))).mpr (hXi t)
  have hY0 : Y 0∈interior (range I) := (interior_coord I _ y hy0).mpr hyi
  have hXrec : ∀ t<N,f t (X t)=X (t+1) := by
    intro t ht
    simpa only [f,X,Function.iterate_succ_apply'] using
      localMap_coordinates I S (a (c t)) (a (c (t+1))) (S^[t] x) (hKU _ (hxs t ht.le))
  have hYrec : ∀ t<N,f t (Y t)=Y (t+1) := fun _ _ => rfl
  have hsmall' : C ^ N*‖Y 0-X 0‖ ≤ r := hsmall
  obtain ⟨hb,hu,hd⟩ := hh (fun t => (c t,c (t+1))) X Y N hXL hXint hY0 hXrec hYrec hsmall'
  have hactual : ∀ t≤N,S^[t] y∈(chartAt H (a (c t))).source ∧
      Y t=(extChartAt I (a (c t))) (S^[t] y) := by
    intro t ht
    induction t with
    | zero => exact ⟨hy0,rfl⟩
    | succ t ih =>
      obtain ⟨hyt,heq⟩ := ih (by omega)
      have htN : t<N := by omega
      have hm := (hu t htN).2
      change S ((extChartAt I (a (c t))).symm (Y t))∈(chartAt H (a (c (t+1)))).source at hm
      rw [heq,(extChartAt I (a (c t))).left_inv
        (by simpa only [extChartAt_source] using hyt)] at hm
      constructor
      · simpa only [Function.iterate_succ_apply'] using hm
      · rw [←hYrec t htN,heq]
        change localMap I S (a (c t)) (a (c (t+1)))
          ((extChartAt I (a (c t))) (S^[t] y))=_
        rw [localMap_coordinates I S _ _ _ hyt,Function.iterate_succ_apply']
  refine ⟨fun t ht => ⟨(hactual t ht).1,?_⟩,hd⟩
  simpa only [(hactual t ht).2,X,Y,ShortDerivative.iterate,Function.iterate_zero_apply,id_eq]
    using (hb t ht).1
end SmoothObstruction.ManifoldCoordinates

end

end OAI
