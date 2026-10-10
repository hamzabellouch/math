import OAI.Analysis.KadisonKastler.HaarPolynomial
import OAI.Analysis.KadisonKastler.FreeProjectionMoments
import OAI.Analysis.KadisonKastler.TracialProducts
import Mathlib.LinearAlgebra.Span.Basic

namespace OAI

/-! # The two free-projection moments under tracial approximation

Finite Laurent-polynomial moments follow from the alternating Haar
moments. Cauchy--Schwarz then extends the required degree-two and
degree-four identities under trace-two-norm approximation. In these
degrees no uniform operator bound on the approximants is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Finite Laurent polynomials in a unitary. -/
def haarLaurentSpan (v : unitary B) : Submodule ℂ B :=
  Submodule.span ℂ (Set.range (haarPower v))

/-- Laurent polynomials with no constant Fourier term. -/
def centeredHaarLaurentSpan (v : unitary B) : Submodule ℂ B :=
  Submodule.span ℂ (Set.range (fun k : {k : ℤ // k ≠ 0} => haarPower v k.val))

theorem haarPower_mem_haarLaurentSpan (v : unitary B) (k : ℤ) :
    haarPower v k ∈ haarLaurentSpan v := Submodule.subset_span ⟨k, rfl⟩

theorem haarPower_mem_centeredHaarLaurentSpan (v : unitary B) {k : ℤ} (hk : k ≠ 0) :
    haarPower v k ∈ centeredHaarLaurentSpan v := Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

/-- The recovery polynomial stays in every star subalgebra containing its unitary. -/
theorem unitaryHaarPolynomial_mem {S : StarSubalgebra ℂ B} {v : unitary B}
    (hv : (v : B) ∈ S) (N : ℕ) : unitaryHaarPolynomial N v ∈ S := by
  apply S.smul_mem ?_ _
  apply S.sum_mem
  intro r hr
  exact S.pow_mem hv _

/-- A Laurent polynomial in a unitary is normal; here only positive powers occur. -/
theorem isStarNormal_unitaryHaarPolynomial (N : ℕ) (v : unitary B) :
    IsStarNormal (unitaryHaarPolynomial N v) := by
  have hs : Commute (star (unitaryHaarSum N v)) (unitaryHaarSum N v) := by
    simp only [unitaryHaarSum, star_sum, star_pow]
    apply Commute.sum_left
    intro r hr
    apply Commute.sum_right
    intro s hs
    exact (star_comm_self (x := (v : B))).pow_pow _ _
  constructor
  simp only [unitaryHaarPolynomial, star_smul]
  exact (hs.smul_left _).smul_right _

/-- Subtraction of the scalar trace is a complex-linear operation. -/
def traceCenter (τ : FaithfulTracialState B) : B →ₗ[ℂ] B :=
  LinearMap.id - τ.toLinearMap.smulRight (1 : B)

@[simp]
theorem traceCenter_apply (τ : FaithfulTracialState B) (x : B) :
    traceCenter τ x = x - τ.toLinearMap x • (1 : B) := rfl

@[simp]
theorem trace_traceCenter (τ : FaithfulTracialState B) (x : B) :
    τ.toLinearMap (traceCenter τ x) = 0 := by
  simp [traceCenter_apply, τ.map_one]

theorem centeredHaarLaurentSpan_le (v : unitary B) :
    centeredHaarLaurentSpan v ≤ haarLaurentSpan v := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨k.val, rfl⟩

theorem traceCenter_mem_centeredHaarLaurentSpan (τ : FaithfulTracialState B)
    (v : unitary B) (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    {x : B} (hx : x ∈ haarLaurentSpan v) :
    traceCenter τ x ∈ centeredHaarLaurentSpan v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    by_cases hk : k = 0
    · simp [hk, traceCenter_apply, τ.map_one]
    · simpa [traceCenter_apply, hhaar k hk] using
        haarPower_mem_centeredHaarLaurentSpan v hk
  | zero => simpa only [map_zero] using (centeredHaarLaurentSpan v).zero_mem
  | add x y hx hy hxc hyc =>
    simpa only [map_add] using (centeredHaarLaurentSpan v).add_mem hxc hyc
  | smul c x hx hxc =>
    simpa only [map_smul] using (centeredHaarLaurentSpan v).smul_mem c hxc

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}

private theorem trace_mul_haarPower (h : FreeHaarMoments τ A v) {a : B}
    (ha : a ∈ A) (haτ : τ.toLinearMap a = 0) (k : ℤ) :
    τ.toLinearMap (a * haarPower v k) = 0 := by
  have hm := h.alternating_moment 1 (by omega) (fun _ => a) (fun _ => k)
    (fun _ => ha) (fun _ => haτ) (by intro i hi; omega)
  simpa [List.ofFn_succ] using hm

private theorem trace_four_haarPowers (h : FreeHaarMoments τ A v) {a b : B}
    (ha : a ∈ A) (hb : b ∈ A) (haτ : τ.toLinearMap a = 0)
    (hbτ : τ.toLinearMap b = 0) (k l : ℤ) (hk : k ≠ 0) :
    τ.toLinearMap (a * haarPower v k * b * haarPower v l) = 0 := by
  have hm := h.alternating_moment 2 (by omega) ![a, b] ![k, l]
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
    (by
      intro i hi
      fin_cases i
      · simpa using hk
      · norm_num at hi)
  simpa [List.ofFn_succ, mul_assoc] using hm

/-- A centered base-algebra element is orthogonal to every Laurent polynomial. -/
theorem trace_mul_laurent (h : FreeHaarMoments τ A v) {a x : B}
    (ha : a ∈ A) (haτ : τ.toLinearMap a = 0) (hx : x ∈ haarLaurentSpan v) :
    τ.toLinearMap (a * x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact h.trace_mul_haarPower ha haτ k
  | zero => simp
  | add x y hx hy hxt hyt => simp [mul_add, hxt, hyt]
  | smul c x hx hxt => simp [hxt]

/-- Alternating degree four, first Haar letter centered. -/
theorem trace_four_laurent (h : FreeHaarMoments τ A v) {a b x y : B}
    (ha : a ∈ A) (hb : b ∈ A) (haτ : τ.toLinearMap a = 0)
    (hbτ : τ.toLinearMap b = 0) (hx : x ∈ centeredHaarLaurentSpan v)
    (hy : y ∈ haarLaurentSpan v) :
    τ.toLinearMap (a * x * b * y) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact h.trace_four_haarPowers ha hb haτ hbτ k l hk
    | zero => simp
    | add y z hy hz hyt hzt => simp [mul_add, hyt, hzt]
    | smul c y hy hyt => simp [hyt]
  | zero => simp
  | add x z hx hz hxt hzt => simp [mul_add, add_mul, hxt, hzt]
  | smul c x hx hxt => simp [hxt]

end FreeHaarMoments

@[simp]
theorem traceTwoNorm_neg (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ (-x) = traceTwoNorm τ x := by
  simp [traceTwoNorm]

theorem traceTwoNorm_sub_comm (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x - y) = traceTwoNorm τ (y - x) := by
  rw [← traceTwoNorm_neg τ (x - y), neg_sub]

/-- Cauchy--Schwarz in its product form. -/
theorem norm_trace_mul_le (τ : FaithfulTracialState B) (x y : B) :
    ‖τ.toLinearMap (x * y)‖ ≤ traceTwoNorm τ x * traceTwoNorm τ y := by
  simpa only [star_star, traceTwoNorm_star] using τ.cauchySchwarz (star x) y

theorem norm_trace_four_le (τ : FaithfulTracialState B) (a b x y : B) :
    ‖τ.toLinearMap (a * x * b * y)‖ ≤
      (‖a‖ * ‖b‖) * traceTwoNorm τ x * traceTwoNorm τ y := by
  calc
    _ ≤ traceTwoNorm τ (a * x * b) * traceTwoNorm τ y := norm_trace_mul_le τ _ _
    _ ≤ (traceTwoNorm τ (a * x) * ‖b‖) * traceTwoNorm τ y :=
      mul_le_mul_of_nonneg_right (traceTwoNorm_mul_le_right τ _ _) (traceTwoNorm_nonneg τ y)
    _ ≤ ((‖a‖ * traceTwoNorm τ x) * ‖b‖) * traceTwoNorm τ y :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (traceTwoNorm_mul_le_left τ _ _) (norm_nonneg b))
        (traceTwoNorm_nonneg τ y)
    _ = _ := by ring

/-- Centering preserves convergence in the tracial two-norm. -/
theorem traceTwoNorm_traceCenter_le (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ (traceCenter τ x) ≤ (1 + ‖(1 : B)‖) * traceTwoNorm τ x := by
  calc
    _ ≤ traceTwoNorm τ x + traceTwoNorm τ (-(τ.toLinearMap x • (1 : B))) := by
      simpa only [traceCenter_apply, sub_eq_add_neg] using
        traceTwoNorm_add_le τ x (-(τ.toLinearMap x • (1 : B)))
    _ ≤ traceTwoNorm τ x + ‖-(τ.toLinearMap x • (1 : B))‖ :=
      add_le_add (le_refl _) (traceTwoNorm_le_norm τ _)
    _ = traceTwoNorm τ x + ‖τ.toLinearMap x‖ * ‖(1 : B)‖ := by rw [norm_neg, norm_smul]
    _ ≤ traceTwoNorm τ x + traceTwoNorm τ x * ‖(1 : B)‖ :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right (τ.norm_apply_le_traceTwoNorm x) (norm_nonneg (1 : B)))
    _ = _ := by ring

theorem tendsto_traceCenter_in_traceTwoNorm (τ : FaithfulTracialState B)
    (c : ℕ → B) (x : B)
    (hc : Tendsto (fun n => traceTwoNorm τ (c n - x)) atTop (𝓝 0)) :
    Tendsto (fun n => traceTwoNorm τ (traceCenter τ (c n) - traceCenter τ x))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => traceTwoNorm_nonneg τ _)
    (fun n => ?_) (show Tendsto
      (fun n => (1 + ‖(1 : B)‖) * traceTwoNorm τ (c n - x)) atTop (𝓝 0) by
        simpa using tendsto_const_nhds.mul hc)
  rw [← map_sub]
  exact traceTwoNorm_traceCenter_le τ _

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}

/-- Degree-two moments pass to tracial two-norm limits of Laurent polynomials. -/
theorem trace_mul_of_laurent_approx (h : FreeHaarMoments τ A v) {a x : B}
    (ha : a ∈ A) (haτ : τ.toLinearMap a = 0) (c : ℕ → B)
    (hc : ∀ n, c n ∈ haarLaurentSpan v)
    (hlim : Tendsto (fun n => traceTwoNorm τ (c n - x)) atTop (𝓝 0)) :
    τ.toLinearMap (a * x) = 0 := by
  have hb (n : ℕ) : ‖τ.toLinearMap (a * x)‖ ≤ ‖a‖ * traceTwoNorm τ (c n - x) := by
    have hz := h.trace_mul_laurent ha haτ (hc n)
    have he : τ.toLinearMap (a * x) = τ.toLinearMap (a * (x - c n)) := by
      simp [mul_sub, hz]
    rw [he]
    exact (τ.norm_apply_le_traceTwoNorm _).trans
      ((traceTwoNorm_mul_le_left τ _ _).trans_eq (by rw [traceTwoNorm_sub_comm]))
  have hl : Tendsto (fun n => ‖a‖ * traceTwoNorm τ (c n - x)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim
  have hn : ‖τ.toLinearMap (a * x)‖ ≤ 0 := ge_of_tendsto hl (Eventually.of_forall hb)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- The ordinary degree-two trace factorization for a Haar-algebra limit. -/
theorem trace_mul_eq_mul_trace_of_laurent_approx (h : FreeHaarMoments τ A v)
    {p x : B} (hp : p ∈ A) (c : ℕ → B) (hc : ∀ n, c n ∈ haarLaurentSpan v)
    (hlim : Tendsto (fun n => traceTwoNorm τ (c n - x)) atTop (𝓝 0)) :
    τ.toLinearMap (p * x) = τ.toLinearMap p * τ.toLinearMap x := by
  have ha : traceCenter τ p ∈ A := A.sub_mem hp (A.smul_mem A.one_mem _)
  have hz := h.trace_mul_of_laurent_approx ha (trace_traceCenter τ p) c hc hlim
  apply sub_eq_zero.mp
  simpa only [traceCenter_apply, sub_mul, smul_mul_assoc, one_mul,
    map_sub, map_smul, smul_eq_mul] using hz

/-- Degree-four moments pass to tracial two-norm limits. -/
theorem trace_four_of_centered_laurent_approx (h : FreeHaarMoments τ A v)
    {a b x : B} (ha : a ∈ A) (hb : b ∈ A) (haτ : τ.toLinearMap a = 0)
    (hbτ : τ.toLinearMap b = 0) (c : ℕ → B)
    (hc : ∀ n, c n ∈ centeredHaarLaurentSpan v)
    (hlim : Tendsto (fun n => traceTwoNorm τ (c n - x)) atTop (𝓝 0)) :
    τ.toLinearMap (a * x * b * x) = 0 := by
  let d (n : ℕ) := traceTwoNorm τ (c n - x)
  have hdn (n : ℕ) : 0 ≤ d n := traceTwoNorm_nonneg τ _
  have hbnd (n : ℕ) : ‖τ.toLinearMap (a * x * b * x)‖ ≤
      (‖a‖ * ‖b‖) * d n * (2 * traceTwoNorm τ x + d n) := by
    have hz := h.trace_four_laurent ha hb haτ hbτ (hc n)
      (centeredHaarLaurentSpan_le v (hc n))
    have he : τ.toLinearMap (a * x * b * x) =
        τ.toLinearMap (a * (x - c n) * b * x) +
          τ.toLinearMap (a * c n * b * (x - c n)) := by
      have halg : a * x * b * x = a * (x - c n) * b * x +
          a * c n * b * (x - c n) + a * c n * b * c n := by noncomm_ring
      rw [halg, map_add, map_add, hz, add_zero]
    have hc_bound : traceTwoNorm τ (c n) ≤ traceTwoNorm τ x + d n := by
      calc
        _ = traceTwoNorm τ (x + (c n - x)) := by congr 1; abel
        _ ≤ _ := traceTwoNorm_add_le τ _ _
    rw [he]
    calc
      _ ≤ ‖τ.toLinearMap (a * (x - c n) * b * x)‖ +
          ‖τ.toLinearMap (a * c n * b * (x - c n))‖ := norm_add_le _ _
      _ ≤ (‖a‖ * ‖b‖) * d n * traceTwoNorm τ x +
          (‖a‖ * ‖b‖) * traceTwoNorm τ (c n) * d n := by
        simpa only [traceTwoNorm_sub_comm τ x (c n)] using
          add_le_add (norm_trace_four_le τ a b (x - c n) x)
            (norm_trace_four_le τ a b (c n) (x - c n))
      _ ≤ (‖a‖ * ‖b‖) * d n * traceTwoNorm τ x +
          (‖a‖ * ‖b‖) * (traceTwoNorm τ x + d n) * d n := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hc_bound (mul_nonneg (norm_nonneg a) (norm_nonneg b)))
            (hdn n))
      _ = _ := by ring
  have hl : Tendsto (fun n => (‖a‖ * ‖b‖) * d n * (2 * traceTwoNorm τ x + d n))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hlim).mul (tendsto_const_nhds.add hlim)
  have hn : ‖τ.toLinearMap (a * x * b * x)‖ ≤ 0 :=
    ge_of_tendsto hl (Eventually.of_forall hbnd)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- The precise two centered projection moments, obtained from Laurent
approximation to the spectral projection. No freeness conclusion is an
assumption of this theorem. -/
theorem centeredProjectionMoments_of_laurent_approx (h : FreeHaarMoments τ A v)
    {p e : B} {t η : ℝ} (hp : p ∈ A) (hpτ : τ.toLinearMap p = (t : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ)) (c : ℕ → B)
    (hc : ∀ n, c n ∈ haarLaurentSpan v)
    (hlim : Tendsto (fun n => traceTwoNorm τ (c n - e)) atTop (𝓝 0)) :
    CenteredProjectionMoments τ p e t η := by
  let a := p - (t : ℂ) • (1 : B)
  have ha : a ∈ A := A.sub_mem hp (A.smul_mem A.one_mem t)
  have haτ : τ.toLinearMap a = 0 := by simp [a, hpτ, τ.map_one]
  let c' (n : ℕ) := traceCenter τ (c n)
  have hc' (n : ℕ) : c' n ∈ centeredHaarLaurentSpan v :=
    traceCenter_mem_centeredHaarLaurentSpan τ v h.haar_moment (hc n)
  have hlim' : Tendsto (fun n => traceTwoNorm τ (c' n - traceCenter τ e))
      atTop (𝓝 0) := tendsto_traceCenter_in_traceTwoNorm τ c e hlim
  constructor
  · simpa only [traceCenter_apply, heτ] using
      h.trace_mul_of_laurent_approx ha haτ c'
        (fun n => centeredHaarLaurentSpan_le v (hc' n)) hlim'
  · simpa only [traceCenter_apply, heτ] using
      h.trace_four_of_centered_laurent_approx ha ha haτ haτ c' hc' hlim'

end FreeHaarMoments

end

end KadisonKastler

end OAI
