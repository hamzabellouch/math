import OAI.Analysis.KadisonKastler.HaarFunctionalCalculus
import OAI.Analysis.KadisonKastler.SpectralRecovery

namespace OAI

/-! # Laurent approximation of tracial limits

A diagonal selection retains Laurent approximation after taking a
tracial two-norm limit. Applied to continuous circle cutoffs, this passes
the finite Laurent moment calculations to the resulting arc projection.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Choose one Laurent approximant at each stage of a convergent sequence,
with error less than `1 / (n + 1)`. -/
theorem exists_haarLaurent_approx_of_traceTwoNorm_limit
    (τ : FaithfulTracialState B) (v : unitary B) (x : ℕ → B) (e : B)
    (happrox : ∀ n, ∃ c : ℕ → B, (∀ k, c k ∈ haarLaurentSpan v) ∧
      Tendsto (fun k => traceTwoNorm τ (c k - x n)) atTop (𝓝 0))
    (hlim : Tendsto (fun n => traceTwoNorm τ (x n - e)) atTop (𝓝 0)) :
    ∃ c : ℕ → B, (∀ n, c n ∈ haarLaurentSpan v) ∧
      Tendsto (fun n => traceTwoNorm τ (c n - e)) atTop (𝓝 0) := by
  choose q hq hqLim using happrox
  have hchoose (n : ℕ) : ∃ k : ℕ,
      traceTwoNorm τ (q n k - x n) < 1 / ((n : ℝ) + 1) := by
    have hevent := (tendsto_order.1 (hqLim n)).2 (1 / ((n : ℝ) + 1)) (by positivity)
    exact hevent.exists
  choose k hk using hchoose
  refine ⟨fun n => q n (k n), fun n => hq n (k n), ?_⟩
  have hbound (n : ℕ) : traceTwoNorm τ (q n (k n) - e) ≤
      1 / ((n : ℝ) + 1) + traceTwoNorm τ (x n - e) := by
    calc
      _ = traceTwoNorm τ ((q n (k n) - x n) + (x n - e)) := by congr 1; abel
      _ ≤ traceTwoNorm τ (q n (k n) - x n) + traceTwoNorm τ (x n - e) :=
        traceTwoNorm_add_le τ _ _
      _ ≤ _ := add_le_add (hk n).le le_rfl
  have hzero : Tendsto
      (fun n : ℕ => 1 / ((n : ℝ) + 1) + traceTwoNorm τ (x n - e)) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.add hlim
  exact squeeze_zero (fun n => traceTwoNorm_nonneg τ _) hbound hzero

/-- Every tracial limit of continuous functions of the Haar unitary has
actual Laurent-polynomial approximants. -/
theorem exists_haarLaurent_approx_of_functional_limit
    (τ : FaithfulTracialState B) (v : unitary B)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n)
    (g : ℕ → C(HaarCircle, ℂ)) (e : B)
    (hlim : Tendsto (fun n => traceTwoNorm τ (Φ (g n) - e)) atTop (𝓝 0)) :
    ∃ c : ℕ → B, (∀ n, c n ∈ haarLaurentSpan v) ∧
      Tendsto (fun n => traceTwoNorm τ (c n - e)) atTop (𝓝 0) := by
  exact exists_haarLaurent_approx_of_traceTwoNorm_limit τ v (fun n => Φ (g n)) e
    (fun n => exists_haarLaurent_approx_of_functional τ v Φ hΦ (g n)) hlim

theorem haarLaurentSpan_mul_mem (v : unitary B) {x y : B}
    (hx : x ∈ haarLaurentSpan v) (hy : y ∈ haarLaurentSpan v) :
    x * y ∈ haarLaurentSpan v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      rw [← haarPower_add]
      exact haarPower_mem_haarLaurentSpan v (k + l)
    | zero => simp
    | add y z hy hz ihy ihz => simpa [mul_add] using (haarLaurentSpan v).add_mem ihy ihz
    | smul c y hy ih => simpa using (haarLaurentSpan v).smul_mem c ih
  | zero => simp
  | add x z hx hz ihx ihz => simpa [add_mul] using (haarLaurentSpan v).add_mem ihx ihz
  | smul c x hx ih => simpa using (haarLaurentSpan v).smul_mem c ih

theorem haarLaurentSpan_star_mem (v : unitary B) {x : B}
    (hx : x ∈ haarLaurentSpan v) : star x ∈ haarLaurentSpan v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [← haarPower_neg]
    exact haarPower_mem_haarLaurentSpan v (-k)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [star_add] using (haarLaurentSpan v).add_mem ihx ihy
  | smul c x hx ih => simpa only [star_smul] using (haarLaurentSpan v).smul_mem (star c) ih

/-- Approximation in the tracial two-norm by finite Laurent polynomials. -/
def HaarLaurentApproximable (τ : FaithfulTracialState B) (v : unitary B) (x : B) : Prop :=
  ∃ c : ℕ → B, (∀ n, c n ∈ haarLaurentSpan v) ∧
    Tendsto (fun n => traceTwoNorm τ (c n - x)) atTop (𝓝 0)

theorem haarLaurentApproximable_of_mem (τ : FaithfulTracialState B) (v : unitary B)
    {x : B} (hx : x ∈ haarLaurentSpan v) : HaarLaurentApproximable τ v x := by
  refine ⟨fun _ => x, fun _ => hx, ?_⟩
  simp [traceTwoNorm]

theorem HaarLaurentApproximable.add {τ : FaithfulTracialState B} {v : unitary B}
    {x y : B} (hx : HaarLaurentApproximable τ v x) (hy : HaarLaurentApproximable τ v y) :
    HaarLaurentApproximable τ v (x + y) := by
  obtain ⟨f, hf, hfLim⟩ := hx
  obtain ⟨g, hg, hgLim⟩ := hy
  refine ⟨fun n => f n + g n, fun n => (haarLaurentSpan v).add_mem (hf n) (hg n), ?_⟩
  apply squeeze_zero (fun n => traceTwoNorm_nonneg τ _)
    (fun n => ?_) (show Tendsto (fun n => traceTwoNorm τ (f n - x) +
      traceTwoNorm τ (g n - y)) atTop (𝓝 0) by simpa using hfLim.add hgLim)
  simpa only [add_sub_add_comm] using traceTwoNorm_add_le τ (f n - x) (g n - y)

theorem HaarLaurentApproximable.star_closed {τ : FaithfulTracialState B} {v : unitary B}
    {x : B} (hx : HaarLaurentApproximable τ v x) : HaarLaurentApproximable τ v (star x) := by
  obtain ⟨f, hf, hfLim⟩ := hx
  refine ⟨fun n => star (f n), fun n => haarLaurentSpan_star_mem v (hf n), ?_⟩
  simpa only [← star_sub, traceTwoNorm_star] using hfLim

/-- Product approximation is diagonal: the second error is chosen after the
norm of the first approximant is known. Uniform bounds are unnecessary. -/
theorem HaarLaurentApproximable.mul {τ : FaithfulTracialState B} {v : unitary B}
    {x y : B} (hx : HaarLaurentApproximable τ v x) (hy : HaarLaurentApproximable τ v y) :
    HaarLaurentApproximable τ v (x * y) := by
  obtain ⟨f, hf, hfLim⟩ := hx
  obtain ⟨g, hg, hgLim⟩ := hy
  have hchoose (n : ℕ) : ∃ k : ℕ,
      traceTwoNorm τ (g k - y) < (1 / ((n : ℝ) + 1)) / (‖f n‖ + 1) := by
    have hevent := (tendsto_order.1 hgLim).2 ((1 / ((n : ℝ) + 1)) / (‖f n‖ + 1))
      (by positivity)
    exact hevent.exists
  choose k hk using hchoose
  refine ⟨fun n => f n * g (k n),
    fun n => haarLaurentSpan_mul_mem v (hf n) (hg (k n)), ?_⟩
  have hsmall (n : ℕ) : ‖f n‖ * traceTwoNorm τ (g (k n) - y) ≤ 1 / ((n : ℝ) + 1) := by
    calc
      _ ≤ (‖f n‖ + 1) * traceTwoNorm τ (g (k n) - y) :=
        mul_le_mul_of_nonneg_right (by linarith) (traceTwoNorm_nonneg τ _)
      _ ≤ (‖f n‖ + 1) * ((1 / ((n : ℝ) + 1)) / (‖f n‖ + 1)) :=
        mul_le_mul_of_nonneg_left (hk n).le (by positivity)
      _ = _ := by field_simp
  have hb (n : ℕ) : traceTwoNorm τ (f n * g (k n) - x * y) ≤
      1 / ((n : ℝ) + 1) + traceTwoNorm τ (f n - x) * ‖y‖ := by
    calc
      _ = traceTwoNorm τ (f n * (g (k n) - y) + (f n - x) * y) := by
        congr 1; noncomm_ring
      _ ≤ traceTwoNorm τ (f n * (g (k n) - y)) + traceTwoNorm τ ((f n - x) * y) :=
        traceTwoNorm_add_le τ _ _
      _ ≤ ‖f n‖ * traceTwoNorm τ (g (k n) - y) + traceTwoNorm τ (f n - x) * ‖y‖ :=
        add_le_add (traceTwoNorm_mul_le_left τ _ _) (traceTwoNorm_mul_le_right τ _ _)
      _ ≤ _ := add_le_add (hsmall n) le_rfl
  have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) +
      traceTwoNorm τ (f n - x) * ‖y‖) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.add (hfLim.mul_const ‖y‖)
  exact squeeze_zero (fun n => traceTwoNorm_nonneg τ _) hb hz

/-- The tracial closure of Laurent polynomials, restricted to bounded elements
of the ambient C*-algebra, is an actual star subalgebra. -/
def haarLaurentTraceClosure (τ : FaithfulTracialState B) (v : unitary B) :
    StarSubalgebra ℂ B where
  carrier := {x | HaarLaurentApproximable τ v x}
  zero_mem' := haarLaurentApproximable_of_mem τ v (haarLaurentSpan v).zero_mem
  add_mem' := HaarLaurentApproximable.add
  one_mem' := haarLaurentApproximable_of_mem τ v (by
    simpa only [haarPower_zero] using haarPower_mem_haarLaurentSpan v 0)
  mul_mem' := HaarLaurentApproximable.mul
  algebraMap_mem' c := haarLaurentApproximable_of_mem τ v (by
    rw [Algebra.algebraMap_eq_smul_one]
    apply (haarLaurentSpan v).smul_mem
    simpa only [haarPower_zero] using haarPower_mem_haarLaurentSpan v 0)
  star_mem' := HaarLaurentApproximable.star_closed

@[simp]
theorem mem_haarLaurentTraceClosure (τ : FaithfulTracialState B) (v : unitary B) (x : B) :
    x ∈ haarLaurentTraceClosure τ v ↔ HaarLaurentApproximable τ v x := Iff.rfl

theorem unitary_mem_haarLaurentTraceClosure (τ : FaithfulTracialState B) (v : unitary B) :
    (v : B) ∈ haarLaurentTraceClosure τ v :=
  haarLaurentApproximable_of_mem τ v (by simpa [haarPower] using haarPower_mem_haarLaurentSpan v (1 : ℤ))

theorem mem_haarLaurentTraceClosure_of_functional_limit
    (τ : FaithfulTracialState B) (v : unitary B)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n)
    (g : ℕ → C(HaarCircle, ℂ)) (e : B)
    (hlim : Tendsto (fun n => traceTwoNorm τ (Φ (g n) - e)) atTop (𝓝 0)) :
    e ∈ haarLaurentTraceClosure τ v :=
  exists_haarLaurent_approx_of_functional_limit τ v Φ hΦ g e hlim

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}

/-- Every base-algebra element is trace independent of the entire bounded
tracial Laurent closure. -/
theorem projectionTraceIndependent_haarLaurentTraceClosure (h : FreeHaarMoments τ A v)
    {p : B} (hp : p ∈ A) : ProjectionTraceIndependent τ p (haarLaurentTraceClosure τ v) := by
  intro x hx
  obtain ⟨c, hc, hlim⟩ := hx
  exact h.trace_mul_eq_mul_trace_of_laurent_approx hp c hc hlim

/-- The degree-two factorization passes through the continuous cutoff limit. -/
theorem trace_mul_eq_mul_trace_of_functional_limit (h : FreeHaarMoments τ A v)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n)
    (g : ℕ → C(HaarCircle, ℂ)) {p e : B} (hp : p ∈ A)
    (hlim : Tendsto (fun n => traceTwoNorm τ (Φ (g n) - e)) atTop (𝓝 0)) :
    τ.toLinearMap (p * e) = τ.toLinearMap p * τ.toLinearMap e := by
  obtain ⟨c, hc, hclim⟩ := exists_haarLaurent_approx_of_functional_limit τ v Φ hΦ g e hlim
  exact h.trace_mul_eq_mul_trace_of_laurent_approx hp c hc hclim

/-- In particular the two precise centered projection moments hold for the
arc projection constructed as a tracial limit of continuous cutoffs. -/
theorem centeredProjectionMoments_of_functional_limit (h : FreeHaarMoments τ A v)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n)
    (g : ℕ → C(HaarCircle, ℂ)) {p e : B} {t η : ℝ}
    (hp : p ∈ A) (hpτ : τ.toLinearMap p = (t : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ))
    (hlim : Tendsto (fun n => traceTwoNorm τ (Φ (g n) - e)) atTop (𝓝 0)) :
    CenteredProjectionMoments τ p e t η := by
  obtain ⟨c, hc, hclim⟩ := exists_haarLaurent_approx_of_functional_limit τ v Φ hΦ g e hlim
  exact h.centeredProjectionMoments_of_laurent_approx hp hpτ heτ c hc hclim

end FreeHaarMoments

end

end KadisonKastler

end OAI
