import OAI.Dynamics.TriangleBilliards.CovariantGenerators

namespace OAI

universe uE uH uIota

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T} {u a b : H}

lemma projection_covariant (h : RotationalCR X Y V u a b) (j : ℤ) :
    RotationalCR X Y V (V.projection j u) (V.projection (j+1) a) (V.projection (j-1) b) := by
  intro θ
  have hx := (h.projection j).1.smul (fourier j θ)
  have hy := (h.projection j).2.smul (fourier j θ)
  simp only [V.projection_eigen]
  have ha : fourier (-1) θ * fourier (j+1) θ = fourier j θ := by
    rw [← fourier_add]; congr 2; ring
  have hb : fourier 1 θ * fourier (j-1) θ = fourier j θ := by
    rw [← fourier_add]; congr 2; ring
  rw [smul_smul, ha, smul_smul, hb]
  constructor
  · simpa only [smul_add] using hx
  · simpa only [smul_comm (fourier j θ) Complex.I, smul_sub] using hy

omit [CompleteSpace H] [Fact (0 < T)] in
lemma add {v c d : H} (h : RotationalCR X Y V u a b) (k : RotationalCR X Y V v c d) :
    RotationalCR X Y V (u+v) (a+c) (b+d) := by
  intro θ
  have hx := (h θ).1.add (k θ).1
  have hy := (h θ).2.add (k θ).2
  simp only [map_add, smul_add]
  constructor
  · convert hx using 1; abel
  · convert hy using 1; module

omit [CompleteSpace H] [Fact (0 < T)] in
lemma smul (h : RotationalCR X Y V u a b) (c : ℂ) :
    RotationalCR X Y V (c • u) (c • a) (c • b) := by
  intro θ
  have hx := (h θ).1.smul c
  have hy := (h θ).2.smul c
  simp only [map_smul]
  constructor
  · convert hx using 1; module
  · convert hy using 1; module

end RotationalCR
end TriangularBilliards.Analysis
namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T} {u a b aa c bb : H}

omit [Fact (0 < T)] in
lemma norm_eq_of_second (h : RotationalCR X Y V u a b)
    (ha : RotationalCR X Y V a aa c) (hb : RotationalCR X Y V b c bb) : ‖a‖ = ‖b‖ := by
  obtain ⟨hxu,hyu⟩ := h.generators
  obtain ⟨hxa,hya⟩ := ha.generators
  obtain ⟨hxb,hyb⟩ := hb.generators
  have hxy : X.HasGenerator (Complex.I • (a-b)) (Complex.I • (aa-bb)) := by
    have hh := (hxa.add (hxb.smul (-1))).smul Complex.I
    convert hh using 1 <;> module
  have hyx : Y.HasGenerator (a+b) (Complex.I • (aa-bb)) := by
    have hh := hya.add hyb
    convert hh using 1
    module
  have hn := HilbertFlow.commuting_generators_CR hxu hyu hxy hyx
  have h₁ : a + b + Complex.I • (Complex.I • (a-b)) = (2 : ℂ) • b := by
    rw [smul_smul, Complex.I_mul_I]; module
  have h₂ : a + b - Complex.I • (Complex.I • (a-b)) = (2 : ℂ) • a := by
    rw [smul_smul, Complex.I_mul_I]; module
  rw [h₁, h₂, norm_smul, norm_smul] at hn
  norm_num at hn
  linarith

lemma projected_norm_eq (h : RotationalCR X Y V u a b)
    (ha : RotationalCR X Y V a aa c) (hb : RotationalCR X Y V b c bb) (j : ℤ) :
    ‖V.projection (j+1) a‖ = ‖V.projection (j-1) b‖ := by
  apply norm_eq_of_second (h.projection_covariant j)
    (c := V.projection j c) (aa := V.projection (j+2) aa) (bb := V.projection (j-2) bb)
  · convert ha.projection_covariant (j+1) using 1 <;> congr 2 <;> ring
  · convert hb.projection_covariant (j-1) using 1 <;> congr 2 <;> ring

end RotationalCR

omit [CompleteSpace H] in
lemma real_parts_CR_algebra (z : ℂ) (x y : H) :
    (z.re : ℂ) • x - (z.im : ℂ) • y =
      conj z • ((1/2 : ℂ) • (x-Complex.I • y)) + z • ((1/2 : ℂ) • (x+Complex.I • y)) := by
  have hr : (z.re : ℂ) = (conj z + z) / 2 := by apply Complex.ext <;> simp
  have hi : (z.im : ℂ) = (z-conj z) / (2*Complex.I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]; ring
  rw [hr, hi]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  module

omit [CompleteSpace H] in
lemma imag_parts_CR_algebra (z : ℂ) (x y : H) :
    (z.im : ℂ) • x + (z.re : ℂ) • y =
      Complex.I • (conj z • ((1/2 : ℂ) • (x-Complex.I • y)) -
        z • ((1/2 : ℂ) • (x+Complex.I • y))) := by
  have hr : (z.re : ℂ) = (conj z + z) / 2 := by apply Complex.ext <;> simp
  have hi : (z.im : ℂ) = (z-conj z) / (2*Complex.I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]; ring
  rw [hr, hi]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  match_scalars
  all_goals ring_nf
  all_goals simp only [Complex.I_sq, mul_neg, mul_one]
  all_goals ring

end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis.CircleAction
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)] (V : CircleAction H T)

lemma projection_commute (L : H →L[ℂ] H)
    (hL : ∀ θ u, L (V.act θ u) = V.act θ (L u)) (j : ℤ) (u : H) :
    L (V.projection j u) = V.projection j (L u) := by
  rw [V.projection_apply, V.projection_apply, ← L.integral_comp_comm (V.weighted_integrable j u)]
  simp only [map_smul, hL]

lemma bessel_reindex {ι : Type uIota} (φ : ι → ℤ) (hφ : Function.Injective φ)
    (u : H) (s : Finset ι) : ∑ i ∈ s, ‖V.projection (φ i) u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  classical
  have hh := V.bessel u (s.image φ)
  rwa [Finset.sum_image (fun i _ k _ hik => hφ hik)] at hh

end TriangularBilliards.Analysis.CircleAction
/-! The real Hilbert formulation applies to the realification of a complex
L² space: real parts of complex inner products are real inner products. -/

open Filter Finset Set
open scoped Topology BigOperators

noncomputable section

namespace TriangularBilliards.Analytic

/-- The finite Cauchy–Schwarz bound used in the localized parity recurrence. -/
lemma sum_products_le {ι : Type uIota} (s : Finset ι) (a b : ι → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : (∑ i ∈ s, (a i) ^ 2) ≤ A ^ 2)
    (hb : (∑ i ∈ s, (b i) ^ 2) ≤ B ^ 2) :
    (∑ i ∈ s, a i * b i) ≤ A * B := by
  calc
    (∑ i ∈ s, a i * b i) ≤
        Real.sqrt (∑ i ∈ s, (a i) ^ 2) * Real.sqrt (∑ i ∈ s, (b i) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s a b
    _ ≤ Real.sqrt (A ^ 2) * Real.sqrt (B ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = A * B := by rw [Real.sqrt_sq hA, Real.sqrt_sq hB]

/-- Exact finite telescoping plus localization. The sequences `a` and `b`
are the norms of the two factors restricted to the spatial support of Xw. -/
lemma parity_energy_finite (D a b : ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrec : ∀ k, D k - D (k + 1) ≤ a k * b k)
    (ha : ∀ n, (∑ k ∈ range n, (a k) ^ 2) ≤ A ^ 2)
    (hb : ∀ n, (∑ k ∈ range n, (b k) ^ 2) ≤ B ^ 2)
    (n : ℕ) : D 0 - D n ≤ A * B := by
  calc
    D 0 - D n = ∑ k ∈ range n, (D k - D (k + 1)) :=
      (sum_range_sub' D n).symm
    _ ≤ ∑ k ∈ range n, a k * b k := sum_le_sum fun k _ => hrec k
    _ ≤ A * B := sum_products_le (range n) a b hA hB (ha n) (hb n)

/-- The infinite-tail passage in the energy estimate.
Only the regularized test field needs its terminal energies to tend to zero;
no decay is required of the invariant field. -/
lemma parity_energy (D a b : ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrec : ∀ k, D k - D (k + 1) ≤ a k * b k)
    (ha : ∀ n, (∑ k ∈ range n, (a k) ^ 2) ≤ A ^ 2)
    (hb : ∀ n, (∑ k ∈ range n, (b k) ^ 2) ≤ B ^ 2)
    (hD : Tendsto D atTop (𝓝 0)) : D 0 ≤ A * B := by
  have hlim : Tendsto (fun n => D 0 - D n) atTop (𝓝 (D 0)) := by
    simpa using tendsto_const_nhds.sub hD
  exact le_of_tendsto' hlim (parity_energy_finite D a b hA hB hrec ha hb)

section RealHilbert

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm-difference identity for the Cauchy–Riemann recurrence. -/
lemma inner_sum_difference (u v : E) :
    inner ℝ (u + v) (u - v) = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u]
  ring

/-- A version of the energy estimate with the Hilbert-space coefficient
factors still visible. The equality of the two Cauchy–Riemann norms enters
as `hnorm`; it is not asserted for nonsmooth invariant functions here. -/
lemma coefficient_energy (a b : ℕ → E) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnorm : ∀ k, ‖a k‖ = ‖b k‖)
    (hX : ∀ n, (∑ k ∈ range n, ‖a k + b (k + 1)‖ ^ 2) ≤ A ^ 2)
    (hY : ∀ n, (∑ k ∈ range n, ‖a k - b (k + 1)‖ ^ 2) ≤ B ^ 2)
    (htail : Tendsto (fun n => ‖a n‖ ^ 2) atTop (𝓝 0)) :
    ‖a 0‖ ^ 2 ≤ A * B := by
  apply parity_energy (fun n => ‖a n‖ ^ 2)
    (fun n => ‖a n + b (n + 1)‖) (fun n => ‖a n - b (n + 1)‖)
    hA hB ?_ hX hY htail
  intro k
  rw [hnorm (k + 1), ← inner_sum_difference]
  exact real_inner_le_norm _ _

end RealHilbert

end TriangularBilliards.Analytic

namespace TriangularBilliards.Analysis.CircleAction
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)] (V : CircleAction H T)

omit [CompleteSpace H] in
lemma real_inner_sum_sub (a b : H) :
    (inner ℂ (a+b) (a-b)).re = ‖a‖^2 - ‖b‖^2 := by
  simp only [inner_add_left, inner_sub_right, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, Complex.add_re, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hh := inner_re_symm (𝕜 := ℂ) a b
  change (inner ℂ a b).re = (inner ℂ b a).re at hh
  linarith

/-- The support-localized coefficient estimate. `R` is the spatial
restriction operator; angular commutation and self-adjointness are the
only properties of that operator used. Terminal-mode decay follows from
Bessel and is NOT a hypothesis about an invariant field. -/
lemma localized_CR_energy (a b : H) (j : ℤ) (R : H →L[ℂ] H)
    (hR : ∀ θ u, R (V.act θ u) = V.act θ (R u))
    (hRs : ∀ u v, inner ℂ (R u) v = inner ℂ u (R v))
    (hX : R (a+b) = a+b)
    (hnorm : ∀ k : ℤ, ‖V.projection (k+2) a‖ = ‖V.projection k b‖) :
    ‖V.projection (j+1) a‖ ^ 2 ≤ ‖a+b‖ * ‖R (a-b)‖ := by
  let φ : ℕ → ℤ := fun n => j + 1 + 2 * (n : ℤ)
  have hφ : Function.Injective φ := parity_index_injective (j+1)
  have hn (n : ℕ) : ‖V.projection (φ (n+1)) a‖ = ‖V.projection (φ n) b‖ := by
    have he : φ (n+1) = φ n + 2 := by dsimp [φ]; ring
    rw [he, hnorm]
  have hc (n : ℕ) : R (V.projection (φ n) (a+b)) = V.projection (φ n) (a+b) := by
    rw [V.projection_commute R hR, hX]
  have hrec (n : ℕ) : ‖V.projection (φ n) a‖^2 - ‖V.projection (φ (n+1)) a‖^2 ≤
      ‖V.projection (φ n) (a+b)‖ * ‖V.projection (φ n) (R (a-b))‖ := by
    rw [hn n, ← real_inner_sum_sub]
    rw [← map_add, ← map_sub]
    have he := hRs (V.projection (φ n) (a+b)) (V.projection (φ n) (a-b))
    rw [hc n, V.projection_commute R hR] at he
    rw [he]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  have hd : Tendsto (fun n => ‖V.projection (φ n) a‖ ^ 2) atTop (𝓝 0) := by
    have hh := ((V.projection_escape hφ a).norm).pow 2
    simpa using hh
  have hh := Analytic.parity_energy
    (fun n => ‖V.projection (φ n) a‖^2)
    (fun n => ‖V.projection (φ n) (a+b)‖)
    (fun n => ‖V.projection (φ n) (R (a-b))‖)
    (norm_nonneg (a+b)) (norm_nonneg (R (a-b))) hrec
    (fun n => V.bessel_reindex φ hφ (a+b) (Finset.range n))
    (fun n => V.bessel_reindex φ hφ (R (a-b)) (Finset.range n)) hd
  simpa only [φ, Nat.cast_zero, mul_zero, add_zero] using hh

end TriangularBilliards.Analysis.CircleAction

end
end
end
end
end
end
end
end

end OAI
