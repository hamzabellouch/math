import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoefficientGradientApply

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology

lemma carleman_large_parameter (C M : ℝ) : ∃ T > 0, ∀ τ ≥ T,
    0 ≤ τ ∧ τ*M + C^2*τ^2 ≤ (1/2:ℝ)*τ^3 := by
  refine ⟨4*(|M|+C^2+1), by positivity, fun τ hτ => ?_⟩
  have hM := abs_nonneg M
  have hCs := sq_nonneg C
  have ht : 1 ≤ τ := by linarith
  have ht0 : 0 ≤ τ := by linarith
  refine ⟨ht0, ?_⟩
  have hm : M ≤ τ/4 := by linarith [le_abs_self M]
  have hc : C^2 ≤ τ/4 := by linarith
  have hh1 := mul_le_mul_of_nonneg_right hm ht0
  have hh2 := mul_le_mul_of_nonneg_right hc (sq_nonneg τ)
  have hh3 := mul_le_mul_of_nonneg_right ht (sq_nonneg τ)
  nlinarith only [hh1, hh2, hh3]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

theorem exists_local_carleman (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0) :
    ∃ H > 0, ∃ U ∈ 𝓝 x₀, ∃ T > 0, ∀ (K : Compacts E), (↑K : Set E) ⊆ U →
      ∀ τ ≥ T, ∀ f : EllipticTest K,
        τ * testGradientSquare K e f + (1/2:ℝ)*τ^3*testPair K f f ≤
          testPair K
            (carlemanSymmetric K e a (coefficientNorm e a (convexifyPhase ψ H)) τ f +
              carlemanSkew K e (coefficientGradient e a (convexifyPhase ψ H)) τ f)
            (carlemanSymmetric K e a (coefficientNorm e a (convexifyPhase ψ H)) τ f +
              carlemanSkew K e (coefficientGradient e a (convexifyPhase ψ H)) τ f) := by
  obtain ⟨C, hC, henergy⟩ := exists_carleman_energy_shift e a ha ψ x₀ hψ hpos
  let p₀ := coefficientNorm e a ψ x₀
  let R₀ := coefficientTransport e (coefficientGradient e a ψ) (coefficientNorm e a ψ) x₀
  have hp : 0 < p₀ := coefficientNorm_pos e a ψ x₀ hpos hgrad
  let H := (|2*C*p₀ - 2*R₀| + 2)/(4*p₀^2)
  have hH : 0 < H := div_pos (by positivity) (by positivity)
  have hHeq : 4*H*p₀^2 = |2*C*p₀-2*R₀|+2 := by
    dsimp [H]
    field_simp
  let φ := convexifyPhase ψ H
  let X := coefficientGradient e a φ
  let p := coefficientNorm e a φ
  have hmass : 2 ≤ 2*coefficientTransport e X p x₀ - 2*C*p x₀ := by
    dsimp only [X, p, φ]
    rw [phase_transport_norm_at e a ψ H x₀ hψ, phase_norm_at e a ψ H x₀ hψ]
    change 2 ≤ 2*(R₀+2*H*p₀^2)-2*C*p₀
    linarith [le_abs_self (2*C*p₀-2*R₀)]
  have he : ∀ᶠ x in 𝓝 x₀, ∀ v, squareSum v ≤
      pointwiseQuadratic (carlemanMatrix e a X C) x v :=
    continuous_matrix_lower_near (fun x i j => carlemanMatrix e a X C i j x)
      (fun i j => (SmoothScalar.contDiff _).continuous) x₀ (henergy H hH.le)
  have hmc : Continuous (fun x => 2*coefficientTransport e X p x - 2*C*p x) :=
    (continuous_const.mul (SmoothScalar.contDiff _).continuous).sub
      (continuous_const.mul (SmoothScalar.contDiff _).continuous)
  have hem : ∀ᶠ x in 𝓝 x₀, 1 ≤ 2*coefficientTransport e X p x - 2*C*p x :=
    ((hmc.tendsto x₀).eventually_const_lt (by linarith : (1:ℝ) <
      2*coefficientTransport e X p x₀ - 2*C*p x₀)).mono fun _ h => h.le
  let q := coefficientElliptic e a (coefficientDivergence e X)
  let M := |q x₀|+1
  have heq : ∀ᶠ x in 𝓝 x₀, q x ≤ M :=
    (((SmoothScalar.contDiff q).continuous.tendsto x₀).eventually_lt_const
      (by dsimp [M]; linarith [le_abs_self (q x₀)])).mono fun _ h => h.le
  let U := {x | (∀ v, squareSum v ≤ pointwiseQuadratic (carlemanMatrix e a X C) x v) ∧
    1 ≤ 2*coefficientTransport e X p x - 2*C*p x ∧ q x ≤ M}
  have hU : U ∈ 𝓝 x₀ := he.and (hem.and heq)
  obtain ⟨T, hT, hlarge⟩ := carleman_large_parameter C M
  refine ⟨H, hH, U, hU, T, hT, fun K hKU τ hτ f => ?_⟩
  obtain ⟨ht0, htn⟩ := hlarge τ hτ
  have hgb : (1:ℝ) * testGradientSquare K e f ≤
      carlemanGradient K e a X f + 2*C*testEnergy K e a f f :=
    carleman_gradient_bound K e a X C 1
      (fun x hx v => by simpa only [one_mul, squareSum] using (hKU hx).1 v) f
  have hh := carleman_coercive_of_bounds K e a ha X p τ C 1 M ht0 f hgb
    (fun x hx => (hKU hx).2.1) (fun x hx => (hKU hx).2.2) htn
  simpa only [mul_one] using hh


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma testPair_sub_square_bound (f g : EllipticTest K) :
    testPair K (f-g) (f-g) ≤ 2*testPair K f f + 2*testPair K g g := by
  have h := testPair_nonneg K (f+g)
  simp only [testPair_add_left, testPair_add_right, testPair_comm K g f] at h
  simp only [testPair_sub_left, testPair_sub_right, testPair_comm K g f]
  linarith

lemma testMultiply_square_bound (V : SmoothScalar E) (B : ℝ)
    (hV : ∀ x ∈ K, (V x)^2 ≤ B) (f : EllipticTest K) :
    testPair K (testMultiply K V f) (testMultiply K V f) ≤ B * testPair K f f := by
  rw [← testMultiply_symmetric, ← testMultiply_mul]
  exact weightedPair_le_of_bound K (V*V) B (fun x hx => by
    simpa only [Subalgebra.coe_mul, Pi.mul_apply, pow_two] using hV x hx) f

def testSchrodinger (a : ι → ι → SmoothScalar E) (V : SmoothScalar E) :
    EllipticTest K →ₗ[ℝ] EllipticTest K := testElliptic K e a + testMultiply K V

theorem exists_local_weighted_carleman (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V ψ : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0) :
    ∃ H > 0, ∃ U ∈ 𝓝 x₀, ∃ T > 0, ∀ (K : Compacts E), (↑K : Set E) ⊆ U →
      ∀ τ ≥ T, ∀ u : EllipticTest K,
        testPair K (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u)
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u) ≤
        8 * testPair K
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u))
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u)) := by
  obtain ⟨H,hH,U,hU,T,hT,hest⟩ := exists_local_carleman e a ha ψ x₀ hψ hpos hgrad
  let B := (V x₀)^2+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbnd : ∀ᶠ x in 𝓝 x₀, (V x)^2 ≤ B :=
    ((((SmoothScalar.contDiff V).continuous.pow 2).tendsto x₀).eventually_lt_const
      (by dsimp [B]; linarith)).mono fun _ h => h.le
  refine ⟨H,hH,U ∩ {x | (V x)^2 ≤ B},inter_mem hU hbnd,max T (8*B+1),
    lt_of_lt_of_le hT (le_max_left ..),fun K hK τ hτ u => ?_⟩
  have ht : T ≤ τ := (le_max_left ..).trans hτ
  have htB : 8*B+1 ≤ τ := (le_max_right ..).trans hτ
  have ht1 : 1 ≤ τ := by linarith
  have ht0 : 0 ≤ τ := by linarith
  let φ := convexifyPhase ψ H
  let f := testMultiply K (exponentialWeight φ τ) u
  let r := testMultiply K (exponentialWeight φ τ) (testSchrodinger K e a V u)
  have hcar := hest K (fun x hx => (hK hx).1) τ ht f
  rw [carleman_conjugation] at hcar
  · have hid : testMultiply K (exponentialWeight φ τ) (testElliptic K e a u) =
        r - testMultiply K V f := by
      dsimp only [r, f, testSchrodinger]
      simp only [LinearMap.add_apply, map_add, ← testMultiply_mul]
      rw [mul_comm V (exponentialWeight φ τ)]
      abel
    change τ*testGradientSquare K e f + (1/2:ℝ)*τ^3*testPair K f f ≤
      testPair K (testMultiply K (exponentialWeight φ τ) (testElliptic K e a u))
        (testMultiply K (exponentialWeight φ τ) (testElliptic K e a u)) at hcar
    rw [hid] at hcar
    have hs := testPair_sub_square_bound K r (testMultiply K V f)
    have hv := testMultiply_square_bound K V B (fun x hx => (hK hx).2) f
    have hg : 0 ≤ τ*testGradientSquare K e f := mul_nonneg ht0
      (Finset.sum_nonneg fun _ _ => testPair_nonneg K _)
    have hτcube : 8*B+1 ≤ τ^3 := htB.trans (by
      have h1 := mul_le_mul_of_nonneg_left ht1 ht0
      have h2 := mul_le_mul_of_nonneg_left ht1 (sq_nonneg τ)
      nlinarith)
    have hf0 := testPair_nonneg K f
    have hh := mul_le_mul_of_nonneg_right hτcube hf0
    change testPair K f f ≤ 8*testPair K r r
    have hbf := mul_nonneg hB.le hf0
    have hr0 := testPair_nonneg K r
    nlinarith only [hcar,hs,hv,hg,hh,hf0,hbf,hr0]
  · exact ha



end YauCounterexamples
end

end OAI
