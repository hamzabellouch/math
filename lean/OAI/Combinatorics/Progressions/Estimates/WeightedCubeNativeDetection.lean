import OAI.Combinatorics.Progressions.Polynomial.CubeMixtureAllDegrees

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_weighted_cube_mixture (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {Ω : Type*} [Fintype Ω] {I : Ω → Type*} [∀ a, Fintype (I a)]
      (μ : FiniteProbabilityWeights Ω) (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : ∀ a, I a → ℂ)
        (twist : ∀ a, I a → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ a i ω x, x ∈ integerBox N → ‖twist a i ω x‖ ≤ 1) →
      μ.mean (fun a => ∑ i, ‖c a i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - μ.complexMean (fun a => ∑ i, c a i *
        (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
          let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
          ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
            twist a i ω (physicalCubeVertexValue u ω)))‖ ≤ Real.exp (-p) / 2 →
      ∃ (a : Ω) (i : I a)
        (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
          (integerBox N) id (fun x => f x * twist a i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist a i ∅ x) * V.test.eval x)‖ := by
  obtain ⟨C, hC, hdetect⟩ := exists_native_partner_of_physical_cube_mixture_all_degrees s
  refine ⟨C, hC, ?_⟩
  intro n N _ Ω _ I _ μ p hp hn f c twist hf ht hc z hz herr
  let c' : (Σ a, I a) → ℂ := fun i => (μ.weight i.1 : ℂ) * c i.1 i.2
  have hc' : (∑ i, ‖c' i‖) ≤ Real.exp p := by
    simpa only [c', FiniteProbabilityWeights.mean, Fintype.sum_sigma, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (μ.nonneg _), ← Finset.mul_sum] using hc
  have herr' : ‖z - ∑ i : (Σ a, I a), c' i *
      (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i.1 i.2 ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 := by
    simpa only [c', Fintype.sum_sigma, FiniteProbabilityWeights.complexMean,
      Finset.mul_sum, mul_assoc] using herr
  obtain ⟨i, V, hV, hcorr⟩ := hdetect N p hp hn f c' (fun i => twist i.1 i.2)
    hf (fun i => ht i.1 i.2) hc' z hz herr'
  exact ⟨i.1, i.2, V, hV, hcorr⟩

end Erdos3

end

end OAI
