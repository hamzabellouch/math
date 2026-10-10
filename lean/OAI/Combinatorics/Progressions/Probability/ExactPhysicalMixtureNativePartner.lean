import OAI.Combinatorics.Progressions.Polynomial.CubeMixtureAllDegrees

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem native_partner_of_exact_physical_mixture {s n : ℕ} (N : Fin n → ℕ)
    [∀ j, NeZero (N j)] {I : Type} [Fintype I]
    (input : (Fin n → ℤ) → ℂ) (c : I → ℂ)
    (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ)
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (n : ℝ) ≤ budget)
    (hinput : ∀ u ∈ integerBox N, ‖input u‖ ≤ 1)
    (htwist : ∀ i site u, ‖twist i site u‖ ≤ 1)
    (hmass : (∑ i, ‖c i‖) ≤ Real.exp budget) {z : ℂ}
    (hpositive : Real.exp (-budget) ≤ z.re)
    (hvalue : z = ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
      let v := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
      ∏ site, conjugationPower site.card (input (physicalCubeVertexValue v site)) *
        twist i site (physicalCubeVertexValue v site))) :
    ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun u => input u * twist i ∅ u)), V.test.normBound ≤ 1 := by
  obtain ⟨i, V, hV, _⟩ := (Classical.choose_spec (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)).2
    N budget hbudget hdimension input c twist hinput (fun i site u _ => htwist i site u) hmass
    z hpositive (by rw [hvalue, sub_self, norm_zero]; positivity)
  exact ⟨i, V, hV⟩
end Erdos3

end

end OAI
