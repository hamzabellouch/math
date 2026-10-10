import OAI.NumberTheory.Ostmann.Conclusion.RegularNormAP

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Arithmetic.PrimeCellReplacement Ostmann.Arithmetic.PrimeProgression

theorem exists_positiveUnitTest_primeCell_upper_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ lo hi : ℝ, L₀ ≤ lo → lo ≤ hi → hi-lo ≤ 1 →
      ∀ (N M : ℕ) [NeZero M] (Z : ℝ), ⌊Real.exp hi⌋₊ ≤ N → 0 < Z →
      (M : ℝ) ≤ Real.exp (d*lo^(1/3 : ℝ)) →
      ∀ (F : (ZMod M)ˣ → ℝ) (C : ℝ), (∀ u, 0 ≤ F u) →
      (∑ u : (ZMod M)ˣ, F u) ≤ C →
      realTestSum N M lo hi Z F ≤
        (harmonicIntegral M lo hi/Z+(K/Z)*Real.exp (-d*lo^(1/3 : ℝ)))*C := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_primeCell_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro lo hi hlo horder hwidth N M _ Z hN hZ hmod F C hF hsum
  have hh := hAP lo hi hlo horder hwidth N M Z hN hZ hmod
  have he := hh.2.1 F hF
  have he' := (le_abs_self _).trans he
  have hunit := hh.1 1 (isUnit_one : IsUnit (1 : ZMod M))
  have hunit' := (le_abs_self _).trans hunit
  have hnonneg : 0 ≤ harmonicIntegral M lo hi/Z+(K/Z)*Real.exp (-d*lo^(1/3 : ℝ)) := by
    have hm := residueMass_nonneg N M 1 lo hi hZ.le
    linarith
  calc
    _ ≤ (harmonicIntegral M lo hi/Z+(K/Z)*Real.exp (-d*lo^(1/3 : ℝ)))*
        ∑ u : (ZMod M)ˣ, F u := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hnonneg

end Ostmann.Conclusion

end

end OAI
