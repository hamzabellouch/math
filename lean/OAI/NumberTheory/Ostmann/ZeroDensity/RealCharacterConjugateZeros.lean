import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.Uniqueness
import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterComplexification

namespace OAI

/-! # Conjugate partners in the actual real-character zero family -/

namespace Ostmann

open Complex Filter Set
open scoped Topology ComplexConjugate

theorem PrimitiveRealCharacter.L_conj_right (χ : PrimitiveRealCharacter)
    (s : ℂ) (hs : 1 < s.re) : χ.L (conj s) = conj (χ.L s) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  change DirichletCharacter.LFunction χ.complexCharacter (conj s) =
    conj (DirichletCharacter.LFunction χ.complexCharacter s)
  rw [χ.complexCharacter.LFunction_eq_LSeries (by simpa using hs),
    χ.complexCharacter.LFunction_eq_LSeries hs]
  change (∑' n, LSeries.term _ (conj s) n) = conj (∑' n, LSeries.term _ s n)
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have ha : (n : ℂ).arg ≠ Real.pi := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) from rfl,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    rw [Complex.cpow_conj _ _ ha]
    simp [PrimitiveRealCharacter.complexCharacter]

theorem PrimitiveRealCharacter.L_conj (χ : PrimitiveRealCharacter) (s : ℂ) :
    χ.L (conj s) = conj (χ.L s) := by
  let g : ℂ → ℂ := conj ∘ χ.L ∘ conj
  have hd : Differentiable ℂ g := by
    intro z
    have hh := (χ.asComplex.L_analytic (conj z)).differentiableAt
    rw [PrimitiveRealCharacter.asComplex_L] at hh
    simpa only [g, Complex.conj_conj] using hh.conj_conj
  have hg : AnalyticOnNhd ℂ g univ := hd.differentiableOn.analyticOnNhd isOpen_univ
  have hf : AnalyticOnNhd ℂ χ.L univ := fun z _ => χ.asComplex.L_analytic z
  have he : g =ᶠ[𝓝 (2 : ℂ)] χ.L := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    simp only [g, Function.comp_apply, χ.L_conj_right z hz, Complex.conj_conj]
  have heq : g = χ.L := hg.eq_of_eventuallyEq hf he
  have hh := congrFun heq s
  change conj (χ.L (conj s)) = χ.L s at hh
  simpa using congrArg conj hh

theorem actualCharacterZeros_complete (χ : PrimitiveComplexCharacter) (z : ℂ)
    (hz : z ∈ complexCharacterZeros χ) : ∃ i, (actualCharacterZeros χ).zeros i = z := by
  have hp : 0 < analyticOrderNatAt χ.L z := by
    have h := (characterZeroOrder_pos_iff χ z).mpr hz.2.2
    rwa [characterZeroOrder_eq_nat, Int.natCast_pos] at h
  let c : CharacterZeroCopy χ := ⟨(z, 0), hz, hp⟩
  refine ⟨(faithfulCharacterZeroEquiv χ).symm c, ?_⟩
  change ((faithfulCharacterZeroEquiv χ) ((faithfulCharacterZeroEquiv χ).symm c)).val.1 = z
  simp [c]

theorem realCharacterActualZeros_conjugate (χ : PrimitiveRealCharacter) (i : ℕ) :
    ∃ j, (realCharacterActualZeros χ).zeros j = conj ((realCharacterActualZeros χ).zeros i) := by
  apply actualCharacterZeros_complete χ.asComplex
  have hi := (realCharacterActualZeros χ).in_strip i
  refine ⟨by simpa using hi.1, by simpa using hi.2, ?_⟩
  change χ.L (conj ((realCharacterActualZeros χ).zeros i)) = 0
  have hz := (realCharacterActualZeros χ).actual_zero i
  change χ.L _ = 0 at hz
  rw [χ.L_conj, hz, map_zero]

end Ostmann

end OAI
