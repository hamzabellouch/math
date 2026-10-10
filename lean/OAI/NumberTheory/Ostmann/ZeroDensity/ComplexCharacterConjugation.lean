import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterConjugateZeros

namespace OAI

/-! # Conjugation and multiplicity for general primitive character zeros -/

namespace Ostmann

open Complex Filter Set
open scoped ComplexConjugate Topology

theorem iteratedDeriv_conjugation (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedDeriv_succ, ih, deriv_conj_conj]

theorem analyticOrderAt_conjugation (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (z : ℂ) (hfinite : analyticOrderAt f (conj z) ≠ ⊤) :
    analyticOrderAt (conj ∘ f ∘ conj) z = analyticOrderAt f (conj z) := by
  have hd : Differentiable ℂ (conj ∘ f ∘ conj) := by
    intro w
    simpa only [Complex.conj_conj] using (hf (conj w)).differentiableAt.conj_conj
  have hg := hd.analyticAt z
  have hn : analyticOrderAt f (conj z) = (analyticOrderNatAt f (conj z) : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hfinite).symm
  rw [hn]
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mpr
  have hh := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hf (conj z))).mp hn
  simp only [iteratedDeriv_conjugation, Function.comp_apply]
  constructor
  · intro k hk
    rw [hh.1 k hk, map_zero]
  · intro he
    apply hh.2
    have he' := congrArg conj he
    simpa only [Complex.conj_conj, map_zero] using he'

theorem PrimitiveComplexCharacter.inverse_L_conj_right (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 1 < s.re) : χ.inverse.L (conj s) = conj (χ.L s) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  change DirichletCharacter.LFunction (χ.character⁻¹) (conj s) =
    conj (DirichletCharacter.LFunction χ.character s)
  rw [(χ.character⁻¹).LFunction_eq_LSeries (by simpa using hs), χ.character.LFunction_eq_LSeries hs]
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
    simp only [map_div₀, map_natCast, ← MulChar.star_eq_inv, MulChar.star_apply, RCLike.star_def]

theorem PrimitiveComplexCharacter.inverse_L_eq_conjugate (χ : PrimitiveComplexCharacter) :
    χ.inverse.L = conj ∘ χ.L ∘ conj := by
  have hd : Differentiable ℂ (conj ∘ χ.L ∘ conj) := by
    intro z
    simpa only [Complex.conj_conj] using (χ.L_analytic (conj z)).differentiableAt.conj_conj
  have hg := hd.differentiableOn.analyticOnNhd isOpen_univ
  have hf : AnalyticOnNhd ℂ χ.inverse.L univ := fun z _ => χ.inverse.L_analytic z
  apply hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  simpa only [Function.comp_apply, Complex.conj_conj] using
    χ.inverse_L_conj_right (conj z) (by simpa using hz)

theorem PrimitiveComplexCharacter.L_order_conjugate (χ : PrimitiveComplexCharacter) (z : ℂ) :
    analyticOrderAt χ.inverse.L (conj z) = analyticOrderAt χ.L z := by
  rw [χ.inverse_L_eq_conjugate, analyticOrderAt_conjugation χ.L χ.L_analytic]
  · simp
  · simpa using χ.L_order_ne_top z

theorem PrimitiveComplexCharacter.L_order_self_reflection (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderAt χ.L (1 - conj z) = analyticOrderAt χ.L z := by
  rw [χ.L_order_reflection (conj z) (by simpa using hz) (by simpa using hz1), χ.L_order_conjugate]

end Ostmann

end OAI
