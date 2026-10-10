import OAI.NumberTheory.DirichletL.Reflection.RetainedWidth
import OAI.NumberTheory.DirichletL.Reflection.ShellDomains
import OAI.NumberTheory.DirichletL.Reflection.Surviving

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

theorem actual_surviving_retained_gates
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ→ℕ) (A : Ideal Eis→Ideal Eis→ℂ) (e : φ→Fin 3)
      (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches F jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))
      0≤v ∧ 0≤ell ∧ -η≤InverseTerminalWidths.ramifiedWidth Z i.1 ∧
      v+3*ell+InverseTerminalWidths.ramifiedWidth Z i.1≤
        InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
          F.ideal jF e+δ+η := by
  obtain ⟨Z₁,hZ₁,hwidth⟩ := actual_retained_width_uniform s hc kK kP 1 1 η hkK hkP (by norm_num) (by norm_num) hη
  obtain ⟨Z₂,hZ₂,hram⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨max Z₁ Z₂,lt_of_lt_of_le hZ₁ (le_max_left _ _),?_⟩
  intro φ _ F hF jF A e Z X QK QP δ i hZ hX hQK hQP hi he
  have hz1 := (le_max_left Z₁ Z₂).trans hZ
  have hz2 := (le_max_right Z₁ Z₂).trans hZ
  have hz := lt_of_lt_of_le hZ₁ hz1
  have hnorm := surviving_forced_norms F hF jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1.2,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩) e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  refine ⟨Real.logb_nonneg hz ((one_le_div (hp 1)).mpr hnorm.1),
    Real.logb_nonneg hz ((one_le_div (hp 2)).mpr hnorm.2),hram Z hz2 i.1,?_⟩
  simpa only [one_mul] using hwidth F jF e Z X QK QP δ i hz1 hX hQK hQP hi
end
end SevenEighths.InverseReflectedPhase

end OAI
