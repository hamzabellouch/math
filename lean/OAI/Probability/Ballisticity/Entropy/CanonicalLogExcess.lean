import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def canonicalLogExcess {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2))).toReal

lemma measurable_canonicalLogExcess {Ω : Type*} [MeasurableSpace Ω]
    (A : ℝ) (p : ℕ → Ω → ℝ) (hp : ∀ n, Measurable (p n)) :
    Measurable (canonicalLogExcess A p) := by
  unfold canonicalLogExcess
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro n
  exact ((hp n).log.neg.sub_const _).ennreal_ofReal

lemma canonicalLogExcess_nonneg {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) :
    0 ≤ canonicalLogExcess A p ω := ENNReal.toReal_nonneg

lemma canonicalLogExcess_bounds {Ω : Type*} {A D W : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hW : 0 ≤ W) (p : ℕ → Ω → ℝ) (ω : Ω)
    (hp : ∀ n, -Real.log (p n ω) ≤ A*Real.log ((n:ℝ)+2)+D*(W+1)) :
    canonicalLogExcess A p ω ≤ D*(W+1) ∧
    (∀ n, -Real.log (p n ω) ≤ 2*A*Real.log ((n:ℝ)+2)+canonicalLogExcess A p ω) := by
  let S := ⨆ n : ℕ, ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2))
  have hS : S ≤ ENNReal.ofReal (D*(W+1)) := by
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    have hn := hp n
    have hl : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    have hm : 0 ≤ A*Real.log ((n:ℝ)+2) := mul_nonneg hA hl
    linarith
  have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS
  constructor
  · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hS
    simpa only [canonicalLogExcess,S,ENNReal.toReal_ofReal (show 0 ≤ D*(W+1) by positivity)] using hh
  · intro n
    have hn : ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2)) ≤ S := le_iSup (fun k : ℕ => ENNReal.ofReal (-Real.log (p k ω)-2*A*Real.log ((k:ℝ)+2))) n
    have hr := (ENNReal.ofReal_le_iff_le_toReal hSt).mp hn
    change -Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2) ≤ canonicalLogExcess A p ω at hr
    linarith

noncomputable def finiteLogExcess {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (⨆ n : Fin (N+1), ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2))).toReal

lemma canonicalLogExcess_eq_finite {Ω : Type*} {A D W M : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hWM : W ≤ M) (p : ℕ → Ω → ℝ) (ω : Ω)
    (hp : ∀ n, -Real.log (p n ω) ≤ A*Real.log ((n:ℝ)+2)+D*(W+1))
    (N : ℕ) (hN : D*(M+1) ≤ A*Real.log ((N:ℝ)+2)) :
    canonicalLogExcess A p ω = finiteLogExcess A p N ω := by
  unfold canonicalLogExcess finiteLogExcess
  congr 1
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : n ≤ N
    · exact le_iSup (fun k : Fin (N+1) => ENNReal.ofReal (-Real.log (p k ω)-2*A*Real.log ((k:ℝ)+2))) ⟨n,by omega⟩
    · have hlog : Real.log ((N:ℝ)+2) ≤ Real.log ((n:ℝ)+2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show N+2 ≤ n+2 by omega))
      have hAl := mul_le_mul_of_nonneg_left hlog hA
      have hDW := mul_le_mul_of_nonneg_left (add_le_add_right hWM 1) hD
      have hp' := hp n
      have hzero : -Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2) ≤ 0 := by linarith
      rw [ENNReal.ofReal_eq_zero.mpr hzero]
      exact zero_le
  · apply iSup_le
    intro n
    exact le_iSup (fun k : ℕ => ENNReal.ofReal (-Real.log (p k ω)-2*A*Real.log ((k:ℝ)+2))) n.val
end DirectionalTransience

end

end

end OAI
