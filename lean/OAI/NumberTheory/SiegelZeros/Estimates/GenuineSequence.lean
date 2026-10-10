import Mathlib.Data.PNat.Basic
import OAI.NumberTheory.SiegelZeros.Characters.BoundedConductor
import OAI.NumberTheory.SiegelZeros.Model

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W02

structure GenuineZero where
  q : ℕ+
  q_ge_three : 3 ≤ (q : ℕ)
  χ : DirichletCharacter ℂ (q : ℕ)
  primitive : χ.IsPrimitive
  nonprincipal : χ ≠ 1
  real_character : ∀ a : ZMod (q : ℕ), (χ a).im = 0
  β : ℝ
  beta_pos : 0 < β
  beta_lt_one : β < 1
  zero : χ.LFunction (β : ℂ) = 0

noncomputable def GenuineZero.gap (z : GenuineZero) : ℝ :=
  (1 - z.β) * Real.log (z.q : ℝ)

theorem genuine_contrary_sequence (failure : ¬ UniformSiegelZeroExclusion) :
    ∃ z : ℕ → GenuineZero,
      (∀ n, n < ((z n).q : ℕ)) ∧
      (∀ n, 0 < (z n).gap ∧ (z n).gap < 1 / ((n : ℝ) + 1)) ∧
      Filter.Tendsto (fun n ↦ ((z n).q : ℕ)) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n ↦ (z n).gap) Filter.atTop (nhds 0) := by
  have hfailure : ¬ ∃ c : ℝ, 0 < c ∧ ∀ z : GenuineZero, True → c ≤ z.gap := by
    rintro ⟨c, hc, hall⟩
    apply failure
    refine ⟨c, hc, ?_⟩
    intro q hzero hq χ hprim hnon hreal β hpos hlt hz
    exact hall {
      q := ⟨q, by omega⟩
      q_ge_three := hq
      χ := χ
      primitive := hprim
      nonprincipal := hnon
      real_character := hreal
      β := β
      beta_pos := hpos
      beta_lt_one := hlt
      zero := hz } trivial
  have hpos : ∀ z : GenuineZero, True → 0 < z.gap := by
    intro z _
    apply mul_pos (sub_pos.mpr z.beta_lt_one)
    apply Real.log_pos
    exact_mod_cast (show 1 < (z.q : ℕ) by have := z.q_ge_three; omega)
  have hbounded : ∀ Q : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ z : GenuineZero, True → (z.q : ℕ) ≤ Q → c ≤ z.gap := by
    intro Q
    obtain ⟨c, hc, hbound⟩ := bounded_conductor_zero_gap Q
    refine ⟨c, hc, ?_⟩
    intro z _ hle
    exact hbound z.q z.q_ge_three hle z.χ z.nonprincipal z.β z.beta_lt_one z.zero
  obtain ⟨z, _, hcond, hsmall, hq, hgap⟩ :=
    exists_contrary_sequence (fun _ : GenuineZero ↦ True)
      (fun z ↦ (z.q : ℕ)) GenuineZero.gap hpos hbounded hfailure
  exact ⟨z, hcond, hsmall, hq, hgap⟩

end WeightedTorusJets.W02

end

end SiegelZeros

end OAI
