import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries Filter

theorem bounded_rich_grid_of_natural (Q : ℕ) (E : Finset ℕ)
    (c0 U logX : ℝ) (k : ℕ) (hprime : ∀ p∈E,p.Prime)
    (hcut : ∀ p : ℕ,Real.log (p:ℝ) ≤ logX/4 → p ≤ Q)
    (hrich : ∀ v : ℝ,U ≤ v → v+(1/10000:ℝ)*k ≤ U+5*k →
      ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+(1/10000:ℝ)*k ∧
        c0 ≤ harmonicIntervalMass E (U+i) (U+i+1)) :
    ∀ v : ℝ,U ≤ v → v+(1/10000:ℝ)*k ≤ U+5*k →
      Real.exp (v+(1/10000:ℝ)*k) ≤ logX/4 →
      ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+(1/10000:ℝ)*k ∧
        c0 ≤ primeShellMass (boundedInterval (boundedPrimeSet Q E) (U+i) (U+i+1)) := by
  intro v hv hvend hvc
  obtain ⟨i,hil,hih,him⟩ := hrich v hv hvend
  refine ⟨i,hil,hih,?_⟩
  rw [boundedInterval_mass_of_cutoff Q E (U+i) (U+i+1) hprime (by
    intro p hp _ hphi
    apply hcut
    have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (hprime p hp).one_lt)
    have hh := Real.exp_le_exp.mpr (hphi.trans hih)
    rw [Real.exp_log hlog] at hh
    exact hh.trans hvc)]
  exact him

theorem eventually_source_locations_rich (k : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,∀ (E : Finset ℕ) (β ρ γ c0 : ℝ)
      (s : SourceLocations E L k α β ρ γ c0), (∀ p∈E,p.Prime) →
      ∀ v : ℝ,s.U ≤ v → v+(1/10000:ℝ)*k ≤ s.U+5*k →
        Real.exp (v+(1/10000:ℝ)*k) ≤ Real.log s.X/4 →
        ∃ i : ℕ,v ≤ s.U+(i:ℝ) ∧ s.U+(i:ℝ)+1 ≤ v+(1/10000:ℝ)*k ∧
          c0 ≤ primeShellMass (boundedInterval s.primes (s.U+i) (s.U+i+1)) := by
  filter_upwards [eventually_higherSource_collisionScale10 k α hα] with L hL
  intro E β ρ γ c0 s hprime
  exact bounded_rich_grid_of_natural s.Q E c0 s.U (Real.log s.X) k hprime
    (hL s.u s.top_lower) (by simpa only [higherSourceEpsilon] using s.rich)

theorem small_shell_lower_of_mass (E : Finset ℕ) (a s : ℝ)
    (hband : ∀ p∈E,a ≤ Real.log (Real.log p))
    (hm : 0 < harmonicIntervalMass E s (s+1)) : a-1 ≤ s := by
  classical
  have hf : (E.filter (fun p : ℕ => s < Real.log (Real.log p) ∧
      Real.log (Real.log p) ≤ s+1)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [harmonicIntervalMass,harmonicPrimeMass,he,Finset.sum_empty] at hm
    exact lt_irrefl _ hm
  obtain ⟨p,hp⟩ := hf
  obtain ⟨hp,_,hu⟩ := Finset.mem_filter.mp hp
  have hl := hband p hp
  linarith

theorem eventually_source_locations_above (k : ℕ) (α c0 aMin : ℝ)
    (hα : 0 < α) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop,∀ (E : Finset ℕ) (β ρ γ : ℝ)
      (s : SourceLocations E L k α β ρ γ c0),
      (∀ p∈E,α*L ≤ Real.log (Real.log p)) → aMin ≤ s.s ∧ aMin ≤ s.U := by
  filter_upwards [(Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop
    (aMin+1+(1/10000:ℝ)*k)] with L hL
  intro E β ρ γ s hband
  change aMin+1+(1/10000:ℝ)*k ≤ α*L at hL
  have hs := small_shell_lower_of_mass E (α*L) s.s hband (hc0.trans_le s.small_mass)
  have htop := s.top_end
  simp only [higherSourceEpsilon] at htop
  have hlower := s.top_lower
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem eventually_source_locations_anchor_mass (k : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,∀ (E : Finset ℕ) (β ρ γ c0 : ℝ)
      (s : SourceLocations E L k α β ρ γ c0), (∀ p∈E,p.Prime) → 0 ≤ γ →
        c0 ≤ primeShellMass (s.base 1) ∧ c0 ≤ primeShellMass (s.base 2) := by
  filter_upwards [eventually_higherSource_collisionScale10 k α hα,
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (0:ℝ)] with L hcut hlarge hL
  intro E β ρ γ c0 s hprime hγ
  change 1 ≤ α*L at hlarge
  have hu : 0 ≤ s.u := by have hh := s.top_lower; linarith
  have hsmall : s.s+1 ≤ s.u+1 := by
    have hh := s.small_gap
    nlinarith [mul_nonneg hγ hL]
  have hs := higherSource_interval_mass hu E hprime (hcut s.u s.top_lower)
    s.s (s.s+1) hsmall
  have ht := higherSource_interval_mass hu E hprime (hcut s.u s.top_lower)
    s.u (s.u+1) le_rfl
  change c0 ≤ primeShellMass (boundedInterval s.primes s.s (s.s+1)) ∧
    c0 ≤ primeShellMass (boundedInterval s.primes s.u (s.u+1))
  dsimp only [SourceLocations.primes,SourceLocations.Q,SourceLocations.X]
  constructor
  · rw [hs]
    exact s.small_mass
  · rw [ht]
    exact s.top_mass

end Ostmann.Characters.HigherBiasSource

end

end OAI
