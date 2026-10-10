import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceData
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries Filter
open scoped BigOperators

lemma prime_double_exp_lower {p : ℕ} (hp : p.Prime) {a : ℝ}
    (ha : a ≤ Real.log (Real.log p)) : Real.exp (Real.exp a) ≤ (p:ℝ) := by
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have he := Real.exp_le_exp.mpr ha
  rw [Real.exp_log hlog] at he
  have hh := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log hp0] using hh

lemma source_prime_lower {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (loc : SourceLocations E L k α β ρ γ c₀)
    (hE : ∀ p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p))
    {p : PrimeUpTo loc.Q} (hp : p∈loc.primes) :
    Real.exp (Real.exp (α*L)) ≤ (p.val:ℝ) :=
  prime_double_exp_lower (hE p.val (mem_boundedPrimeSet.mp hp)).1
    (hE p.val (mem_boundedPrimeSet.mp hp)).2

lemma source_endpoints_in_unit_window {d : Decomposition} {E : Finset ℕ} {δ L : ℝ}
    {k : ℕ} {α β ρ γ c₀ : ℝ} (s : SelectedWordSource d E δ L k α β ρ γ c₀)
    (hX : 0 < (s.locations.X:ℝ)) {n : ℤ} (hn : n∈s.endpoints) :
    |(n:ℝ)/(s.locations.X:ℝ)| ≤ 1 := by
  obtain ⟨a,ha,rfl⟩ := s.window n hn
  have hbound : (a:ℝ) ≤ s.locations.X := by exact_mod_cast (mem_upperWindow.mp ha).2.1
  rw [Int.cast_natCast,abs_of_nonneg (by positivity)]
  exact (div_le_one hX).mpr hbound

lemma primeShellMass_mono {Q : ℕ} {E F : Finset (PrimeUpTo Q)} (h : E⊆F) :
    primeShellMass E ≤ primeShellMass F :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun p _ _=>by positivity)

lemma source_prime_mass_le {E : Finset ℕ} {Q : ℕ} :
    primeShellMass (boundedPrimeSet Q E) ≤ harmonicPrimeMass E := by
  rw [← naturalPrimeSet_mass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact mem_boundedPrimeSet.mp hq
  · intro p _ _
    positivity

theorem source_union_mass_bound : ∃ DH : ℝ,0 < DH ∧
    ∀ {Q b : ℕ} (E : Finset ℕ) (a B : ℝ),0 < a → a ≤ B →
      (∀ p∈E,p.Prime ∧ a ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ B) →
      ∀ G : Fin b → Finset (PrimeUpTo Q),(∀ i,G i⊆boundedPrimeSet Q E) →
      primeShellMass (Finset.univ.biUnion G) ≤ B+DH := by
  classical
  obtain ⟨DH,hDH,hbound⟩ := harmonicIntervalMass_mertens
  refine ⟨DH,hDH,?_⟩
  intro Q b E a B ha haB hE G hG
  have hm : harmonicPrimeMass E ≤ B+DH := by
    rw [← harmonicIntervalMass_eq_of_support E 0 B
      (fun p hp=>⟨ha.trans_le (hE p hp).2.1,(hE p hp).2.2⟩)]
    simpa only [sub_zero] using hbound E (fun p hp=>(hE p hp).1) 0 B le_rfl (ha.le.trans haB)
  apply (primeShellMass_mono (F:=boundedPrimeSet Q E) ?_).trans (source_prime_mass_le.trans hm)
  intro p hp
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  exact hG i hi

lemma source_base_mass {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}
    (loc : SourceLocations E L k α β ρ γ c₀) (hu : 0 ≤ loc.u)
    (hγL : 0 ≤ γ*L) (hprime : ∀ p∈E,p.Prime)
    (hcut : ∀ p : ℕ,Real.log p ≤ Real.log (loc.X:ℝ)/4 → p≤loc.Q) :
    (ρ*L ≤ primeShellMass (loc.base 0)) ∧
      (c₀ ≤ primeShellMass (loc.base 1)) ∧ (c₀ ≤ primeShellMass (loc.base 2)) := by
  have hbulk : loc.B+loc.w ≤ loc.u+1 := by linarith [loc.bulk_gap]
  have hsmall : loc.s+1 ≤ loc.u+1 := by linarith [loc.small_gap]
  have hb := higherSource_interval_mass hu E hprime hcut loc.B (loc.B+loc.w) hbulk
  have hs := higherSource_interval_mass hu E hprime hcut loc.s (loc.s+1) hsmall
  have ht := higherSource_interval_mass hu E hprime hcut loc.u (loc.u+1) le_rfl
  refine ⟨?_,?_,?_⟩
  · change ρ*L ≤ primeShellMass (boundedInterval loc.primes loc.B (loc.B+loc.w))
    simpa only [SourceLocations.primes,SourceLocations.Q,SourceLocations.X,hb] using loc.bulk_mass
  · change c₀ ≤ primeShellMass (boundedInterval loc.primes loc.s (loc.s+1))
    simpa only [SourceLocations.primes,SourceLocations.Q,SourceLocations.X,hs] using loc.small_mass
  · change c₀ ≤ primeShellMass (boundedInterval loc.primes loc.u (loc.u+1))
    simpa only [SourceLocations.primes,SourceLocations.Q,SourceLocations.X,ht] using loc.top_mass

end Ostmann.Characters.HigherBiasSource

end

end OAI
