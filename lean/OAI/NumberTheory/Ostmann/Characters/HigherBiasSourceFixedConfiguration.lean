import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationCost
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationIdentity
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationPointwise
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetCellsLocations

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries HigherBiasSourceWord InitialCharacterScale Filter

theorem exists_actual_fixed_configurations (δ c0 : ℝ) (hδ : 0 < δ) (hc0 : 0 < c0) :
    ∃ c : ℝ,0 < c ∧ ∃ K : ℕ,∀ k : ℕ,K ≤ k →
    ∀ α β ρ γ BD : ℝ,0 < α → 0 ≤ γ → 1 ≤ BD →
    ∀ᶠ L : ℝ in atTop,∀ (d : Decomposition) (E : Finset ℕ)
      (s : SelectedWordSource d E δ L k α β ρ γ c0),
      (∀ p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∃ cfg : SourceConfiguration k,∃ H : Finset ℤ,
        cfg.Bounded ⌊Real.exp (β*L)⌋₊ (configurationListLengthBound k) ∧
        H ⊆ s.endpoints ∧ ConfigurationGeometry s c BD cfg ∧
        (∀ n∈H,ConfigurationGoodAt s c cfg n) ∧
        Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ) -
          configurationLossCoefficient β*maxCells 4 k*L) ≤
          (H.card:ℝ)/Real.sqrt s.locations.X := by
  classical
  obtain ⟨c,aMin,hc,hproducer,K,hactual⟩ := exists_actual_good_target_cells c0 δ hc0 hδ
  refine ⟨c,hc,K,?_⟩
  intro k hk α β ρ γ BD hα hγ hBD
  filter_upwards [eventually_source_locations_rich k α hα,
    eventually_source_locations_above k α c0 aMin hα hc0,
    eventually_source_locations_anchor_mass k α hα,
    eventually_gapSchedule_le_exp k hBD hα,
    eventually_fixed_source_configuration_retained β,
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (0:ℝ)] with L hrich habove hmass hgap hfreeze hlarge hL
  intro d E s hE
  change 1 ≤ α*L at hlarge
  have hu0 : 0 ≤ s.locations.u := by have hh := s.locations.top_lower; linarith
  have hsu : s.locations.s+1 ≤ s.locations.u := by
    have hh := s.locations.small_gap
    nlinarith [mul_nonneg hγ hL]
  have hmin := habove E β ρ γ s.locations (fun p hp => (hE p hp).2.1)
  have hmass' := hmass E β ρ γ c0 s.locations (fun p hp => (hE p hp).1) hγ
  have hX := higherSourceX_log_bounds k s.locations.u hu0
  have hXu : 0 < (s.locations.X:ℝ) := by
    have hn : 0 < s.locations.X := lt_of_lt_of_le Nat.zero_lt_one hX.1
    exact_mod_cast hn
  have huupper : s.locations.u ≤ s.locations.U+2*(1/10000:ℝ)*k := by
    have hh := s.locations.top_end
    simp only [higherSourceEpsilon] at hh
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  have hpoint (n : ℤ) (hn : n∈s.endpoints) :
      ∃ cfg : SourceConfiguration k,ConfigurationGeometry s c BD cfg ∧ ConfigurationGoodAt s c cfg n := by
    apply exists_configuration_at_endpoint s hc hc0 hproducer (fun p hp => (hE p hp).2.2)
      hmin.1 (hmin.2.trans s.locations.top_start) hsu hu0 hmass'.1 hmass'.2
      (hgap s.locations.u s.locations.top_lower) hn
    intro T hTlo hThi
    obtain ⟨a,l,hUa,_,_,hcell,herr,hlenlo,hlenhi⟩ := hactual k hk d s.locations.Q
      s.locations.primes s.family s.locations.base s.locations.U s.locations.u T
      (Real.log s.locations.X) n hmin.2 s.locations.top_start huupper hTlo hThi hX.2.1
      (hrich E β ρ γ c0 s.locations (fun p hp => (hE p hp).1))
      s.test_mass_pos (s.shell_means n hn)
    exact ⟨l,⟨a,hUa,hcell⟩,herr,hlenlo,hlenhi⟩
  have hchoice (n : ℤ) : ∃ cfg : SourceConfiguration k,
      n∈s.endpoints → ConfigurationGeometry s c BD cfg ∧ ConfigurationGoodAt s c cfg n := by
    by_cases hn : n∈s.endpoints
    · obtain ⟨cfg,hg⟩ := hpoint n hn
      exact ⟨cfg,fun _ => hg⟩
    · exact ⟨(fun _ => 0,fun _ => []),fun hh => (hn hh).elim⟩
  choose f hf using hchoice
  have hfbound (n : ℤ) (hn : n∈s.endpoints) :
      (f n).Bounded ⌊Real.exp (β*L)⌋₊ (configurationListLengthBound k) := by
    have hh := configuration_bounded_of_good (hf n hn).2 (hf n hn).1
    simpa only [configurationListLengthBound,
      show 2*((1/10000:ℝ)*k)=2*(k:ℝ)/10000 by ring] using hh
  obtain ⟨cfg,H,hbounded,hsub,heq,hcard⟩ := hfreeze k s.endpoints f hfbound
    (s.locations.X:ℝ) (selectionCost β (δ/2)) (wordSize k L:ℝ) hXu s.cardinal
  have hH : H.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [he,Finset.card_empty,Nat.cast_zero,zero_div] at hcard
    exact (not_le_of_gt (Real.exp_pos _)) hcard
  obtain ⟨n,hn⟩ := hH
  have hgeom : ConfigurationGeometry s c BD cfg := by
    rw [←heq n hn]
    exact (hf n (hsub hn)).1
  refine ⟨cfg,H,hbounded,hsub,hgeom,?_,hcard⟩
  intro m hm
  rw [←heq m hm]
  exact (hf m (hsub hm)).2

end Ostmann.Characters.HigherBiasSource

end

end OAI
