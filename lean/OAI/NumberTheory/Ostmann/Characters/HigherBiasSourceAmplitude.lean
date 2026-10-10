import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitudeData
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationIdentity
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter
open scoped BigOperators

theorem eventually_fixedConfiguration_amplitude (d : Decomposition)
    {α β ρ γ c₀ c δ : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c)
    (hδ : 0 < δ) (hδu : δ ≤ 1) :
    ∀ᶠ k : ℕ in atTop,∀ BD : ℝ,
      gapThreshold (positiveRate (selectionCost β (δ/2)) (configurationLossCoefficient β))
        ρ (2*(β+1)) β ≤ BD →
      ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,
      (∀ p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀ s : SelectedWordSource d E δ L k α β ρ γ c₀,
      ∀ w : FixedConfigurationWitness s c BD,
      Real.exp (-amplitudeRate (selectionCost β (δ/2)) (configurationLossCoefficient β)*
        (wordSize k L:ℝ)) ≤ ‖w.amplitude‖ := by
  classical
  obtain ⟨DH,hDH,hunion⟩ := source_union_mass_bound
  have hβ : 0 < β := hα.trans hαβ
  have hδ4 : 0 < δ/4 := by positivity
  have hδ4u : δ/4 ≤ 1 := by linarith
  have hCI := (configurationLossCoefficient_pos β).le
  have hmain := initial_amplitude_exponential_at_actual_scales hρ hc₀
    (show 0 ≤ β+1 by linarith) hβ.le hδ4 hδ4u hCI
    (show (0:ℝ) ≤ 4 by norm_num) hα (selectionCost β (δ/2))
  filter_upwards [hmain] with k hk
  intro BD hBD
  have hnum : ∀ᶠ L : ℝ in atTop,1 ≤ α*L :=
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  filter_upwards [hk BD hBD 0 (configurationProductWidth k c) DH,
    eventually_higherSource_collisionScale10 k α hα,hnum,
    eventually_gt_atTop (0:ℝ),eventually_ge_atTop (-Real.log c)]
    with L hA hcut hnum hL hLc
  intro E hE s w
  have hu : 0 ≤ s.locations.u := by linarith [s.locations.top_lower]
  have hX : 0 < (s.locations.X:ℝ) := by
    have hh := (higherSourceX_log_bounds k s.locations.u hu).1
    exact_mod_cast (show 0 < s.locations.X by exact Nat.lt_of_lt_of_le Nat.zero_lt_one hh)
  have hnc : (configCellCount w.configuration:ℝ) ≤ maxCells 4 k := by
    have hh := configCellCount_le w.configuration (by
      intro j
      simpa only [show 2*((1/10000:ℝ)*k)=2*(k:ℝ)/10000 by ring] using w.geometry.length_upper j)
    simpa only [maxCells,show (2/10000:ℝ)*k=2*(k:ℝ)/10000 by ring] using hh
  have hsource := source_base_mass s.locations hu (mul_nonneg hγ.le hL.le)
    (fun p hp=>(hE p hp).1) (hcut s.locations.u s.locations.top_lower)
  have hroles : ∀ i,w.roles i⊆s.locations.primes := w.roles_subset
  have hχ : ∀ i,∀ p∈w.roles i,familyCharacter s.family p.val≠1 := by
    intro i p hp
    exact s.family.characterNat_nonprincipal (hroles i hp)
  have hz : ∀ i,∀ p∈w.roles i,‖familyPhase s.family p.val‖≤1 :=
    fun _ p _=>(familyPhase_norm s.family p.val).le
  have hNorm : (∏ i,(primeShellMass (w.roles i))⁻¹) ≤
      (1/(ρ*L))^(wordSize k L)/c₀*Real.exp ((β+1)*maxCells 4 k*L) := by
    obtain ⟨n,hn⟩ := w.nonempty
    have hcMass : ∀ i,c/Real.exp (β*L) ≤ primeShellMass (w.cells i) :=
      fun i=>(w.good n hn i).2.2.1
    have hh := halfRole_normalization_le (s.locations.base 0) (s.locations.base 2)
      (wordSize k L) w.cells (fun _=>β*L) (mul_pos hρ hL) hc₀ hc
      hsource.1 hsource.2.2 hcMass (fun _=>le_rfl) hLc
    change (∏ i,(primeShellMass (w.roles i))⁻¹) ≤ _ at hh
    apply hh.trans
    simp only [one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnc (by linarith)) hL.le
  have hUnion : primeShellMass (Finset.univ.biUnion w.roles) ≤ β*L+DH :=
    hunion E (α*L) (β*L) (mul_pos hα hL)
      (mul_le_mul_of_nonneg_right hαβ.le hL.le) hE w.roles hroles
  have hmin : ∀ i,∀ p∈w.roles i,Real.exp (Real.exp (α*L)) ≤ (p.val:ℝ) := by
    intro i p hp
    exact source_prime_lower s.locations (fun p hp=>⟨(hE p hp).1,(hE p hp).2.1⟩) (hroles i hp)
  have hwindow : ∀ q : Fin (((wordSize k L+1)+configCellCount w.configuration)+
      ((wordSize k L+1)+configCellCount w.configuration))→PrimeUpTo s.locations.Q,
      (∀ i,q i∈characterDoubleShell w.roles i) →
      characterDoubleMask (sourceHalfMask s.J) q≠0 →
      (s.locations.X:ℝ)*Real.exp (initialGap BD k L-configurationProductWidth k c) ≤
        (characterTupleProduct q:ℝ) ∧ (characterTupleProduct q:ℝ) ≤
        (s.locations.X:ℝ)*Real.exp (initialGap BD k L+configurationProductWidth k c) := by
    intro q hq hmask
    apply source_doubled_product_window (s.locations.base 0) (s.locations.base 2)
      s.locations.primes w.configuration w.roles_pos s.J
      (configurationTarget (Real.log s.locations.X) s.J (gapSchedule BD k L) w.configuration)
      hX w.geometry.target_error ?_ ?_ q hq hmask
    · simpa only [gapSchedule_zero] using configuration_targets_total_identity
        (Real.log s.locations.X) s.J (gapSchedule BD k L) w.configuration
    · intro j
      simpa only [show 2*((1/10000:ℝ)*k)=2*(k:ℝ)/10000 by ring] using w.geometry.length_upper j
  exact hA s.locations.Q ((wordSize k L+1)+configCellCount w.configuration)
    (configCellCount w.configuration) hnc rfl w.roles w.roles_pos
    (fun _=>familyCharacter s.family) (fun _=>familyCenter s.family) (fun _=>familyPhase s.family)
    hχ hz (sourceHalfMask s.J) (sourceHalfMask_bounds s.J) w.endpoints s.locations.X hX
    (fun n hn=>source_endpoints_in_unit_window s hX (w.subset hn))
    (w.endpoint_mean hδ.le) (by simpa only [sub_zero] using w.population) hNorm hUnion hmin hwindow

end Ostmann.Characters.HigherBiasSource

end

end OAI
