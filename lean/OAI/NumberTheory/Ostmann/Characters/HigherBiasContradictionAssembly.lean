import OAI.NumberTheory.Ostmann.Characters.HigherBiasCancellationEndpoints
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSource
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceTerminalSeparationExponent

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasContradiction
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HigherBiasSourceWord Filter DiagonalEstimate
attribute [local instance] Classical.propDecidable

theorem no_biased_mass_of_actual_cancellation (d : Decomposition) (α β mass δ : ℝ)
    (hα : 0<α) (hαβ : α<β) (hmass : 0 < mass) (hδ : 0<δ) (hδu : δ≤1)
    (hterminal : ∀ρ γ c₀ c BD : ℝ,0<ρ → 0<γ → 0<c₀ → 0<c → 1≤BD →
      ∀ᶠn : ℕ in atTop,TerminalCancellation d δ α β ρ γ c₀ c BD n)
    (hdiagonal : ∀ρ γ c₀ c BD : ℝ,0<ρ → 0<γ → 0<c₀ → 0<c → 1≤BD →
      ∀ᶠk : ℕ in atTop,DiagonalCancellation d δ α β ρ γ c₀ c BD k) :
    ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,
      (∀p∈E,p.Prime ∧ α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
      mass*L≤harmonicPrimeMass E → (∀p∈E,δ≤higherPrimeBias d p) → False := by
  obtain ⟨ρ,γ,c₀,c,BD0,hρ,hγ,hc₀,hc,hBD0,M,h,hM,Kmin,hKmin,hsource⟩ :=
    exists_actual_higher_character_sources d α β mass δ hα hαβ hmass hδ hδu
  let B0 := amplitudeRate (selectionCost β (δ/2)) (configurationLossCoefficient β)
  obtain ⟨BDdiag,hBDdiag,hdiag⟩ := exists_sourceDiagonal_assembly (δ:=δ) d (B0+2)
    hα hαβ hρ hγ hc₀ hc
  let BD := max BD0 BDdiag
  have hBDsrc : BD0≤BD := le_max_left _ _
  have hBDnum : BDdiag≤BD := le_max_right _ _
  have hBDone : 1≤BD := hBD0.trans hBDsrc
  have hBDpos : 0<BD := zero_lt_one.trans_le hBDone
  obtain ⟨Klower,hlower⟩ := exists_sourceAmplitudeSequence_lower_threshold β
  obtain ⟨Kcost,hcost⟩ := exists_sourcePivotLoss_threshold β
  obtain ⟨Kdiag,hdiag⟩ := eventually_atTop.mp (hdiag BD hBDnum)
  obtain ⟨Kterm,hterm⟩ := eventually_atTop.mp (hterminal ρ γ c₀ c BD hρ hγ hc₀ hc hBDone)
  obtain ⟨Kcancel,hcancel⟩ := eventually_atTop.mp (hdiagonal ρ γ c₀ c BD hρ hγ hc₀ hc hBDone)
  obtain ⟨Nsep,hsep⟩ := exists_sourceTerminal_separation_threshold_with_exponent
    (δ:=δ) (c₀:=c₀) (c:=c) d hα hαβ hρ hγ hBDpos (B0+2)
  obtain ⟨Kb,hKb⟩ := exists_nat_ge Kmin
  let K0 := Kb+Klower+Kcost+Kdiag+Kterm+Kcancel+Nsep+2
  have hlarge : Kb≤K0 ∧ Klower≤K0 ∧ Kcost≤K0 ∧ Kdiag≤K0 ∧
      Kterm+1≤K0 ∧ Kcancel≤K0 ∧ Nsep+1≤K0 ∧ 0<K0 := by
    dsimp only [K0]
    omega
  have hKreal : Kmin≤(K0:ℝ) := hKb.trans (by exact_mod_cast hlarge.1)
  have hki (i : Fin (h+1)) : K0≤K0*M^i.val :=
    Nat.le_mul_of_pos_right K0 (pow_pos (by omega : 0<M) _)
  have hnone (i : Fin (h+1)) :
      ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,(∀p∈E,p.Prime) →
        (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
        ∀s : SelectedWordSource d E δ L (K0*M^i.val) α β ρ γ c₀,
        ∀w : FixedConfigurationWitness s c BD,
        Real.exp (-B0*(wordSize (K0*M^i.val) L:ℝ))≤‖w.amplitude‖ → False := by
    have hkpos : 0<K0*M^i.val := hlarge.2.2.2.2.2.2.2.trans_le (hki i)
    obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    rw [heq]
    have hk : K0≤n+1 := by simpa only [heq] using hki i
    have hnterm : Kterm≤n := by omega
    have hnsep : Nsep≤n := by omega
    have hnlow : Klower≤n+1 := by omega
    have hncost : Kcost≤n+1 := by omega
    have hndiag : Kdiag≤n+1 := by omega
    have hncancel : Kcancel≤n+1 := by omega
    obtain ⟨τt,αt,hτt,hat,ht⟩ := hterm n hnterm
    obtain ⟨Kd,τd,ad,hτd,had,hd⟩ := hcancel (n+1) hncancel
    filter_upwards [hlower (n+1) hnlow BD c α B0 hBDone hc hα,
      hcost (n+1) hncost c hc,hdiag (n+1) hndiag Kd τd ad hτd had,
      hsep n hnsep τt αt hτt hat,ht,hd]
      with L hl hcL hdL huL htL hpL
    intro E hE hband s w hinitial
    have hloss (j : ℕ) (hj : j<n+1) : sourcePivotLoss β (n+1) L j≤(wordSize (n+1) L:ℝ) := by
      have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
      have hsum := Finset.single_le_sum
        (fun l (_hl : l∈Finset.range (n+1)) => add_nonneg (hcL.1 l) hlog)
        (Finset.mem_range.mpr hj)
      exact (le_add_of_nonneg_right hlog).trans (hsum.trans (hcL.2.1 (n+1) le_rfl))
    have hdiagall (j : ℕ) (hj : j<n+1) := hdL E hE hband s w j hj
      (sourceRecurrenceB w.configuration s.J (gapSchedule BD (n+1) L) c)
      (sourceRecurrenceV BD (n+1) L) (hpL E hE hband s w j hj)
      (sourcePivotLoss β (n+1) L j) (hloss j hj)
    have hlo := hl d E δ ρ γ c₀ hband s w hinitial hdiagall (n+1) le_rfl
    have hup := huL E hE hband s w
      (sourceRecurrenceB w.configuration s.J (gapSchedule BD (n+1) L) c)
      (sourceRecurrenceV BD (n+1) L) (htL E hE hband s w)
    exact (not_lt_of_ge hlo) hup
  filter_upwards [hsource BD hBDsrc K0 hKreal,Filter.eventually_all.mpr hnone] with L hs hn
  intro E hE hmassE hbias
  obtain ⟨i,s,w,hamp⟩ := hs E hE hmassE hbias
  exact hn i E (fun p hp=>(hE p hp).1) (fun p hp=>(hE p hp).2) s w hamp

end Ostmann.Characters.HigherBiasContradiction

end

end OAI
