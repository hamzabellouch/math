import OAI.NumberTheory.Ostmann.Construction.InitialEtaRepeatedCutoff
import OAI.NumberTheory.Ostmann.Construction.InitialEtaRepeatedEstimate
import OAI.NumberTheory.Ostmann.Construction.RepeatedErrorScale
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
open Filter
namespace Ostmann.Construction.InitialEta

theorem initial_repeatedContribution_error_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) (hBs : 200≤Bs) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hZ : 0<harmonicPrimeMass P),
      L/5000≤harmonicPrimeMass P →
      (∀p∈P,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℝ) ∧
        Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L)) →
      ‖repeatedContribution d C.favorable C.giant C.bulk (harmonicPrimeSource P hP hZ) C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2) C.bulkBin C.spectatorBin C.scale‖≤
        (1/2)*Real.exp (-27*(Conclusion.bulkSize k L:ℝ)) := by
  classical
  filter_upwards [initial_jointPrior_mass_bound_eventually d Bs BD Bz hk,
    initial_candidate_harmonicMass_eventually d Bs BD Bz hk,
    initial_tupleValues_min_eventually d Bs BD Bz hk,
    eventually_levelZero_window_doubleExp Bs k,
    repeated_error_scale_eventually hBs hk,eventually_gt_atTop (0:ℝ)]
    with L hmass hcommon hmin hinflation habsorb hL
  intro E C hG hGu hcl hcu hb hd P hP hZ hPH hsupport
  let spectator := harmonicPrimeSource P hP hZ
  let A : ℝ := (5000/L)^(2*Conclusion.bulkSize k L)*Real.exp (24*(Conclusion.bulkSize k L:ℝ))
  have hA : 0≤A := by dsimp only [A]; positivity
  have hX : 0<(C.scale:ℝ) := by exact_mod_cast initial_scale_pos C
  have hm := hmass E C hG hGu hcl hcu hb hd P hP hZ hPH
  have hcandidate := hcommon E C hG hGu hcl hcu hb hd spectator
    (fun p => (hsupport p p.property).2) (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)
  have hvalues := hmin E C hG hGu hcl hcu hb hd spectator (fun p => (hsupport p p.property).1)
  have hbound := repeatedContribution_bound d C.favorable C.giant C.bulk spectator C.auxiliary
    (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2) C.bulkBin C.spectatorBin
    (Δ := Conclusion.initialGap Bs k L) (W := 14+6*(k:ℝ)) hX hA hm
    (by
      intro x hmx hbx hn
      have hw := initial_tuplePeriod_log_support C spectator x hmx hbx
      apply repeated_tuple_cutoff_of_log_support (tupleValues x) (tupleValues_prime x) hn
        (Δ := Conclusion.initialGap Bs k L) (W := 14+6*(k:ℝ)) hX
        (Real.exp_pos _) (hvalues x hmx)
      · have hh := (abs_le.mp hw).2
        change Real.log (tuplePeriod x:ℝ)≤_
        linarith
      · exact hinflation)
    (by
      intro x hmx hbx
      have hh := (abs_le.mp (initial_tuplePeriod_log_support C spectator x hmx hbx)).1
      change _≤Real.log (tuplePeriod x:ℝ)
      linarith)
  have hcount : 2+2*(Conclusion.bulkSize k L/2)+2*(Conclusion.bulkSize k L/2)+2*(3+2*k)=
      2*Conclusion.bulkSize k L+4*k+8 := by
    obtain ⟨n,hn⟩ := Conclusion.bulkSize_even k L
    omega
  simp only [card_position,card_auxiliaryIndex,hcount] at hbound
  have hexp : Real.exp (harmonicPrimeMass
      (candidateValues C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)))≤Real.exp (2*L) :=
    Real.exp_le_exp.mpr hcandidate
  have hconstant : 0≤A*‖𝓕 SchwartzCutoff.psi 0‖*
      Real.exp ((-Conclusion.initialGap Bs k L+(14+6*(k:ℝ)))/2)*
      ((2*Conclusion.bulkSize k L+4*k+8:ℕ):ℝ)^(2*Conclusion.bulkSize k L+4*k+8) := by positivity
  refine (hbound.trans (mul_le_mul_of_nonneg_left hexp hconstant)).trans ?_
  rw [show (-Conclusion.initialGap Bs k L+(14+6*(k:ℝ)))/2 =
    -(Conclusion.initialGap Bs k L-(14+6*(k:ℝ)))/2 by ring]
  convert habsorb using 1; dsimp only [A]; ring

end Ostmann.Construction.InitialEta

end

end OAI
