import Mathlib
import OAI.Computability.QuantumFactoring.SamplerLabels
import OAI.Computability.QuantumFactoring.TrialRawPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness

noncomputable def recovered {w s : ℕ} (a m : Basis w) (n d j : ℕ)
    (x : Basis (OrderSample.width w (s+2))) : Prop :=
  SampleSelected a m x ∧
    scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY x)) (2*(s+3)+1)=(d,j)

noncomputable def modeFirst {w : ℕ} (s n : ℕ) (a m : Basis w) (d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat<2 ∧ recovered a m n d j x.2.1 ∧ firstPass n d j x.2.2
noncomputable def modeSecond {w : ℕ} (s n d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat=2 ∧ secondPass n d j x.2.2
noncomputable def modeThird {w : ℕ} (s n d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat=3 ∧ thirdPass n d j x.2.2

noncomputable def labelEvent {w : ℕ} (s n : ℕ) (a m : Basis w) (d j : ℕ) (x : Raw w s n) : Prop :=
  modeFirst s n a m d j x ∨ modeSecond s n d j x ∨ modeThird s n d j x

lemma phaseScale_bounds {n s : ℕ} (_hn : 1≤n) (hs : 2^(s+2)=(2^n)^16) :
    (2^n)^2≤2^(s+2) ∧ 2^(s+2)<2^(s+3) := by
  constructor
  · rw [hs]
    exact Nat.pow_le_pow_right (by positivity) (by decide)
  · exact Nat.pow_lt_pow_right (by decide) (by omega)

lemma first_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    outcomeMass (modeFirst s n a m (orderOf u) j) (rawState s n a m)=
      firstModeMass n ((2^n)^16) (2^n) (orderOf u) j := by
  have hd : 0<orderOf u := orderOf_pos u
  have hsamp := sampler_recovered_label_mass (b:=s) (s:=s+3) a m hm u ha
    (phaseScale_bounds hn hs).1 (phaseScale_bounds hn hs).2 hdB j hj hcop
  have hsmass : outcomeMass (recovered (s:=s) a m n (orderOf u) j) (samplerState (s:=s) a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(s+2)) (orderOf u) j t.val := hsamp
  unfold modeFirst rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat<2)
      (fun x => recovered a m n (orderOf u) j x.1 ∧ firstPass n (orderOf u) j x.2),
    fair_threshold_mass (by decide : 2≤2^2),
    independent_mass (samplerState (s:=s) a m) (guessState n) (recovered a m n (orderOf u) j) (firstPass n (orderOf u) j),
    firstPass_mass hn hd hdB j]
  rw [hsmass,Fin.sum_univ_eq_sum_range,hs]
  unfold firstModeMass firstRetention
  norm_num
  ring

lemma second_mass {w n s : ℕ} (hn : 1≤n) (a m : Basis w)
    {d : ℕ} (hd : 0<d) (hdB : d<2^n) (j : ℕ) (hj : j<d) :
    outcomeMass (modeSecond (w:=w) s n d j) (rawState s n a m)=
      secondModeMass n ((2^n)^16) (2^n) d j := by
  unfold modeSecond rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat=2) (fun x => secondPass n d j x.2),
    fair_value_mass (by decide : 2<2^2),
    independent_mass_right (samplerState (s:=s) a m) (guessState n) (secondPass n d j)
      (basis_preparation_normalized (OrderSample.completeSampler w s) _),
    secondPass_mass hn hd hdB j hj]
  unfold secondModeMass
  rw [Finset.mul_sum]
  simp only [discrepancyRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_sub,
    residueProbabilityRat_cast (by positivity : 0<(2^n)^16),Nat.cast_pow,Nat.cast_ofNat]
  norm_num

lemma third_mass {w n s : ℕ} (hn : 1≤n) (a m : Basis w)
    {d : ℕ} (hd : 0<d) (hdB : d<2^n) (j : ℕ) (hj : j<d) :
    outcomeMass (modeThird (w:=w) s n d j) (rawState s n a m)=
      thirdModeMass n ((2^n)^16) (2^n) d j := by
  unfold modeThird rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat=3) (fun x => thirdPass n d j x.2),
    fair_value_mass (by decide : 3<2^2),
    independent_mass_right (samplerState (s:=s) a m) (guessState n) (thirdPass n d j)
      (basis_preparation_normalized (OrderSample.completeSampler w s) _),
    thirdPass_mass hn hd hdB j hj]
  simp only [thirdModeMass,remainderRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Nat.cast_pow,Nat.cast_ofNat]
  norm_num
  ring

/-- True-order cancellation for the ACTUAL physical finite-gate experiment,
with all unselected sampler amplitudes, guesses, and retention coins retained. -/
theorem labelEvent_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    outcomeMass (labelEvent s n a m (orderOf u) j) (rawState s n a m)=
      (prescribedMass (orderOf u):ℝ) := by
  have hd : 0<orderOf u := orderOf_pos u
  unfold labelEvent
  rw [outcomeMass_disjoint_or _ _ _ (by
    intro x h
    rcases h with ⟨h0,h1|h2⟩
    · have h0 := h0.1; have h1 := h1.1; omega
    · have h0 := h0.1; have h2 := h2.1; omega),
    outcomeMass_disjoint_or _ _ _ (by
      intro x h
      have h1 := h.1.1; have h2 := h.2.1; omega),
    first_mass hn hs a m hm u ha hdB j hj hcop,
    second_mass hn a m hd hdB j hj,third_mass hn a m hd hdB j hj,← add_assoc]
  exact three_mode_mass (by positivity) hd hcop

end ExactQuantumFactoring.OrderTrial


end

end OAI
