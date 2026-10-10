import Mathlib
import OAI.Computability.QuantumFactoring.ArithmeticBounds
import OAI.Computability.QuantumFactoring.PhysicalTrialLaw

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma outcomeMass_finite_union {α β : Type*} [Fintype α] [DecidableEq β]
    (ψ : α→ℂ) (S : Finset β) (E : β→α→Prop)
    (h : ∀ x j k, j∈S → k∈S → E j x → E k x → j=k) :
    outcomeMass (fun x => ∃ j∈S, E j x) ψ=∑ j∈S, outcomeMass (E j) ψ := by
  classical
  unfold outcomeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∃ j∈S, E j x
  · obtain ⟨j,hj,he⟩ := hx
    rw [ite_eq_left ⟨j,hj,he⟩,Finset.sum_eq_single j]
    · rw [ite_eq_left he]
    · intro k hk hkj
      exact ite_eq_right (fun hek => hkj (h x k j hk hj hek he))
    · exact fun hj' => False.elim (hj' hj)
  · rw [ite_eq_right hx]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun he => hx ⟨j,hj,he⟩)

namespace OrderTrial

def ValidLabel (n a m d j : ℕ) : Prop :=
  0<d ∧ d<2^n ∧ j<d ∧ Nat.Coprime j d ∧ a^d%m=1

noncomputable def labelPair {w : ℕ} (s n : ℕ) (x : Raw w s n) : ℕ×ℕ :=
  if (bitsValue x.1).toNat<2 then
    scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY x.2.1)) (2*(s+3)+1)
  else ((bitsValue x.2.2.1).toNat,(bitsValue x.2.2.2.1).toNat)

lemma labelEvent_pair {w s n d j : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) : labelPair s n x=(d,j) := by
  rcases h with h|h|h
  · rw [labelPair,ite_eq_left h.1]
    exact h.2.1.2
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1

lemma labelEvent_unique {w s n d j d' j' : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) (h' : labelEvent s n a m d' j' x) :
    d=d' ∧ j=j' := by
  have he := (labelEvent_pair a m x h).symm.trans (labelEvent_pair a m x h')
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Arithmetic validation is performed in every mode, before any returned
candidate is used. The plain scan/guess never serves as an order certificate. -/
noncomputable def trialResult {w : ℕ} (s n : ℕ) (a m : Basis w) (x : Raw w s n) : Option ℕ := by
  classical
  let dj := labelPair s n x
  exact if ValidLabel n (bitsValue a).toNat (bitsValue m).toNat dj.1 dj.2 ∧
      labelEvent s n a m dj.1 dj.2 x then some dj.1 else none

lemma trialResult_some {w s n d : ℕ} (a m : Basis w) (x : Raw w s n) :
    trialResult s n a m x=some d ↔ ∃ j,
      ValidLabel n (bitsValue a).toNat (bitsValue m).toNat d j ∧ labelEvent s n a m d j x := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · constructor
    · intro hd
      have he := Option.some.inj hd
      exact ⟨(labelPair s n x).2,he ▸ h⟩
    · rintro ⟨j,hv,hl⟩
      rw [labelEvent_pair a m x hl]
  · constructor
    · intro hh; cases hh
    · rintro ⟨j,hv,hl⟩
      have he := labelEvent_pair a m x hl
      exact False.elim (h (by simpa only [he] using And.intro hv hl))

lemma validLabel_order_dvd {n a m d j : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (h : ValidLabel n a m d j) : orderOf u∣d := by
  let : NeZero m := ⟨by omega⟩
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  apply ZMod.val_injective
  rw [← nat_pow_eq_unit u ha d,h.2.2.2.2]
  exact (ZMod.val_one'' (by omega : m≠1)).symm

lemma true_validLabel {n a m : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (hdB : orderOf u<2^n)
    (j : ℕ) (hj : j<orderOf u) (hc : Nat.Coprime j (orderOf u)) :
    ValidLabel n a m (orderOf u) j := by
  let : NeZero m := ⟨by omega⟩
  refine ⟨orderOf_pos u,hdB,hj,hc,?_⟩
  rw [nat_pow_eq_unit u ha,pow_orderOf_eq_one,Units.val_one,ZMod.val_one'' (by omega : m≠1)]

lemma trialResult_multiple {w s n d : ℕ} (a m : Basis w) (hm : 2≤(bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (x : Raw w s n) (h : trialResult s n a m x=some d) :
    0<d ∧ d<2^n ∧ orderOf u∣d := by
  obtain ⟨j,hv,_⟩ := (trialResult_some a m x).mp h
  exact ⟨hv.1,hv.2.1,validLabel_order_dvd hm u ha hv⟩

/-- The physical, validated order trial has the manuscript's exact true-order
mass phi(r)*lambda(r). False candidates remain in the recorded history. -/
theorem trialResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    outcomeMass (fun x => trialResult s n a m x=some (orderOf u)) (rawState s n a m)=
      (Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ) := by
  classical
  let S := (Finset.range (orderOf u)).filter (fun j => Nat.Coprime j (orderOf u))
  have he : (fun x : Raw w s n => trialResult s n a m x=some (orderOf u))=
      (fun x => ∃ j∈S, labelEvent s n a m (orderOf u) j x) := by
    funext x
    apply propext
    rw [trialResult_some]
    constructor
    · rintro ⟨j,hv,hl⟩
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.2.2.1,hv.2.2.2.1⟩,hl⟩
    · rintro ⟨j,hj,hl⟩
      have hj' := Finset.mem_filter.mp hj
      exact ⟨j,true_validLabel hm u ha hdB j (Finset.mem_range.mp hj'.1) hj'.2,hl⟩
  rw [he,outcomeMass_finite_union _ S _ (by
    intro x j k _ _ hj hk
    exact (labelEvent_unique a m x hj hk).2)]
  have hr : ∀ j∈S, outcomeMass (labelEvent s n a m (orderOf u) j) (rawState s n a m)=
      (prescribedMass (orderOf u):ℝ) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact labelEvent_mass hn hs a m hm u ha hdB j (Finset.mem_range.mp hj'.1) hj'.2
  rw [Finset.sum_congr rfl hr,Finset.sum_const,nsmul_eq_mul]
  congr 1
  norm_cast
  simp [S,Nat.totient,Nat.coprime_comm]

lemma actual_trial_lower {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    1/(2048*(n+1):ℝ)≤outcomeMass (fun x => trialResult s n a m x=some (orderOf u)) (rawState s n a m) := by
  rw [trialResult_mass hn hs a m hm u ha hdB]
  have hd := orderOf_pos u
  have he : (1/(2048*(orderOf u:ℝ)))≤(prescribedMass (orderOf u):ℝ) := by
    have ht := (Rat.cast_le (K:=ℝ)).mpr (prescribedMass_lower hd)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using ht
  have ht := totient_ratio_lower hd hdB
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (Nat.totient (orderOf u)))
  have hdiv := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤1/2048)
  calc
    _ = (1/2048:ℝ)*(1/(n+1)) := by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring
    _ ≤ (1/2048:ℝ)*((Nat.totient (orderOf u):ℝ)/orderOf u) := hdiv
    _ = (Nat.totient (orderOf u):ℝ)*(1/(2048*(orderOf u:ℝ))) := by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring
    _ ≤ _ := hmul

end OrderTrial
end ExactQuantumFactoring


end

end OAI
