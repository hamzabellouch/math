import OAI.NumberTheory.Ostmann.Arithmetic.MovingSplitModulusBound
import OAI.NumberTheory.Ostmann.ZeroDensity.PageRegularAverage

namespace OAI

/-! # Conductor-prime deletion for the complete sampled modulus -/

namespace Ostmann
open scoped Classical BigOperators

private theorem naturalProduct_coprime_right {σ : Type*} (r : ℕ) (value : σ → ℕ)
    (h : ∀ i, r.Coprime (value i)) (s : List σ) :
    r.Coprime (MovingSlotReversal.naturalProduct value s) := by
  induction s with
  | nil => simp [MovingSlotReversal.naturalProduct]
  | cons i s ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons] using
      (h i).mul_right ih

theorem MovingSlotData.frequencyProduct_coprime {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (r : ℕ) (hf : T.Frequencies (fun s => r.Coprime s.natAbs)) :
    r.Coprime T.frequencyProduct.natAbs := by
  induction T with
  | leaf => exact hf
  | node s CL CR U left right ihL ihR =>
    simpa only [MovingSlotData.frequencyProduct, Int.natAbs_mul] using
      (hf.1.mul_right (ihL hf.2.1)).mul_right (ihR hf.2.2)

theorem movingGiantUnitPeriod_coprime {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (r : ℕ)
    (hf : T.Frequencies (fun s => r.Coprime s.natAbs))
    (hvalue : ∀ i, r.Coprime (value i)) (hout : r.Coprime outside.prod) :
    r.Coprime (movingGiantUnitPeriod value outside T).natAbs := by
  have hfreq := T.frequencyProduct_coprime r hf
  induction T with
  | leaf s slots =>
    simpa only [movingGiantUnitPeriod, Int.natAbs_mul, Int.natAbs_natCast,
      MovingSlotData.regularSlots] using
      (hfreq.mul_right (naturalProduct_coprime_right r value hvalue slots)).mul_right hout
  | node s CL CR U left right ihL ihR =>
    have hlocal := (hfreq.mul_right (naturalProduct_coprime_right r value hvalue
      (MovingSlotData.node s CL CR U left right).regularSlots)).mul_right hout
    have hcomp := hf.1.mul_right (naturalProduct_coprime_right r value hvalue U)
    simpa only [movingGiantUnitPeriod, Int.natAbs_mul, Int.natAbs_natCast] using
      ((hlocal.mul_right hcomp).mul_right (ihL hf.2.1
        (left.frequencyProduct_coprime r hf.2.1))).mul_right
        (ihR hf.2.2 (right.frequencyProduct_coprime r hf.2.2))

theorem movingFullPairModulus_coprime {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (r : ℕ)
    (hfreq : ∀ b, (T b).Frequencies (fun s => r.Coprime s.natAbs))
    (hvalues : ∀ i, r.Coprime (value i)) (hout : r.Coprime outside.prod)
    (hq : ∀ i ∈ S, r.Coprime (q i)) :
    r.Coprime (movingFullPairModulus value hvalue outside childBound pivotBound T hf q S) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_prod_right_iff.mpr
  intro b _
  have hg := movingGiantUnitPeriod_coprime value outside (T b) r (hfreq b) hvalues hout
  have ha := hg.of_dvd_right (Int.natAbs_dvd_natAbs.mpr
    (movingAuxiliaryUnitPeriod_dvd_full value outside (T b)))
  have ht := movingTopPeriod_coprime_of_auxiliary value hvalue outside childBound pivotBound
    (T b) (hf b) r (hfreq b) ha
  have hd := ha.of_dvd_right (Int.natAbs_dvd_natAbs.mpr
    (movingSpectatorDenominator_dvd_auxiliary value outside (T b)))
  exact (((ht.mul_right hd).mul_right (Nat.coprime_prod_right_iff.mpr hq)).mul_right hg)

/-- The deleted large conductor prime cannot divide the full modulus: its
remaining prime factors come from the sampled values, spectators and frequencies. -/
theorem movingFullPairModulus_deleted_prime_coprime {σ I : Type*}
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I)
    (hq : ∀ i ∈ S, (q i).Prime) (hout : ∀ p ∈ outside, p.Prime)
    (V cutoff : ℕ) (hV : V < cutoff)
    (hfreq : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ V))
    (r : ℕ) (hr : r.Prime) (hcut : cutoff ≤ r)
    (hvalues : ∀ i, value i ≠ r) (hspec : ∀ i ∈ S, q i ≠ r)
    (houtside : r ∉ outside) :
    r.Coprime (movingFullPairModulus value (fun i => (hprime i).ne_zero) outside
      childBound pivotBound T hf q S) := by
  have hsmall (s : ℤ) (hs : s ≠ 0) (hsV : s.natAbs ≤ V) : r.Coprime s.natAbs := by
    apply hr.coprime_iff_not_dvd.mpr
    intro hd
    have hpos : 0 < s.natAbs := Int.natAbs_pos.mpr hs
    have hle := Nat.le_of_dvd hpos hd
    omega
  have hfreq' : ∀ b, (T b).Frequencies (fun s => r.Coprime s.natAbs) := by
    have go {d : ℕ} (U : MovingSlotData σ d) :
        U.Frequencies (· ≠ 0) → U.Frequencies (fun s => s.natAbs ≤ V) →
          U.Frequencies (fun s => r.Coprime s.natAbs) := by
      induction U with
      | leaf s slots => exact fun hn hb => hsmall s hn hb
      | node s CL CR U left right ihL ihR =>
        intro hn hb
        exact ⟨hsmall s hn.1 hb.1, ihL hn.2.1 hb.2.1, ihR hn.2.2 hb.2.2⟩
    exact fun b => go (T b) (hf b) (hfreq b)
  have hval : ∀ i, r.Coprime (value i) := by
    intro i
    apply hr.coprime_iff_not_dvd.mpr
    intro hd
    exact hvalues i ((Nat.prime_dvd_prime_iff_eq hr (hprime i)).mp hd).symm
  apply movingFullPairModulus_coprime value (fun i => (hprime i).ne_zero) outside
    childBound pivotBound T hf q S r hfreq' hval
  · apply Nat.coprime_list_prod_right_iff.mpr
    intro p hp
    apply hr.coprime_iff_not_dvd.mpr
    intro hd
    exact houtside (((Nat.prime_dvd_prime_iff_eq hr (hout p hp)).mp hd).symm ▸ hp)
  · intro i hi
    apply hr.coprime_iff_not_dvd.mpr
    intro hd
    exact hspec i hi ((Nat.prime_dvd_prime_iff_eq hr (hq i hi)).mp hd).symm

/-- The regular block has no exceptional-character factor after the one
prescribed conductor-prime deletion. Its Page weight remains on the reduced block. -/
theorem movingSplitModulus_page_projection {σ I : Type*}
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I)
    (hq : ∀ i ∈ S, (q i).Prime) (hout : ∀ p ∈ outside, p.Prime)
    (V cutoff : ℕ) (hV : V < cutoff)
    (hfreq : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ V))
    (z : Option PrimitiveRealZero)
    (hvalues : ∀ e, z = some e → ∀ r, deletedConductorPrime e.modulus cutoff = some r →
      ∀ i, value i ≠ r)
    (hspec : ∀ e, z = some e → ∀ r, deletedConductorPrime e.modulus cutoff = some r →
      ∀ i ∈ S, q i ≠ r)
    (houtside : ∀ e, z = some e → ∀ r, deletedConductorPrime e.modulus cutoff = some r → r ∉ outside)
    (hlarge : ∀ i, cutoff ≤ value i)
    (hcop : (MovingSlotReversal.naturalProduct value (T false).regularSlots).Coprime
      (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf q S)) :
    pageAtModulus (MovingSlotReversal.naturalProduct value (T false).regularSlots *
      movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf q S) z =
      pageAtModulus (movingReducedPairModulus value (fun i => (hprime i).ne_zero)
        outside childBound pivotBound T hf q S) z := by
  apply pageAtModulus_regular_factor z _ _ cutoff
  · intro r hr hd
    by_contra hlt
    have hc : r.Coprime (MovingSlotReversal.naturalProduct value (T false).regularSlots) := by
      apply naturalProduct_coprime_right r value
      intro i
      apply hr.coprime_iff_not_dvd.mpr
      intro hri
      have he := (Nat.prime_dvd_prime_iff_eq hr (hprime i)).mp hri
      have hi := hlarge i
      omega
    exact hr.coprime_iff_not_dvd.mp hc hd
  · intro e he r hr hd
    have hc := movingFullPairModulus_deleted_prime_coprime value hprime outside childBound pivotBound
      T hf q S hq hout V cutoff hV hfreq r (deletedConductorPrime_spec hr).1
      (deletedConductorPrime_spec hr).2.2 (hvalues e he r hr) (hspec e he r hr) (houtside e he r hr)
    exact ((deletedConductorPrime_spec hr).1.coprime_iff_not_dvd.mp hc)
      (hd.trans (movingSplitModulus_dvd_full value (fun i => (hprime i).ne_zero) outside
        childBound pivotBound T hf q S _ rfl hcop))

end Ostmann

end OAI
