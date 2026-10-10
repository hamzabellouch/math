import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCellBounds
import OAI.NumberTheory.JointDickman.Amplification.HighExclusiveLocalLaw

namespace OAI

/-! # The conditional common-product cell bound -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem primeProductLogCell_eq {D : Type*} [DecidableEq D]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (w : (Q → Bool) → ℝ) (c : Q → Bool) (u r : (ZMod q)ˣ)
    (hu : (retainedPrimeProduct Q c : ZMod q) = u) (d : D) :
    optionCellMass w (primeProductCell Q (logResidueCell B q lower upper) c) (d, r) =
      ∑ e : Q → Bool,
        if Real.log (retainedPrimeProduct Q e) / B ∈
            Set.Ioc (lower d - Real.log (retainedPrimeProduct Q c) / B)
              (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
          (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) then w e else 0 := by
  unfold optionCellMass
  apply sum_congr rfl
  intro e _
  have hi := product_cell_iff (B := B) (retainedPrimeProduct_pos Q hQ c)
    (retainedPrimeProduct_pos Q hQ e) u r hu (lower d) (upper d)
  simp only [primeProductCell, logResidueCell_eq_some B q lower upper hdisjoint, hi]

open Classical in
/-- A low exclusive product shifts each cell inside a fixed positive
logarithmic range, where the common-product density is uniformly bounded. -/
theorem primeCommonLogCell_upper
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ lower upper : D → ℝ,
      (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
      (∀ d, 1 / 2 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
      ∀ e : auxiliaryPrimes B → Bool,
      lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e → ∀ d : D, ∀ r : (ZMod q)ˣ,
      optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
        (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c e) (d, r) ≤
        M * (upper d - lower d) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨M, C, hM0, hC, hbound⟩ := primeSite_interval_upper hSD hSW hM hMP
    (Or.inl rfl : (1 / 4 : ℝ) = 1 / 4 ∨ (1 / 4 : ℝ) = 1 / 2)
  refine ⟨M, C, hM0, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq lower upper hdisjoint hlower horder hupper e he d r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  have hcut : ∀ p ∈ auxiliaryPrimes B, q < p := by
    intro p hp
    have hP : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
    exact hqP.trans_lt hP
  let u := ZMod.unitOfCoprime (retainedPrimeProduct (auxiliaryPrimes B) e)
    (retainedPrimeProduct_coprime (auxiliaryPrimes B) (auxiliaryPrimes_prime B) (NeZero.ne q) hcut e)
  let t := Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / (B : ℝ)
  have ht : 0 ≤ t := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have ht' : t ≤ 1 / 4 := he
  have hcomm : (fun c => primeProductCell (auxiliaryPrimes B)
      (logResidueCell B q lower upper) c e) =
      primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) e := by
    funext c
    simp only [primeProductCell, Nat.mul_comm]
  rw [hcomm, primeProductLogCell_eq _ (auxiliaryPrimes_prime B) B q lower upper
    hdisjoint _ e u r rfl d]
  have hb := hboundB (lower d - t) (upper d - t) (by linarith [hlower d])
    (by linarith [horder d]) (by linarith [hupper d]) q hq (u⁻¹ * r)
  simpa only [quarterPrimeMass_eq, t, sub_sub_sub_cancel_right] using hb

end JointDickman

end OAI
