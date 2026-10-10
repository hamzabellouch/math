import OAI.NumberTheory.Ostmann.Arithmetic.MovingRootReconstruction
import OAI.NumberTheory.Ostmann.Construction.TransferOutputSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmallFrequencyUnits

namespace OAI

/-! # Support inherited by the reconstructed giant-only transfer -/

namespace Ostmann
open scoped Classical

/-- The integer quotient satisfies the full rigidity guard. Its frequency
unit is derived from prime sizes, rather than assumed as a new transfer input. -/
theorem moving_reconstructed_node_valid {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (x : MovingSlotState σ) (I : Finset ℕ) (s v w : ℤ) (V : ℕ)
    (hI : ∀ p ∈ I, 0 < p)
    (h : validTransferredPivot I
      (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
      (s * x.compensation value))
    (hV : s.natAbs ≤ V)
    (hlarge : ∀ q, q.Prime → q ∣ x.rightProduct value → V < q)
    (hpivot : ∀ p ∈ I, p * x.compensation value ≤ pivotBound x.depth)
    (hv : v.natAbs ≤ childBound x.depth) (hw : w.natAbs ≤ childBound x.depth)
    (hgap : 2 * pivotBound x.depth * childBound x.depth < x.rightProduct value)
    (hunit : ∀ p ∈ I, (p * x.compensation value).Coprime w.natAbs) :
    let p := reconstructedPivot
      (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
      (s * x.compensation value)
    ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w
      (p * x.compensation value) ∧ 0 < x.compensation value := by
  dsimp only
  let p := reconstructedPivot
    (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
    (s * x.compensation value)
  have hs : s ≠ 0 := left_ne_zero_of_mul h.1
  have hU : 0 < x.compensation value := Nat.pos_of_ne_zero (by
    intro hz
    exact h.1 (by simp only [hz, Nat.cast_zero, mul_zero]))
  have hR := large_prime_factors_coprime_frequency (x.rightProduct value) s hs
    (fun q hq hd => hV.trans_lt (hlarge q hq hd))
  have hRu : IsCoprime s (x.rightProduct value : ℤ) := by
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
      using hR.symm
  have he := validTransferredPivot_equation I _ _ h
  refine ⟨⟨hs, hRu, ?_, Nat.mul_pos (hI p h.2.2.2) hU,
    hpivot p h.2.2.2, hv, hw, hgap, hunit p h.2.2.2⟩, hU⟩
  change v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ) =
    s * ((p * x.compensation value : ℕ) : ℤ)
  rw [Nat.cast_mul]
  calc
    _ = (s * (x.compensation value : ℤ)) * (p : ℤ) := he
    _ = _ := by ring

/-- The two branch priors already supply their internal and outside tests.
The only new pairwise requirement is the cross-product coprimality. -/
theorem pairwise_coprime_merge_shared (A B Y : List ℕ)
    (hA : (A ++ Y).Pairwise Nat.Coprime)
    (hB : (B ++ Y).Pairwise Nat.Coprime) (hAB : A.prod.Coprime B.prod) :
    (A ++ B ++ Y).Pairwise Nat.Coprime := by
  obtain ⟨hAA, hYY, hAY⟩ := List.pairwise_append.mp hA
  obtain ⟨hBB, _, hBY⟩ := List.pairwise_append.mp hB
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨hAA, hBB, ?_⟩, hYY, ?_⟩
  · intro a ha b hb
    exact (Nat.coprime_list_prod_right_iff.mp
      (Nat.coprime_list_prod_left_iff.mp hAB a ha)) b hb
  · intro a ha y hy
    rcases List.mem_append.mp ha with ha | ha
    · exact hAY a ha y hy
    · exact hBY a ha y hy

/-- The root's pairwise test follows from the two old branch supports and
the nonzero transfer equation, since every shared prime is too large to
divide the new frequency. -/
theorem moving_transferred_current_pairwise {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (s : ℤ) (CL CR u : List σ) (l r : MovingSlotData σ n) (XL XR P : ℕ)
    (hs : s ≠ 0) (v w : ℤ)
    (hrel : v * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
      w * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) = s * P)
    (hleft : ((XL :: CL.map value) ++ outside).Pairwise Nat.Coprime)
    (hright : ((XR :: CR.map value) ++ outside).Pairwise Nat.Coprime)
    (hsmall : ∀ q, q.Prime → q ∣ XL * MovingSlotReversal.naturalProduct value CL →
      q ∣ XR * MovingSlotReversal.naturalProduct value CR → s.natAbs < q)
    (hunit : (XL * MovingSlotReversal.naturalProduct value CL).Coprime P) :
    ((MovingSlotData.node s CL CR u l r).currentSlots value XL XR ++ outside).Pairwise
      Nat.Coprime := by
  have hLR := transferred_products_coprime
    (XL * MovingSlotReversal.naturalProduct value CL)
    (XR * MovingSlotReversal.naturalProduct value CR) v w s P hs hrel hsmall
    (common_prime_pivot_unit P _ _ hunit)
  have hp := pairwise_coprime_merge_shared (XL :: CL.map value) (XR :: CR.map value)
    outside hleft hright (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct]
      using hLR)
  have he : ((XL :: CL.map value) ++ (XR :: CR.map value) ++ outside).Perm
      ((MovingSlotData.node s CL CR u l r).currentSlots value XL XR ++ outside) := by
    apply List.perm_iff_count.mpr
    intro a
    simp only [MovingSlotData.currentSlots, MovingSlotData.regularSlots, List.map_append,
      List.count_cons, List.count_append]
    omega
  exact (he.pairwise_iff (R := Nat.Coprime) (fun h => h.symm)).mp hp

/-- All current giant tests, including descendant frequencies, follow from
pairwise support and the same large-prime separation used at the root. -/
theorem moving_local_support_of_large {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hf : T.Frequencies (fun s => s ≠ 0 ∧
      ∀ q, q.Prime → q ∣ XL * XR → s.natAbs < q)) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  have cast_coprime {a b : ℕ} (h : a.Coprime b) : IsCoprime (a : ℤ) (b : ℤ) := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa only [Int.gcd_natCast_natCast] using h)
  have giant_frequency (X : ℕ) (hX : X ∣ XL * XR) :
      IsCoprime (X : ℤ) T.frequencyProduct := by
    apply (T.frequencies_isCoprime (X : ℤ)).mp
    apply hf.mono
    intro s hs
    have hu := large_prime_factors_coprime_frequency X s hs.1
      (fun q hq hqd => hs.2 q hq (hqd.trans hX))
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using hu
  have hXL := giant_frequency XL (dvd_mul_right XL XR)
  have hXR := giant_frequency XR (dvd_mul_left XR XL)
  have hpair := hp
  change (XL :: XR :: (T.regularSlots.map value ++ outside)).Pairwise Nat.Coprime at hpair
  obtain ⟨hL, htail⟩ := List.pairwise_cons.mp hpair
  obtain ⟨hR, _⟩ := List.pairwise_cons.mp htail
  have hLreg : XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro a ha
    exact hL a (List.mem_cons_of_mem XR (List.mem_append_left outside ha))
  have hRreg : XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro a ha
    exact hR a (List.mem_append_left outside ha)
  have hLout : XL.Coprime outside.prod := Nat.coprime_list_prod_right_iff.mpr
    (fun a ha => hL a (List.mem_cons_of_mem XR (List.mem_append_right _ ha)))
  have hRout : XR.Coprime outside.prod := Nat.coprime_list_prod_right_iff.mpr
    (fun a ha => hR a (List.mem_append_right _ ha))
  exact ⟨hp, hXL, hXR, cast_coprime hLreg, cast_coprime hRreg,
    cast_coprime hLout, cast_coprime hRout⟩

/-- In the transfer application the surviving top giants are actual primes.
All the additional descendant-frequency tests are therefore automatic. -/
theorem moving_local_support_prime_giants {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR V : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V < XL) (hVR : V < XR)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hf : T.Frequencies (fun s => s ≠ 0 ∧ s.natAbs ≤ V)) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  apply moving_local_support_of_large value outside T XL XR hp
  apply hf.mono
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro q hq hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · have he : q = XL := ((Nat.dvd_prime hXL).mp hd).resolve_left hq.ne_one
    exact he ▸ hs.2.trans_lt hVL
  · have he : q = XR := ((Nat.dvd_prime hXR).mp hd).resolve_left hq.ne_one
    exact he ▸ hs.2.trans_lt hVR

end Ostmann

end OAI
