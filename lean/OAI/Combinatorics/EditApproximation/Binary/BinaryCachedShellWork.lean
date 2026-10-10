import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGridWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalWarmupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryCachedContinuation
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalDenominator

namespace OAI

/-! Initial and warmup returns are integers on every seed. Their cache
representation is produced by the counted fixed-denominator routine, rather
than by an uncharged conversion of a rational value. -/

namespace EditApproximation

theorem localInitialConeTable_den_one {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (query : TargetInterval target.length) :
    (localInitialConeTable source target U N P F A a query).den = 1 := by
  unfold localInitialConeTable
  split_ifs
  · exact Rat.den_zero
  · apply Nat.eq_one_of_dvd_one
    apply rationalMinimum_den_dvd
    · have heq : (32 * F + 1 : ℚ) * N = (((32 * F + 1) * N : ℕ) : ℚ) := by
        push_cast
        rfl
      rw [heq, Rat.den_natCast]
    · intro v hv
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
      unfold initialConeValue scaledSeedValue
      apply rat_den_add_dvd
      · apply rat_den_max_dvd
        · simp only [Rat.den_natCast, dvd_refl]
        · have heq : rationalStateGap source target r =
              (((r.hi : ℤ) - r.lo - source.length : ℤ) : ℚ) := by
            simp only [rationalStateGap, Int.cast_sub, Int.cast_natCast]
          rw [heq, ← Int.cast_abs]
          simp only [Rat.den_intCast, dvd_refl]
      · have heq : (32 * F : ℚ) * targetEndpointDistance query r =
            ((32 * F * targetEndpointDistance query r : ℕ) : ℚ) := by
          push_cast
          rfl
        rw [heq, Rat.den_natCast]

namespace BinaryFraction

attribute [local irreducible] initialProgramWithWork localWarmupKernelWithWork

def cachedInitialProgramWithWork {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (U : TargetInterval n → ℕ) (query : TargetInterval n) : BinaryFraction × ℕ :=
  finishCachedWithWork (initialProgramWithWork sourceLength N P F A a U query)
    [true] (by decide) 0

def cachedInitialProgramBitBudget (P Amax B : ℕ) : ℕ :=
  initialProgramBitBudget P Amax B + powerDenominatorBitBudget 0 (initialMinimumWordBudget (B + 4)) 1 + 1

theorem cachedInitialProgramWithWork_cost {n : ℕ} (sourceLength N P F Amax B : ℕ)
    (A a : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F ≤ B) (hs : Nat.size sourceLength ≤ B) (hn : Nat.size n ≤ B)
    (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B) (ha : a.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
    (cachedInitialProgramWithWork sourceLength N P F A a U q).2 ≤
      cachedInitialProgramBitBudget P Amax B := by
  have hb := initialProgramWithWork_bounds sourceLength N P F Amax B A a U q
    hB hP hN hPb hF hs hn hU hAb ha hA hmax
  have hc := powerDenominatorWithWork_cost
    (initialProgramWithWork sourceLength N P F A a U q).1 [true] (by decide) 0
    (initialMinimumWordBudget (B + 4)) 1 hb.1 (by decide)
  exact Nat.add_le_add_right (Nat.add_le_add hb.2 hc) 1

theorem cachedInitialProgramWithWork_value_width {α : Type*} (source target : List α)
    (N P F : ℕ) (A a : BinaryFraction) (U : TargetInterval target.length → ℕ)
    (query : TargetInterval target.length) (hP : 0 < P) :
    (cachedInitialProgramWithWork source.length N P F A a U query).1.value =
        localInitialConeTable source target U N P F A.value a.value query ∧
    (cachedInitialProgramWithWork source.length N P F A a U query).1.width ≤
        Nat.size ((32 * F + 1) * N) + 3 := by
  let raw := initialProgramWithWork source.length N P F A a U query
  have hraw := initialProgramWithWork_value source target N P F A a U query hP
  have hd : raw.1.value.den ∣ bitWordValue [true] ^ 0 := by
    rw [hraw, localInitialConeTable_den_one]
    exact one_dvd _
  have hv : |raw.1.value| ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    rw [hraw, abs_of_nonneg (localInitialConeTable_nonneg source target U N P F A.value a.value query)]
    unfold localInitialConeTable
    split_ifs
    · exact Nat.cast_nonneg _
    · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        rationalMinimum_le_fallback ((32 * F + 1 : ℚ) * N) _
  exact ⟨(finishCachedWithWork_value raw [true] (by decide) 0 hd).trans hraw,
    by
      change (powerDenominatorWithWork raw.1 [true] (by decide) 0).1.width ≤ _
      simpa only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using
        powerDenominatorWithWork_width raw.1 [true] (by decide) 0 ((32 * F + 1) * N) 1
        (by decide) hd hv⟩

def cachedLocalWarmupKernelWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny) :
    BinaryFraction × ℕ :=
  finishCachedWithWork (localWarmupKernelWithWork parent N P F a initial child query)
    [true] (by decide) 0

theorem localWarmupKernelWithWork_integer_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F V : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (hP : 0 < P) (hi : ∀ r, (initial r).value.den = 1)
    (hic : ∀ r, 0 ≤ (initial r).value ∧ (initial r).value ≤ V)
    (hc : ∀ s, (child s).value.den = 1) (hcn : ∀ s, 0 ≤ (child s).value) :
    (localWarmupKernelWithWork parent N P F a initial child query).1.value.den = 1 ∧
      |(localWarmupKernelWithWork parent N P F a initial child query).1.value| ≤ V := by
  rw [localWarmupKernelWithWork_value parent N P F hP a initial child query]
  let actions := rationalActualWideActions (M := M) parent
    (localRefinementRepresentatives N P F a.value (fun q => (initial q).value) query) P
  have hd : (rationalBellman (fun q => (initial q).value)
      (fun p q => (targetEndpointDistance p q : ℚ)) (128 * F) actions
      (fun s => (child s).value) query).den ∣ 1 := by
    apply rationalMinimum_den_dvd
    · rw [hi]
    · intro value hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      apply rationalActionValue_den_dvd
      · exact Rat.den_natCast _
      · simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F)
      · exact rationalActualWideActions_connection_den parent _ P action ha
      · intro i
        rw [hc]
  have hn : 0 ≤ rationalBellman (fun q => (initial q).value)
      (fun p q => (targetEndpointDistance p q : ℚ)) (128 * F) actions
      (fun s => (child s).value) query := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨(hic query).1, ?_⟩
    intro value hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    unfold rationalActionValue
    exact add_nonneg (add_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (rationalActualWideActions_connection_nonneg parent _ P action ha))
      (Finset.sum_nonneg fun i _ => hcn _)
  refine ⟨Nat.eq_one_of_dvd_one hd, ?_⟩
  rw [abs_of_nonneg hn]
  exact (rationalMinimum_le_fallback _ _).trans (hic query).2

theorem cachedLocalWarmupKernelWithWork_value_width {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F V : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (hP : 0 < P) (hi : ∀ r, (initial r).value.den = 1)
    (hic : ∀ r, 0 ≤ (initial r).value ∧ (initial r).value ≤ V)
    (hc : ∀ s, (child s).value.den = 1) (hcn : ∀ s, 0 ≤ (child s).value) :
    (cachedLocalWarmupKernelWithWork parent N P F a initial child query).1.value =
        (localWarmupKernelWithWork parent N P F a initial child query).1.value ∧
    (cachedLocalWarmupKernelWithWork parent N P F a initial child query).1.width ≤ Nat.size V + 3 := by
  let raw := localWarmupKernelWithWork parent N P F a initial child query
  have hb := localWarmupKernelWithWork_integer_bounds parent N P F V a initial child query hP hi hic hc hcn
  have hd : raw.1.value.den ∣ bitWordValue [true] ^ 0 := by rw [hb.1]; exact one_dvd _
  exact ⟨finishCachedWithWork_value raw [true] (by decide) 0 hd,
    by
      change (powerDenominatorWithWork raw.1 [true] (by decide) 0).1.width ≤ _
      simpa only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using
        powerDenominatorWithWork_width raw.1 [true] (by decide) 0 V 1 (by decide) hd hb.2⟩

theorem cachedLocalWarmupKernelWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F B : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction)
    (child : Fin M × TargetInterval ny → BinaryFraction) (query : TargetInterval ny)
    (hP : 0 < P) (hFpos : 1 ≤ F) (hB : 10 ≤ B) (hN : Nat.size N ≤ B)
    (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B) (hM : Nat.size M ≤ B)
    (hPbits : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).width ≤ B) (hc : ∀ s, (child s).width ≤ B) :
    (cachedLocalWarmupKernelWithWork parent N P F a initial child query).2 ≤
      localWarmupBitBudget M P F B + powerDenominatorBitBudget 0 (localWarmupWordBudget M B) 1 + 1 := by
  have hb := localWarmupKernelWithWork_bounds parent N P F B hP hFpos a initial child query
    hB hN hnx hny hM hPbits hF ha hi hc
  have hp := powerDenominatorWithWork_cost
    (localWarmupKernelWithWork parent N P F a initial child query).1 [true] (by decide) 0
    (localWarmupWordBudget M B) 1 hb.1 (by decide)
  exact Nat.add_le_add_right (Nat.add_le_add hb.2 hp) 1

end BinaryFraction
end EditApproximation

end OAI
