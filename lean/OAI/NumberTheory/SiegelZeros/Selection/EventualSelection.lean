import OAI.NumberTheory.SiegelZeros.Structure.EventuallyInputs

namespace OAI

namespace SiegelZeros

section

open Filter
open scoped Topology

namespace SiegelZerosAwei.W50

open WeightedTorusJets.W48 Result.Workers.W33

theorem auxiliaryU_cube (γ q : ℝ) :
    auxiliaryU γ q ^ (3 : ℕ) = (auxiliaryN γ q : ℝ) ^ (4 : ℕ) := by
  unfold auxiliaryU
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) (4 / 3 : ℝ) 3]
  norm_num

theorem false_of_actual_pivot_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    (H : ℕ) (hH : 86713344 ≤ H) (γ C CH : ℝ)
    (hγ : 0 < γ) (hCH : 0 ≤ CH)
    (hallow : (C + 13 / 24) / (4 * γ / 3) < 1 / 16)
    (q : ι → ℕ) (delta : ι → ℝ) (P : ι → Finset W31.MultiIndex)
    (hq : Tendsto q l atTop) (hdelta : Tendsto delta l (𝓝 0))
    (hcard : ∀ᶠ i in l, (P i).card = auxiliaryN γ (q i) ^ 4)
    (hcut : ∀ᶠ i in l, ∀ a ∈ P i, W31.weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i))
    (hmaster : ∀ᶠ i in l,
      1 ≤ W46.masterRHS (firstOrder (P i)) (transverseOrder (P i))
        (P i).card (auxiliaryU γ (q i)) C CH (Real.log (q i)) (delta i)
        (Real.log (auxiliaryU γ (q i))) (Real.log (P i).card) (Real.log 8)) :
    False := by
  have hi := SiegelZeros.W49.eventual_error_inputs P H hH hγ hq hcard hcut
  have hcardR : ∀ᶠ i in l, ((P i).card : ℝ) =
      (auxiliaryN γ (q i) : ℝ) ^ (4 : ℕ) := by
    filter_upwards [hcard] with i hc
    exact_mod_cast hc
  apply false_of_ceiling_master γ C CH (SiegelZeros.W49.fixedPivotCoefficient H)
    hγ (SiegelZeros.W49.fixedPivotCoefficient_pos (by omega)) hCH hallow
    (fun i => (q i : ℝ)) (fun i => firstOrder (P i))
    (fun i => transverseOrder (P i)) (fun i => ((P i).card : ℝ)) delta
    (tendsto_natCast_atTop_atTop.comp hq) hdelta
  · filter_upwards [hi, hcardR] with i hii hc
    rw [hc]
    exact hii.1
  · filter_upwards [hi, hcardR] with i hii hc
    rw [hc]
    exact hii.2.2.2.1
  · exact hi.mono fun _ h => h.2.2.2.2
  · filter_upwards [hcardR] with i hc
    rw [auxiliaryU_cube]
    exact hc
  · exact hmaster

end SiegelZerosAwei.W50

end

section

open Filter
open scoped Topology

namespace SiegelZerosAwei.W50

open WeightedTorusJets.W48 Result.Workers.W33

theorem false_of_eventual_exists_pivot_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    (H : ℕ) (hH : 86713344 ≤ H) (γ C CH : ℝ)
    (hγ : 0 < γ) (hCH : 0 ≤ CH)
    (hallow : (C + 13 / 24) / (4 * γ / 3) < 1 / 16)
    (q : ι → ℕ) (delta : ι → ℝ)
    (hq : Tendsto q l atTop) (hdelta : Tendsto delta l (𝓝 0))
    (hexists : ∀ᶠ i in l, ∃ P : Finset W31.MultiIndex,
      P.card = auxiliaryN γ (q i) ^ 4 ∧
      (∀ α ∈ P, W31.weight (H : ℝ) α ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i)) ∧
      1 ≤ W46.masterRHS (firstOrder P) (transverseOrder P)
        P.card (auxiliaryU γ (q i)) C CH (Real.log (q i)) (delta i)
        (Real.log (auxiliaryU γ (q i))) (Real.log P.card) (Real.log 8)) : False := by
  classical
  let property := fun i (P : Finset W31.MultiIndex) =>
    P.card = auxiliaryN γ (q i) ^ 4 ∧
      (∀ α ∈ P, W31.weight (H : ℝ) α ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * auxiliaryU γ (q i)) ∧
      1 ≤ W46.masterRHS (firstOrder P) (transverseOrder P)
        P.card (auxiliaryU γ (q i)) C CH (Real.log (q i)) (delta i)
        (Real.log (auxiliaryU γ (q i))) (Real.log P.card) (Real.log 8)
  let P : ι → Finset W31.MultiIndex := fun i =>
    if h : ∃ p, property i p then h.choose else ∅
  have hP : ∀ᶠ i in l, property i (P i) := by
    filter_upwards [hexists] with i hi
    change ∃ p, property i p at hi
    dsimp only [P]
    rw [dite_eq_left hi]
    exact hi.choose_spec
  exact false_of_actual_pivot_master H hH γ C CH hγ hCH hallow q delta P hq hdelta
    (hP.mono fun _ h => h.1) (hP.mono fun _ h => h.2.1)
    (hP.mono fun _ h => h.2.2)

end SiegelZerosAwei.W50

end

end SiegelZeros

end OAI
