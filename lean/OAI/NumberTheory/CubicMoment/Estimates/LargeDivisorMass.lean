import OAI.NumberTheory.CubicMoment.Estimates.DivisorOuterMass
import OAI.NumberTheory.CubicMoment.Estimates.PrimeSliceEnergySum

namespace OAI

/-! Sum the actual large-common-divisor mass using the finite prime
factor multiplicity, retaining the shortening in both sieve scales. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_large_divisor_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
      (e : Eisenstein) (H U : Finset Eisenstein) (u t N₀ B D : ℝ),
      1 ≤ R → (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → (∀ p ∈ U, primaryPrime p) →
      0 < N₀ → 1 ≤ B → 1 ≤ D → D ≤ ∏ i, X i →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      let N := R^Fintype.card ι*(∏ i, X i)/D
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        fullPrimeDivisorMellinMass R W X e H u N₀ (∏ p ∈ s, p) t) ≤
      C*(2^Fintype.card ι:ℝ)*(2*B*N)^ε*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
        ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := fullPrime_divisor_outer_mass (ι := ι) hε
  refine ⟨C,hC,?_⟩
  intro R W X e H U u t N₀ B D hR hX hlo hhi hU hN₀ hB hD hDL hH
  dsimp only
  let L := ∏ i, X i
  let N := R^Fintype.card ι*L/D
  let A := C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)
  have hL : 0 < L := Finset.prod_pos (fun i _ => hX i)
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hN : 1 ≤ N := by
    apply (le_div_iff₀ hD0).mpr
    have hRp : 1 ≤ R^Fintype.card ι := one_le_pow₀ hR
    simpa only [one_mul] using hDL.trans (le_mul_of_one_le_left hL.le hRp)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (s : Finset Eisenstein)
      (hs : s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p))) :
      fullPrimeDivisorMellinMass R W X e H u N₀ (∏ p ∈ s, p) t ≤
        A*∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2 := by
    obtain ⟨hsU,hfD⟩ := Finset.mem_filter.mp hs
    have hf := primary_finset_prod s (fun p : Eisenstein => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp hsU hp)).1)
    apply hbound R W X (∏ p ∈ s, p) e H u t N₀ B N hX hlo hhi hf hN₀ hB hN _ hH
    intro n hn
    apply (fullPrimeSliceSupport_bounds R W X _ e hn).2.2.2.trans
    exact div_le_div_of_nonneg_left (mul_nonneg (by positivity) hL.le) hD0 hfD.le
  have he := fullPrime_summed_slice_energy W X hX hlo hhi e U hU
  have hesub : (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
        ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) ≤
      (2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ‖fullPrimeCoefficient R W X b‖^2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans he
  calc
    _ ≤ ∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        A*∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2 := Finset.sum_le_sum hrow
    _ = A*(∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ‖fullPrimeCoefficient R W X b‖^2) := mul_le_mul_of_nonneg_left hesub hA
    _ = _ := by dsimp [A,N,L]; ring

end CubicFirstMoment

end

end OAI
