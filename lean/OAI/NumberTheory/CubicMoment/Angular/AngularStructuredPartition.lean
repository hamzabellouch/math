import OAI.NumberTheory.CubicMoment.Angular.AngularStructuredWeightScaling
import OAI.NumberTheory.CubicMoment.Estimates.StructuredCutoffConsistency
import OAI.NumberTheory.CubicMoment.Estimates.StructuredPartition

namespace OAI

/-! The literal angular sum and its finite smooth output partition, with
coefficient cutoffs kept consistent at every output dyad. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def structuredAngularPrimeMomentAt (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*theta ℓ z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

lemma structuredAngularPrimeMomentAt_eq (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z)
    (V : ℝ → ℂ) (hVhi : ∀ x, 2 < x → V x = 0) :
    structuredAngularPrimeMomentAt ℓ a b v e u W X Z V Y =
      structuredAngularPrimeMoment ℓ a b v e u W X V Y := by
  let T := (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
    (fun z => IsCoprime z e)
  let U := (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
    (fun z => IsCoprime z e)
  have hsub : T ⊆ U := by
    intro z hz
    obtain ⟨hz,hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨n,hn,hprod⟩ := Finset.mem_image.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨n,?_,hprod⟩,hcop⟩
    rw [coordinatePrimeSupport_trim W X hYZ] at hn
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1)
  have hzero (z : Eisenstein) (hz : z ∈ U) (hnorm : ¬norm z ≤ 2*Y) :
      V (norm z/Y) = 0 := hVhi _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hnorm))
  have hnonzero (z : Eisenstein) (hz : z ∈ U) : z ≠ 0 :=
    primary_ne_zero (orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
      (fun i n hn => (coordinatePrimeSupport_primary W X Z i n hn).1)
      (Finset.mem_filter.mp hz).1)
  symm
  change (∑ z ∈ T, _) = ∑ z ∈ U, _
  calc
    _ = ∑ z ∈ T, primeMomentCoefficient W X Z z*theta ℓ z*mellinPhase u (norm z)*
        cubicSymbol z (v*a*b^2)*V (norm z/Y) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hN : norm z ≤ 2*Y
      · rw [primeMomentCoefficient_dyad_consistent W X hYZ (hnonzero z (hsub hz)) hN]
      · rw [hzero z (hsub hz) hN]
        simp only [mul_zero]
    _ = _ := Finset.sum_subset hsub (by
      intro z hz hnot
      have hN : ¬norm z ≤ 2*Y := by
        intro hN
        have hm := orderedSupport_filter_norm (coordinatePrimeSupport W X Z) (hnonzero z hz) hN
          (Finset.mem_filter.mp hz).1
        rw [← coordinatePrimeSupport_trim W X hYZ] at hm
        exact hnot (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hz).2⟩)
      rw [hzero z hz hN,mul_zero])


def structuredAngularPrimeSum (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*theta ℓ z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

lemma structuredAngularPrimeSum_partition (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ)
    {L B : ℝ} (hL : 0 < L) (N : ℕ) (hN : 2*B ≤ (4/3:ℝ)^N)
    (hrange : ∀ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      L ≤ norm z ∧ norm z ≤ B*L) :
    structuredAngularPrimeSum ℓ a b v e u W X Z =
      ∑ k ∈ Finset.range N,
        structuredAngularPrimeMomentAt ℓ a b v e u W X Z normPartitionWeight (L*((4/3:ℝ)^k/2)) := by
  unfold structuredAngularPrimeSum structuredAngularPrimeMomentAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  have hr := hrange z (Finset.mem_filter.mp hz).1
  have hm := normPartitionWeight_partition
    (show 1 ≤ norm z/L by exact (le_div_iff₀ hL).mpr (by simpa using hr.1))
    (show norm z/L ≤ B by exact (div_le_iff₀ hL).mpr hr.2) hN
  have heq : (∑ k ∈ Finset.range N,
      normPartitionWeight (norm z/(L*((4/3:ℝ)^k/2)))) = 1 := by
    simp_rw [normPartitionWeight_scaled _ _ hL.ne' (pow_ne_zero _ (by norm_num : (4/3:ℝ) ≠ 0))]
    exact hm
  rw [heq,mul_one]

lemma structuredAngularPrimeSum_partition_dyads (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ)
    {L B : ℝ} (hL : 0 < L) (N : ℕ) (hN : 2*B ≤ (4/3:ℝ)^N)
    (hrange : ∀ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      L ≤ norm z ∧ norm z ≤ B*L)
    (hZ : ∀ k ∈ Finset.range N, L*((4/3:ℝ)^k/2) ≤ Z) :
    structuredAngularPrimeSum ℓ a b v e u W X Z =
      ∑ k ∈ Finset.range N,
        structuredAngularPrimeMoment ℓ a b v e u W X normPartitionWeight (L*((4/3:ℝ)^k/2)) := by
  rw [structuredAngularPrimeSum_partition ℓ a b v e u W X Z hL N hN hrange]
  apply Finset.sum_congr rfl
  intro k hk
  exact structuredAngularPrimeMomentAt_eq ℓ a b v e u W X
    (mul_pos hL (div_pos (pow_pos (by norm_num : (0:ℝ) < 4/3) _) (by norm_num)))
    (hZ k hk) normPartitionWeight (fun _ => normPartitionWeight_high)

end CubicFirstMoment

end

end OAI
