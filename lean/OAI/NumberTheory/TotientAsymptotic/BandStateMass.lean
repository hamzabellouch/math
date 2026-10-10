import OAI.NumberTheory.TotientAsymptotic.BandStates

namespace OAI

/-! One exact finite transfer step for reciprocal masses of truncated states. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma factorProduct_band_split {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b)
    {U V : ℝ} (hUV : U ≤ V)
    (ht : ∀ j,partBelow (t.left j) V=t.left j)
    (htail : ∀ j : Fin b,k ≤ j.val → partBetween (t.left j) U V=1) :
    factorProduct t=factorProduct (lowerState t U)*pairedProduct (stateBand hk t U V) := by
  have he (j : Fin b) : partBelow (t.left j) U*partBetween (t.left j) U V=t.left j :=
    (partBelow_band_split _ hUV).trans (ht j)
  change (∏ j,t.left j)=(∏ j,partBelow (t.left j) U)*
    (∏ j : Fin k,partBetween (t.left (Fin.castLE hk j)) U V)
  rw [← fin_prod_initial hk _ htail,← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => (he j).symm)

lemma state_fiber_reciprocal {b k : ℕ} (hk : k ≤ b) {U V : ℝ} (hUV : U ≤ V)
    (Q : Finset (ShiftedPair b))
    (hQ : ∀ t ∈ Q,∀ j,partBelow (t.left j) V=t.left j ∧ partBelow (t.right j) V=t.right j)
    (htail : ∀ t ∈ Q,∀ j : Fin b,k ≤ j.val →
      partBetween (t.left j) U V=1 ∧ partBetween (t.right j) U V=1)
    (r : ShiftedPair b) :
    (∑ t ∈ Q.filter (fun t => lowerState t U=r),(factorProduct t:ℝ)⁻¹)=
      (factorProduct r:ℝ)⁻¹*
      (∑ f ∈ (Q.filter (fun t => lowerState t U=r)).image (fun t => stateBand hk t U V),
        (pairedProduct f:ℝ)⁻¹) := by
  classical
  have hi : ∀ t ∈ Q.filter (fun t => lowerState t U=r),
      ∀ s ∈ Q.filter (fun t => lowerState t U=r),stateBand hk t U V=stateBand hk s U V → t=s := by
    intro t ht s hs he
    obtain ⟨ht,htr⟩ := Finset.mem_filter.mp ht
    obtain ⟨hs,hsr⟩ := Finset.mem_filter.mp hs
    exact lowerState_recover hk hUV (hQ t ht) (hQ s hs) (htail t ht) (htail s hs)
      (htr.trans hsr.symm) he
  rw [Finset.mul_sum,Finset.sum_image hi]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨ht,htr⟩ := Finset.mem_filter.mp ht
  rw [factorProduct_band_split hk t hUV (fun j => (hQ t ht j).1)
    (fun j hj => (htail t ht j hj).1),htr,Nat.cast_mul,mul_inv_rev]
  ring

/-- Summing on the image of the next state avoids charging old multiplicities again. -/
theorem band_state_mass_transfer {b k : ℕ} (hk : k ≤ b) {U V A : ℝ} (hUV : U ≤ V)
    (Q : Finset (ShiftedPair b))
    (hQ : ∀ t ∈ Q,∀ j,partBelow (t.left j) V=t.left j ∧ partBelow (t.right j) V=t.right j)
    (htail : ∀ t ∈ Q,∀ j : Fin b,k ≤ j.val →
      partBetween (t.left j) U V=1 ∧ partBetween (t.right j) U V=1)
    (hband : ∀ r ∈ Q.image (fun t => lowerState t U),
      (∑ f ∈ (Q.filter (fun t => lowerState t U=r)).image (fun t => stateBand hk t U V),
        (pairedProduct f:ℝ)⁻¹) ≤ A) :
    (∑ t ∈ Q,(factorProduct t:ℝ)⁻¹) ≤
      A*(∑ r ∈ Q.image (fun t => lowerState t U),(factorProduct r:ℝ)⁻¹) := by
  classical
  let R := Q.image (fun t => lowerState t U)
  have hmap : ∀ t ∈ Q,lowerState t U ∈ R := fun t ht => Finset.mem_image.mpr ⟨t,ht,rfl⟩
  calc
    _ = ∑ r ∈ R,∑ t ∈ Q.filter (fun t => lowerState t U=r),(factorProduct t:ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun t => (factorProduct t:ℝ)⁻¹)).symm
    _ = ∑ r ∈ R,(factorProduct r:ℝ)⁻¹*
        (∑ f ∈ (Q.filter (fun t => lowerState t U=r)).image (fun t => stateBand hk t U V),
          (pairedProduct f:ℝ)⁻¹) :=
      Finset.sum_congr rfl (fun r _ => state_fiber_reciprocal hk hUV Q hQ htail r)
    _ ≤ ∑ r ∈ R,(factorProduct r:ℝ)⁻¹*A := Finset.sum_le_sum (fun r hr =>
      mul_le_mul_of_nonneg_left (hband r hr) (inv_nonneg.mpr (Nat.cast_nonneg _)))
    _ = _ := by rw [← Finset.sum_mul,mul_comm]

end TotientAsymptotic

end

end OAI
