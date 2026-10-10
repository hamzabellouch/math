import OAI.NumberTheory.TotientAsymptotic.TerminalStateCount
import OAI.NumberTheory.TotientAsymptotic.SmoothResidualMass

namespace OAI

/-! The final smooth-state mass with its exact cancelled-product exponent. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem terminal_state_mass {k d N : ℕ} {L : ℝ} (hk : 1 ≤ k) (hd : 0 < d)
    (Q : Finset (ShiftedPair k))
    (hQ : ∀ t ∈ Q,0 < factorProduct t ∧
      d*factorProduct t=t.remainder*(∏ j,t.right j) ∧
      largestPrimeFactor (factorProduct t) ≤ N ∧
      ((factorProduct t).primeFactorsList.length:ℝ) ≤ L) :
    (∑ t ∈ Q,(factorProduct t:ℝ)⁻¹) ≤
      (k+1:ℝ)^d.primeFactorsList.length*((k:ℝ)*(k+1))^L*primeEulerProduct N := by
  classical
  let P := Q.image factorProduct
  let W := (k+1:ℝ)^d.primeFactorsList.length*((k:ℝ)*(k+1))^L
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hmap : ∀ t ∈ Q,factorProduct t ∈ P := fun t ht => Finset.mem_image.mpr ⟨t,ht,rfl⟩
  have hP (s : ℕ) (hs : s ∈ P) : 0 < s ∧ largestPrimeFactor s ≤ N ∧
      (s.primeFactorsList.length:ℝ) ≤ L := by
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hQ t ht).1,(hQ t ht).2.2⟩
  have hfiber (s : ℕ) (hs : s ∈ P) :
      (∑ t ∈ Q.filter (fun t => factorProduct t=s),(factorProduct t:ℝ)⁻¹) ≤ W*(s:ℝ)⁻¹ := by
    let F := Q.filter (fun t => factorProduct t=s)
    have hF : ∀ t ∈ F,factorProduct t=s ∧ d*factorProduct t=t.remainder*(∏ j,t.right j) := by
      intro t ht
      exact ⟨(Finset.mem_filter.mp ht).2,(hQ t (Finset.mem_filter.mp ht).1).2.1⟩
    have hc := terminal_state_card_le hd (hP s hs).1 F hF
    have hcr : (F.card:ℝ) ≤ (k+1:ℝ)^d.primeFactorsList.length*
        ((k:ℝ)*(k+1))^s.primeFactorsList.length := by exact_mod_cast hc
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hb : (1:ℝ) ≤ (k:ℝ)*(k+1) := by nlinarith
    have hp := Real.rpow_le_rpow_of_exponent_le hb (hP s hs).2.2
    rw [Real.rpow_natCast] at hp
    have hcard : (F.card:ℝ) ≤ W := hcr.trans
      (mul_le_mul_of_nonneg_left hp (by positivity))
    have he : (∑ t ∈ F,(factorProduct t:ℝ)⁻¹)=(F.card:ℝ)*(s:ℝ)⁻¹ := by
      calc
        _ = ∑ _t ∈ F,(s:ℝ)⁻¹ := Finset.sum_congr rfl (fun t ht => by rw [(hF t ht).1])
        _ = _ := by simp
    rw [show Q.filter (fun t => factorProduct t=s)=F from rfl,he]
    exact mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (Nat.cast_nonneg s))
  calc
    _ = ∑ s ∈ P,∑ t ∈ Q.filter (fun t => factorProduct t=s),(factorProduct t:ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun t => (factorProduct t:ℝ)⁻¹)).symm
    _ ≤ ∑ s ∈ P,W*(s:ℝ)⁻¹ := Finset.sum_le_sum hfiber
    _ = W*(∑ s ∈ P,(s:ℝ)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (smooth_residual_reciprocal_mass N P (fun s hs => ⟨(hP s hs).1,(hP s hs).2.1⟩)) hW

end TotientAsymptotic

end

end OAI
