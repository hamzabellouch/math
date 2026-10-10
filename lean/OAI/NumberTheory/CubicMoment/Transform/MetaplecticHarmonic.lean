import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSupportedSum

namespace OAI

/-! The finite d-sum in the retained angular estimate costs an
arbitrarily small power of its cutoff. The proof uses the already proved
convergent Eisenstein norm series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primary_finite_harmonic_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (J : ℝ), 0 < J →
      (∀ d ∈ S, primary d) → (∀ d ∈ S, norm d ≤ J) →
      (∑ d ∈ S, norm d^(-1:ℝ)) ≤ C*J^ε := by
  have hs : Summable (fun d : Eisenstein => norm d^(-1-ε)) := by
    convert summable_eisenstein_norm_rpow (s := 1+ε) (by linarith) using 1
    ext d
    congr 1
    ring
  let M : ℝ := ∑' d : Eisenstein, norm d^(-1-ε)
  have hM : 0 ≤ M := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  refine ⟨M+1,by linarith,?_⟩
  intro S J hJ hS hbound
  have hp (d : Eisenstein) (hd : d ∈ S) :
      norm d^(-1:ℝ) ≤ J^ε*norm d^(-1-ε) := by
    have hn := norm_pos_of_ne_zero (primary_ne_zero (hS d hd))
    calc
      _ = norm d^ε*norm d^(-1-ε) := by rw [←Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hn.le (hbound d hd) hε.le)
        (Real.rpow_nonneg hn.le _)
  calc
    _ ≤ ∑ d ∈ S, J^ε*norm d^(-1-ε) := Finset.sum_le_sum hp
    _ = J^ε*(∑ d ∈ S, norm d^(-1-ε)) := (Finset.mul_sum _ _ _).symm
    _ ≤ J^ε*M := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum S (fun d _ => Real.rpow_nonneg (norm_nonneg d) _))
      (Real.rpow_nonneg hJ.le _)
    _ ≤ (M+1)*J^ε := by nlinarith [Real.rpow_nonneg hJ.le ε]

end CubicFirstMoment

end

end OAI
