import OAI.NumberTheory.CubicMoment.Estimates.ThinCellNormalized
import OAI.NumberTheory.CubicMoment.Estimates.SmallBBilinearLog

namespace OAI

/-! Absorb logarithmic coefficient energies in the thin-cell power saving. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem thinCell_bilinear_log_saving
    {C Mα Mβ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (j dα dβ : ℕ) :
    ∃ (γ K : ℝ), 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(2-1/80000:ℝ) ≤ A → A ≤ Z^(2+γ) → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ 1+1/(4*Z^γ) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*Z^γ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨γ,K,hγ,hK,hbound⟩ := thinCell_bilinear_normalized hMV hC hHuxley
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound (2*j+dα+dβ)
    (s := 2*γ/3) (by positivity)
  refine ⟨γ,2*(Real.sqrt (Mα*(K*Mβ*H))+1),hγ,by positivity,?_⟩
  intro P S α β Z A T u hZ hA hAupper hT hP hS hα hβ
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  let L := 1+Real.log Z
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hZ1]
  let E := ∑ a ∈ P, ‖α a‖^2
  let V := K*A^(2/3:ℝ)*Z^(2/3-2*γ/3)*∑ b ∈ S, ‖β b‖^2
  let f := fun t => ∑ a ∈ P, ∑ b ∈ S,
    α a*β b*gauss (a*b)*normTwist (u+t) (a*b)
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp (continuous_const.add continuous_id))
  have herror : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ E*V := by
    apply (hbound P S α β Z A T u hZ hA hAupper hT hP hS).trans_eq
    dsimp [E,V]
    ring
  have hmass : V ≤ (K*Mβ*H)*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    have hz : Z^(2/3-2*γ/3)*Z = Z^(5/3-2*γ/3) := by
      nth_rw 2 [←Real.rpow_one Z]
      rw [←Real.rpow_add hZp]
      congr 1
      ring
    have hh := smallB_nondiagonal_log_scale hAp.le hZp hL (2*j+dα) dβ (hlog Z hZ1)
    calc
      V ≤ K*A^(2/3:ℝ)*Z^(2/3-2*γ/3)*(Mβ*Z*L^dβ) :=
        mul_le_mul_of_nonneg_left hβ (by positivity)
      _ = (K*Mβ)*(A^(2/3:ℝ)*Z^(5/3-2*γ/3)*L^dβ) := by rw [←hz]; ring
      _ ≤ (K*Mβ)*(H*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα)) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg hK.le hMβ)
      _ = _ := by ring
  exact height_bilinear_error_log_saving hf hTp hMα (by positivity)
    hAp hZp hL j dα (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (by dsimp [V]; positivity) herror hα hmass

end CubicFirstMoment

end

end OAI
