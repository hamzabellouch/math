import OAI.NumberTheory.CubicMoment.Estimates.LogCellBilinear
import OAI.NumberTheory.CubicMoment.Estimates.NearLogNormCells
import OAI.NumberTheory.CubicMoment.Estimates.HeightSquareRoot
import OAI.NumberTheory.CubicMoment.Estimates.HeightPoissonDyadic

namespace OAI

/-! Summation of the actual near-boundary cell polynomials, preserving the
thin diagonal and the proved derivative cost in the dispersion remainder. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def logCellPolynomial (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B : ℝ) (e : ℤ × ℤ) (u : ℝ) : ℂ :=
  ∑ a ∈ logNormCellSupport P J A e.1, ∑ b ∈ logNormCellSupport S J B e.2,
    α a*β b*gauss (a*b)*normTwist u (a*b)

lemma logCellPolynomial_continuous (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B : ℝ) (e : ℤ × ℤ) : Continuous (logCellPolynomial P S α β J A B e) := by
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul (continuous_normTwist (a*b))

theorem near_logCell_height_bound
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A B X₀ T u : ℝ),
      65536 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < B → 0 < X₀ → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖∑ e ∈ nearLogNormCells P S J A B X₀,
        logCellPolynomial P S α β J A B e (u+t)‖) T ≤
        K*(Real.sqrt (A/J)+Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)))*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨d,K,hK,hcell⟩ := logCell_bilinear_height_square hMV hC hHuxley
  refine ⟨d,10*Real.sqrt K,by positivity,?_⟩
  intro J hJ P S α β Z A B X₀ T u hZ hA hB hX hT hP hS
  have hZp : 0 < Z := by linarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  let E := nearLogNormCells P S J A B X₀
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  let b := fun j => Real.sqrt (∑ n ∈ logNormCellSupport S J B j, ‖β n‖^2)
  let H := 2*Real.sqrt K*(Real.sqrt (A/J)+
    Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)))
  have hF (e : ℤ × ℤ) : Continuous
      (fun t : ℝ => logCellPolynomial P S α β J A B e (u+t)) :=
    (logCellPolynomial_continuous P S α β J A B e).comp
      (continuous_const.add continuous_id)
  have hh (e : ℤ × ℤ) (he : e ∈ E) :
      dyadicHeightMean (fun t => ‖logCellPolynomial P S α β J A B e (u+t)‖) T ≤
        H*a e.1*b e.2 := by
    have hi : e.1 ∈ P.image (logNormCell J A) :=
      (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    exact height_cell_square_root (hF e) hTp hK.le (by positivity) (by positivity)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (hcell J hJ P S α β Z A B T u hZ hA hT hP hS e.1 hi e.2)
  have hsum := dyadicHeightMean_norm_sum_le E
    (fun e t => logCellPolynomial P S α β J A B e (u+t)) (fun e _ => hF e) hTp
  apply (hsum.trans (Finset.sum_le_sum hh)).trans
  have hnear := nearLogNormCells_energy_bound P S (fun a ha => (hP a ha).1)
    (fun b hb => (hS b hb).1) α β J hAp hB hX
  calc
    (∑ e ∈ E, H*a e.1*b e.2) = H*(∑ e ∈ E, a e.1*b e.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ H*(5*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)) :=
      mul_le_mul_of_nonneg_left hnear (by dsimp [H]; positivity)
    _ = _ := by dsimp [H]; ring

end CubicFirstMoment

end

end OAI
