import OAI.NumberTheory.CubicMoment.Estimates.LowLogCellBilinear
import OAI.NumberTheory.CubicMoment.Estimates.LowHeightSquareRoot
import OAI.NumberTheory.CubicMoment.Estimates.LowCellMass
import OAI.NumberTheory.CubicMoment.Estimates.LogCellNearHeight

namespace OAI

/-! The near-cell diagonal is summed with the degree-five incidence
bound. Only the logarithmically small remainder pays the cell-count cost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem low_near_logCell_height_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖∑ e ∈ nearLogNormCells P S J A (Z/2) X₀,
        logCellPolynomial P S α β J A (Z/2) e (u+t)‖) T ≤
      K*(Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨d,hfamily⟩ := low_logCell_bilinear_height_square hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hcell⟩ := hfamily q
  refine ⟨10*Real.sqrt K,Ct,by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M u hZ hA hX hT hM hP hS hβ
  have hJ1 : 1 ≤ J := by linarith
  have hZp : 0 < Z := by nlinarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hTp : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) _).trans_le hT
  let E := nearLogNormCells P S J A (Z/2) X₀
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  let b := fun j => Real.sqrt (∑ n ∈ logNormCellSupport S J (Z/2) j, ‖β n‖^2)
  let R := J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q
  let H₁ := 2*Real.sqrt K*Real.sqrt (A/J)
  let H₂ := 2*Real.sqrt K*Real.sqrt R
  have hF (e : ℤ × ℤ) : Continuous
      (fun t : ℝ => logCellPolynomial P S α β J A (Z/2) e (u+t)) :=
    (logCellPolynomial_continuous P S α β J A (Z/2) e).comp
      (continuous_const.add continuous_id)
  have hh (e : ℤ × ℤ) (he : e ∈ E) :
      dyadicHeightMean (fun t => ‖logCellPolynomial P S α β J A (Z/2) e (u+t)‖) T ≤
        H₁*a e.1*b e.2+H₂*a e.1 := by
    have hi : e.1 ∈ P.image (logNormCell J A) :=
      (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    have hb := height_mixed_square_root (hF e) hTp hK.le (by positivity)
      (show 0 ≤ R by dsimp [R]; positivity)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (hcell J hJ P S α β Z A (Z/2) T M u hZ hA hT hM hP hS hβ e.1 hi e.2)
    convert hb using 1
    dsimp [H₁,H₂,a,b]
    ring
  have hs := dyadicHeightMean_norm_sum_le E
    (fun e t => logCellPolynomial P S α β J A (Z/2) e (u+t)) (fun e _ => hF e) hTp
  have hn := nearLogNormCells_energy_bound P S (fun a ha => (hP a ha).1)
    (fun b hb => (hS b hb).1) α β J hAp (by positivity : 0 < Z/2) hX
  have hl := dyadic_logCell_left_mass P S hJ1 (fun a ha => (hP a ha).2)
    (fun b hb => ⟨(le_div_iff₀ (by positivity : 0 < Z/2)).mpr (by simpa using (hS b hb).2.2.1),
      (div_le_iff₀ (by positivity : 0 < Z/2)).mpr (by nlinarith [(hS b hb).2.2.2])⟩)
    E (Finset.filter_subset _ _) α
  apply (hs.trans (Finset.sum_le_sum hh)).trans
  calc
    _ = H₁*(∑ e ∈ E, a e.1*b e.2)+H₂*(∑ e ∈ E, a e.1) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_assoc]
    _ ≤ H₁*(5*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2))+
        H₂*(4*J^2*Real.sqrt (∑ a ∈ P, ‖α a‖^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hn (by dsimp [H₁]; positivity))
        (mul_le_mul_of_nonneg_left hl (by dsimp [H₂]; positivity))
    _ ≤ _ := by
      dsimp [H₁,H₂,R]
      have hnon : 0 ≤ Real.sqrt K*J^2*
          Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2) := by positivity
      nlinarith only [hnon]

end CubicFirstMoment

end

end OAI
