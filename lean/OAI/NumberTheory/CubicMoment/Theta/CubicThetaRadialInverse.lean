import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInversePoleMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHarmonic

namespace OAI

/-! The literal radial Gauss sum inherits the proved two-sided mean by
finite inverse completion. The pole contributes its summable divisor tail. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_inverted_radial_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) (D : ℕ) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y U F T : ℝ, 1 ≤ Y → 0 < U → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ U → U ≤ Y^B →
      Real.exp h.radius*U ≤ F → F ≤ Y^B →
      ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖)+
        (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖))/T ≤
          K*Real.sqrt U*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
            E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  have hS : 1 ≤ Real.exp h.radius := Real.one_le_exp h.radius_nonneg
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨K,E,hK,hE,hcompleted⟩ :=
    h.cubicTheta_completed_signed_radial_mean hMV hM hhalf
      (show 0 ≤ 4*B by positivity) D
  let α : ℝ := η/(2*(B+1))
  have hα : 0 < α := by dsimp [α]; positivity
  have hαB : B*α ≤ η/2 := by
    have he := div_mul_cancel₀ η (show 2*(B+1) ≠ 0 by positivity)
    change α*(2*(B+1)) = η at he
    nlinarith
  obtain ⟨C,hC,harmonic⟩ := primary_finite_harmonic_power hα
  let S : ℝ := ∑' c : Eisenstein, norm c^(-2:ℝ)
  have hSn : 0 ≤ S := tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _)
  refine ⟨K*C,E*S,mul_nonneg hK hC.le,mul_nonneg hE hSn,?_⟩
  intro i r hr hsr Y U F T hY hU hT hRY hTY hUlo hUhi hSF hFY
  have hYp := zero_lt_one.trans_le hY
  have hTp := zero_lt_one.trans_le hT
  have hRp := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hFp : 0 < F := (mul_pos (zero_lt_one.trans_le hS) hU).trans_le hSF
  have hB4 : B ≤ 4*B := by linarith
  have hRY4 : norm r ≤ Y^(4*B) := hRY.trans (Real.rpow_le_rpow_of_exponent_le hY hB4)
  have hTY4 : T ≤ Y^(4*B) := hTY.trans (Real.rpow_le_rpow_of_exponent_le hY hB4)
  let H : ℝ := K*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T
  let J : ℝ := E*norm r^(-1/6:ℝ)/T^D
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hmean (c : Eisenstein) (hc : c ∈ primaryElementBall F) :
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 (W i) (U/norm c^3) t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 (W i) (U/norm c^3) t‖))/T ≤
          H*Real.sqrt (U/norm c^3)+J*(U/norm c^3)^(5/6:ℝ) := by
    obtain ⟨hcp,hcF⟩ := mem_primaryElementBall.mp hc
    obtain ⟨hX,hXlo,hXhi⟩ := metaplectic_inverse_length_range hY hB hUlo hUhi
      (one_le_norm (primary_ne_zero hcp)) (hcF.trans hFY)
    exact (hcompleted i r hr hsr Y (U/norm c^3) T hY hX hT
      hRY4 hTY4 hXlo hXhi).trans_eq (by dsimp [H,J]; ring)
  have hi := metaplectic_inverse_signed_mean_with_pole r (W i) (h.compact i) hU
    (zero_le_one.trans hS) hSF (h.upper_support i) hTp hmean
  have hs : (∑ c ∈ primaryElementBall F, norm c^(-1:ℝ)) ≤ C*Y^(η/2) := by
    apply (harmonic (primaryElementBall F) F hFp
      (fun c hc => (mem_primaryElementBall.mp hc).1)
      (fun c hc => (mem_primaryElementBall.mp hc).2)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    calc
      _ ≤ (Y^B)^α := Real.rpow_le_rpow hFp.le hFY hα.le
      _ = Y^(B*α) := (Real.rpow_mul hYp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hαB
  have hy : Y^(η/2)*Y^(η/2) = Y^η := by rw [←Real.rpow_add hYp]; congr 1; ring
  calc
    _ ≤ H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ))+
        J*U^(5/6:ℝ)*(∑ c ∈ primaryElementBall F, norm c^(-2:ℝ)) := hi
    _ ≤ H*Real.sqrt U*(C*Y^(η/2))+J*U^(5/6:ℝ)*S :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_le_mul_of_nonneg_left (primary_inverse_square_sum_bound F) (by positivity))
    _ = (K*C*Real.sqrt U*norm r^(1/4:ℝ)*Real.sqrt T)*(Y^(η/2)*Y^(η/2))+
        (E*S)*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by dsimp [H,J]; ring
    _ = _ := by rw [hy]; ring

end CubicFirstMoment

end

end OAI
