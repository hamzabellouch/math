import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInverseMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformAngular
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHarmonic

namespace OAI

/-! The signed-height estimate for the original angular Gauss sum.
Both its completion and its inverse have been derived. The harmonic
cube-divisor loss is absorbed by choosing its exponent first. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_inverted_angular_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {η B : ℝ}
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (mpos mneg : ℕ) (K : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y U F T : ℝ, 1 ≤ Y → 0 < U → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ U → U ≤ Y^B →
      Real.exp h.radius*U ≤ F → F ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mneg:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mneg:ℝ)-1/2)) →
      ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r ℓ (W i) U t‖)+
        (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r ℓ (W i) U t‖))/T ≤
          K*Real.sqrt U*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  have hS : 1 ≤ Real.exp h.radius := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr h.radius_nonneg
  have hhalf : 0 < η/2 := by positivity
  have h4B : 0 ≤ 4*B := by positivity
  obtain ⟨mpos,mneg,K,hmp,hmn,hK,hcompleted⟩ :=
    h.metaplectic_completed_signed_angular_mean hV hMV hM ℓ hℓ hhalf h4B
  let α : ℝ := η/(2*(B+1))
  have hα : 0 < α := by dsimp [α]; positivity
  have hαB : B*α ≤ η/2 := by
    have he := div_mul_cancel₀ η (show 2*(B+1) ≠ 0 by positivity)
    change α*(2*(B+1)) = η at he
    nlinarith
  obtain ⟨C,hC,harmonic⟩ := primary_finite_harmonic_power hα
  refine ⟨mpos,mneg,K*C,hmp,hmn,mul_nonneg hK hC.le,?_⟩
  intro i r hr hsr Y U F T hY hU hT hRY hTY hUlo hUhi hSF hFY hgmpos hgppos hgmneg hgpneg
  have hYp := zero_lt_one.trans_le hY
  have hTp := zero_lt_one.trans_le hT
  have hRp := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hFp : 0 < F := (mul_pos (zero_lt_one.trans_le hS) hU).trans_le hSF
  have hB4 : B ≤ 4*B := by linarith
  have hRY4 : norm r ≤ Y^(4*B) := hRY.trans (Real.rpow_le_rpow_of_exponent_le hY hB4)
  have hTY4 : T ≤ Y^(4*B) := hTY.trans (Real.rpow_le_rpow_of_exponent_le hY hB4)
  let H : ℝ := K*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hmean (c : Eisenstein) (hc : c ∈ primaryElementBall F) :
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ (W i) (U/norm c^3) t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) (U/norm c^3) t‖))/T ≤
          H*Real.sqrt (U/norm c^3) := by
    obtain ⟨hcp,hcF⟩ := mem_primaryElementBall.mp hc
    obtain ⟨hX,hXlo,hXhi⟩ := metaplectic_inverse_length_range hY hB hUlo hUhi
      (one_le_norm (primary_ne_zero hcp)) (hcF.trans hFY)
    have hb := hcompleted i r hr hsr Y (U/norm c^3) T hY hX hT
      hRY4 hTY4 hXlo hXhi hgmpos hgppos hgmneg hgpneg
    apply hb.trans_eq
    dsimp [H]
    ring
  have hi := metaplectic_inverse_signed_mean r ℓ (W i) (h.compact i) hU
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
    _ ≤ H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ)) := hi
    _ ≤ H*Real.sqrt U*(C*Y^(η/2)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hH (Real.sqrt_nonneg _))
    _ = (K*C*Real.sqrt U*norm r^(1/4:ℝ)*Real.sqrt T)*(Y^(η/2)*Y^(η/2)) := by
      dsimp [H]
      ring
    _ = _ := by rw [hy]; ring

end CubicFirstMoment

end

end OAI
