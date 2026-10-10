import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNegativeTail
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformNegativeLong
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticNaturalCutoff
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedSubpower
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformTruncation
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformRetained

namespace OAI

/-! The uniform actual nonzero-angular long-height estimate, with
its exact primal dilation and proved coefficient bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma sqrt_level_negative_power {Y R X B : ℝ}
    (hY : 0 < Y) (hRY : R ≤ Y^B) (hYX : Y^(-B) ≤ X) :
    Real.sqrt R*Y^(-B) ≤ Real.sqrt X := by
  have he : Real.sqrt (Y^B)*Y^(-B) = Real.sqrt (Y^(-B)) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hY.le,
      ←Real.rpow_add hY,←Real.rpow_mul hY.le]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (Y^B)*Y^(-B) := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hRY) (Real.rpow_nonneg hY.le _)
    _ = Real.sqrt (Y^(-B)) := he
    _ ≤ _ := Real.sqrt_le_sqrt hYX

/-- For each small loss, the far-left line is chosen once before all
levels, lengths and heights. Its Gamma bounds are exactly the published
bounded-strip input at that chosen line. -/
theorem UniformLogWeights.cubicTheta_completed_dilated_negative_long_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ≠0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (m : ℕ) (K : ℝ), 2 ≤ m ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
      Real.sqrt (norm r)*T^2 ≤ X →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)) →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) (729*X) (-t)‖)/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  let B' := 7*B+η
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  have hBB' : B ≤ B' := by dsimp [B']; linarith
  have h7B : 7*B ≤ B' := by dsimp [B']; linarith
  have hσ : (0:ℝ) < 1/20000 := by norm_num
  obtain ⟨m,C,hm,hms,hC,htail⟩ := h.metaplectic_twisted_tail_arbitrary_power cubicThetaCoreCoefficient_bounds ℓ hσ hη B' B
  obtain ⟨D,hD,hret⟩ := h.metaplectic_retained_negative_voronoi_subpower cubicThetaCoreCoefficient_bounds hMV hM ℓ (div_pos hη (by norm_num : (0:ℝ) < 2)) hB'
  let P := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨m,81*(4*D+C/P),hm,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hlong hgm hgp
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hR1 := one_le_norm (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let J := metaplecticNaturalCutoff Y (norm r) T X η
  have hJ1 : 1 ≤ J := metaplecticNaturalCutoff_ge_one _ _ _ _ _
  have hJ : 0 < J := zero_lt_one.trans_le hJ1
  have hJY : J ≤ Y^B' := metaplecticNaturalCutoff_polynomial hY hR hTp hB hη.le hRY hTY hYX
  have hRY' : norm r ≤ Y^B' := hRY.trans (Real.rpow_le_rpow_of_exponent_le hY hBB')
  have hTY' : T ≤ Y^B' := hTY.trans (Real.rpow_le_rpow_of_exponent_le hY hBB')
  have hDY : norm r^2*T^4/X ≤ Y^B' :=
    (metaplectic_natural_length_polynomial hY hR hTp hRY hTY hYX).trans
      (Real.rpow_le_rpow_of_exponent_le hY h7B)
  have hcut : (norm r^2*T^4/X)/J ≤ Y^(-η) := metaplecticNaturalCutoff_ratio hYp
  have ht (t : ℝ) (htt : |t| ≤ 2*T) :
      ‖∑' nd, metaplecticFarTailTerm cubicThetaCoreCoefficient r ℓ (fun x => W i x*mellinPhase t x)
        ((m:ℝ)-1/2) X J nd‖ ≤ C*Y^(-B) :=
    htail i r hr hsr Y X J T hY hX hJ hT hRY' hTY' hDY hcut t htt
  have ha : 0 ≤ (m:ℝ)-1/2 := hσ.le.trans hms
  have hscale : (729*X)/729=X := by ring
  have hb := cubicTheta_completed_negative_tail_mean hr hsr hℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
    (X:=729*X) (by positivity) (hσ.trans_le hms) hTp hgm hgp
    (by simpa only [hscale] using ht)
  simp only [hscale] at hb
  have hv := hret i r hr hsr Y ((m:ℝ)-1/2) X J T hY ha hX hJ1 hTp hRY' hJY hgm hgp
  have hg := metaplectic_long_sqrt_factor hY hR1 hT hη.le
    (metaplectic_long_cutoff hY hR1 hT hX hη.le hlong)
  change 1+Real.sqrt (4*J/(norm r*T)) ≤ _ at hg
  have hyprod : Y^(η/2)*Y^(η/2) = Y^η := by rw [←Real.rpow_add hYp]; congr 1; ring
  have hmain : (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
      ∑ nd ∈ metaplecticDualBall J,
        metaplecticDualTerm cubicThetaCoreCoefficient r ℓ (fun x => W i x*mellinPhase (-t) x) ((m:ℝ)-1/2) X nd‖)/T ≤
        4*D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
    apply hv.trans
    calc
      _ ≤ D*Real.sqrt X*Y^(η/2)*(4*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T) := by gcongr
      _ = _ := by
        rw [show D*Real.sqrt X*Y^(η/2)*(4*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T) =
          4*D*Real.sqrt X*(Y^(η/2)*Y^(η/2))*norm r^(1/4:ℝ)*Real.sqrt T by ring,hyprod]
  have hf : 1 ≤ Y^η*norm r^(1/4:ℝ)*Real.sqrt T :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hY hη.le)
        (Real.one_le_rpow hR1 (by norm_num))) (Real.one_le_sqrt.mpr hT)
  have htailbound : ‖metaplecticPrefactor r ℓ‖*(C*Y^(-B)) ≤
      C/P*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
    rw [norm_metaplecticPrefactor (primary_ne_zero hr)]
    calc
      _ = C/P*(Real.sqrt (norm r)*Y^(-B)) := by dsimp [P]; ring
      _ ≤ C/P*Real.sqrt X := mul_le_mul_of_nonneg_left
        (sqrt_level_negative_power hYp hRY hYX) (by positivity)
      _ ≤ (C/P*Real.sqrt X)*(Y^η*norm r^(1/4:ℝ)*Real.sqrt T) :=
        le_mul_of_one_le_right (by positivity) hf
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ 81*(4*D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
        C/P*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain htailbound) (by norm_num)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
