import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortInverse
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! The short inverse-completion error for the original logarithmically
varying weights, in both the radial and fixed angular modes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCompleted_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    metaplecticCompleted r ℓ (fun x => z*W x) U = z*metaplecticCompleted r ℓ W U := by
  unfold metaplecticCompleted
  rw [←tsum_mul_left]
  apply tsum_congr
  intro du
  by_cases hc : IsCoprime (du.1:Eisenstein) r
  · simp only [hc,ite_true]
    ring
  · simp only [hc,ite_false,mul_zero]

lemma metaplecticMain_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    metaplecticMain r ℓ (fun x => z*W x) U = z*metaplecticMain r ℓ W U := by
  have hm : mellin (fun x => z*W x) (5/6) = z*mellin W (5/6) := by
    simpa only [smul_eq_mul] using mellin_const_smul W (5/6) z
  unfold metaplecticMain
  split_ifs
  · rw [hm]
    ring
  · exact (mul_zero _).symm

lemma metaplecticShortCompletionError_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U C : ℝ) (z : ℂ) :
    metaplecticShortCompletionError r ℓ (fun x => z*W x) U C =
      z*metaplecticShortCompletionError r ℓ W U C := by
  unfold metaplecticShortCompletionError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [metaplecticCompleted_const_mul,metaplecticMain_const_mul]
  ring

theorem LogarithmicWeightFamily.metaplectic_short_completion_error
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W) (ℓ : ℤ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ U C : ℝ, (Y i)^(-B) ≤ U → U ≤ (Y i)^B →
      0 ≤ C → C ≤ (Y i)^B → norm r ≤ (Y i)^B →
      ‖metaplecticShortCompletionError r ℓ (W i) U C‖ ≤
        K*(Y i)^ε*Real.sqrt (norm r)*C^(3/2:ℝ) := by
  have hs : 0 < ε/2 := half_pos hε
  obtain ⟨K,hK,hbound⟩ := (hW.normalize hs).metaplectic_short_completion_error hV ℓ hGamma hs hB
  refine ⟨K,hK,?_⟩
  intro i r hr hsr U C hUlo hUhi hC hChi hrhi
  have hY : 0 < Y i := zero_lt_one.trans_le (hW.length_one i)
  have he : metaplecticShortCompletionError r ℓ (normalizedLogWeight Y W (ε/2) i) U C =
      (((Y i)^(-(ε/2)):ℝ):ℂ)*metaplecticShortCompletionError r ℓ (W i) U C := by
    change metaplecticShortCompletionError r ℓ (fun x => ((Y i)^(-(ε/2)):ℝ) • W i x) U C = _
    simp_rw [Complex.real_smul]
    exact metaplecticShortCompletionError_const_mul r ℓ (W i) U C _
  have hb := hbound i r hr hsr (Y i) U C (hW.length_one i) hUlo hUhi hC hChi hrhi
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^(ε/2)*(Y i)^(-(ε/2)) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^(ε/2)*((Y i)^(-(ε/2))*‖metaplecticShortCompletionError r ℓ (W i) U C‖) := by
      rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^(ε/2)*(K*(Y i)^(ε/2)*Real.sqrt (norm r)*C^(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = K*((Y i)^(ε/2)*(Y i)^(ε/2))*Real.sqrt (norm r)*C^(3/2:ℝ) := by ring
    _ = _ := by rw [←Real.rpow_add hY,show ε/2+ε/2 = ε by ring]

end CubicFirstMoment

end

end OAI
