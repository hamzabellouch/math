import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortLogInverse
import OAI.NumberTheory.CubicMoment.Estimates.TypeIFinal

namespace OAI

/-! The actual short inverse-completion error after summing the level
coefficients. This is the common radial/angular short-error term. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma short_completion_level_scale {R : ℝ} (hR : 0 < R) :
    R*Real.sqrt (2*R) = Real.sqrt 2*R^(3/2:ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp_rw [Real.sqrt_eq_rpow]
  rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hR,Real.rpow_one]
  ring

theorem LogarithmicWeightFamily.metaplectic_short_outer_error
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W) (ℓ : ℤ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) (d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset ι) (α : ι → ℂ) (r : ι → Eisenstein)
      (R U C : ℝ), 1 ≤ R → 1 ≤ U → 0 ≤ C →
      (∀ i ∈ S, primary (r i) ∧ Squarefree (r i) ∧ norm (r i) ≤ 2*R) →
      (∀ i ∈ S, Y i ≤ R*U ∧ (Y i)^(-B) ≤ U ∧ U ≤ (Y i)^B ∧
        C ≤ (Y i)^B ∧ norm (r i) ≤ (Y i)^B) →
      (∑ i ∈ S, ‖α i‖) ≤ A*R*(Real.log (R*U))^d →
      ‖∑ i ∈ S, α i*metaplecticShortCompletionError (r i) ℓ (W i) U C‖ ≤
        K*(R*U)^η*R^(3/2:ℝ)*C^(3/2:ℝ) := by
  have hδ : 0 < η/2 := half_pos hη
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_short_completion_error hV ℓ hGamma hδ hB
  obtain ⟨D,hD,hlog⟩ := typeI_log_power_bound d hδ
  refine ⟨Real.sqrt 2*K*A*D,by positivity,?_⟩
  intro S α r R U C hR hU hC hr hy hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  have hXp : 0 < R*U := by positivity
  let M := K*(R*U)^(η/2)*Real.sqrt (2*R)*C^(3/2:ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (i : ι) (hi : i ∈ S) :
      ‖metaplecticShortCompletionError (r i) ℓ (W i) U C‖ ≤ M := by
    obtain ⟨hp,hs,hn⟩ := hr i hi
    obtain ⟨hYi,hlo,hhi,hCi,hri⟩ := hy i hi
    have hi0 : 0 ≤ Y i := (zero_lt_one.trans_le (hW.length_one i)).le
    apply (hbound i (r i) hp hs U C hlo hhi hC hCi hri).trans
    dsimp [M]
    gcongr
  calc
    _ ≤ ∑ i ∈ S, ‖α i‖*‖metaplecticShortCompletionError (r i) ℓ (W i) U C‖ := by
      simpa only [norm_mul] using
        norm_sum_le S (fun i => α i*metaplecticShortCompletionError (r i) ℓ (W i) U C)
    _ ≤ ∑ i ∈ S, ‖α i‖*M := Finset.sum_le_sum
      (fun i hi => mul_le_mul_of_nonneg_left (hb i hi) (_root_.norm_nonneg _))
    _ = (∑ i ∈ S, ‖α i‖)*M := (Finset.sum_mul S _ M).symm
    _ ≤ (A*R*(Real.log (R*U))^d)*M := mul_le_mul_of_nonneg_right hα hM
    _ = (K*A)*(R*U)^(η/2)*(Real.log (R*U))^d*(R*Real.sqrt (2*R))*C^(3/2:ℝ) := by
      dsimp [M]
      ring
    _ ≤ (K*A)*(R*U)^(η/2)*(D*(R*U)^(η/2))*(R*Real.sqrt (2*R))*C^(3/2:ℝ) := by
      gcongr
      exact hlog _ hX
    _ = _ := by
      rw [short_completion_level_scale hRp]
      have he : (R*U)^(η/2)*(R*U)^(η/2) = (R*U)^η := by
        rw [←Real.rpow_add hXp,show η/2+η/2 = η by ring]
      calc
        _ = (Real.sqrt 2*K*A*D)*((R*U)^(η/2)*(R*U)^(η/2))*R^(3/2:ℝ)*C^(3/2:ℝ) := by ring
        _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
