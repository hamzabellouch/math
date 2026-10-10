import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLowPowers
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInverseScale
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalFinite
import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-! The short part of inverse completion. The same actual error sum
serves the radial and every fixed angular Type-I argument. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticShortCompletionError (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U C : ℝ) : ℂ :=
  ∑ c ∈ primaryElementBall C,
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
      (metaplecticCompleted r ℓ W (U/norm c^3)-metaplecticMain r ℓ W (U/norm c^3))

lemma primary_sqrt_norm_mass {C : ℝ} (hC : 0 ≤ C) :
    (∑ c ∈ primaryElementBall C, Real.sqrt (norm c)) ≤ 18*C^(3/2:ℝ) := by
  have hsub : primaryElementBall C ⊆ nonzeroNormBall C := by
    intro c hc
    obtain ⟨hp,hn⟩ := mem_primaryElementBall.mp hc
    exact mem_nonzeroNormBall.mpr ⟨hn,primary_ne_zero hp⟩
  have hcard : ((primaryElementBall C).card:ℝ) ≤ 18*C :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hC)
  calc
    _ ≤ ∑ c ∈ primaryElementBall C, Real.sqrt C := Finset.sum_le_sum
      (fun c hc => Real.sqrt_le_sqrt (mem_primaryElementBall.mp hc).2)
    _ = ((primaryElementBall C).card:ℝ)*Real.sqrt C := by simp
    _ ≤ (18*C)*Real.sqrt C := mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)
    _ = _ := by
      by_cases hz : C = 0
      · simp [hz]
      · have hp : 0 < C := lt_of_le_of_ne hC (Ne.symm hz)
        rw [Real.sqrt_eq_rpow,show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hp,
          Real.rpow_one]
        ring

theorem UniformLogWeights.metaplectic_short_completion_error
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {ι : Type*} {W : ι → ℝ → ℂ} (hW : UniformLogWeights W) (ℓ : ℤ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y U C : ℝ, 1 ≤ Y → Y^(-B) ≤ U → U ≤ Y^B →
      0 ≤ C → C ≤ Y^B → norm r ≤ Y^B →
      ‖metaplecticShortCompletionError r ℓ (W i) U C‖ ≤
        K*Y^ε*Real.sqrt (norm r)*C^(3/2:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := uniform_metaplectic_completed_subpower hV hW ℓ hGamma hε
    (show 0 ≤ 4*B by positivity)
  refine ⟨18*K,by positivity,?_⟩
  intro i r hr hsr Y U C hY hUlo hUhi hC hChi hrhi
  have hrbig : norm r ≤ Y^(4*B) := hrhi.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith))
  have hc (c : Eisenstein) (hc : c ∈ primaryElementBall C) :
      ‖((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
        (metaplecticCompleted r ℓ (W i) (U/norm c^3)-
          metaplecticMain r ℓ (W i) (U/norm c^3))‖ ≤
          Real.sqrt (norm c)*(K*Y^ε*Real.sqrt (norm r)) := by
    obtain ⟨hcp,hcn⟩ := mem_primaryElementBall.mp hc
    obtain ⟨hpos,hlo,_⟩ := metaplectic_inverse_length_range hY hB hUlo hUhi
      (one_le_norm (primary_ne_zero hcp)) (hcn.trans hChi)
    rw [norm_mul]
    exact mul_le_mul (norm_metaplectic_inverse_weight r ℓ 0 hcp)
      (hbound i r hr hsr Y _ hY hpos hrbig hlo) (_root_.norm_nonneg _) (Real.sqrt_nonneg _)
  unfold metaplecticShortCompletionError
  calc
    _ ≤ ∑ c ∈ primaryElementBall C,
        Real.sqrt (norm c)*(K*Y^ε*Real.sqrt (norm r)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hc)
    _ = (∑ c ∈ primaryElementBall C, Real.sqrt (norm c))*(K*Y^ε*Real.sqrt (norm r)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (18*C^(3/2:ℝ))*(K*Y^ε*Real.sqrt (norm r)) :=
      mul_le_mul_of_nonneg_right (primary_sqrt_norm_mass hC) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
