import OAI.NumberTheory.CubicMoment.Estimates.NormFourierSeminorm

namespace OAI

/-! The fixed radial lift and trace Fourier transform form a continuous
linear operator. Thus the finite profile cost is controlled by finitely
many seminorms of the original one-dimensional cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment
open CubicPoisson

lemma normSq_hasTemperateGrowth : Function.HasTemperateGrowth Complex.normSq := by
  have he : (Complex.normSq : ℂ → ℝ) = fun z => ‖z‖^2 := funext Complex.normSq_eq_norm_sq
  rw [he]
  exact Function.hasTemperateGrowth_norm_sq ℂ

lemma normSq_polynomial_growth : ∃ (k : ℕ) (C : ℝ),
    ∀ z : ℂ, ‖z‖ ≤ C*(1+‖Complex.normSq z‖)^k := by
  refine ⟨1,1,?_⟩
  intro z
  rw [pow_one,one_mul,Real.norm_of_nonneg (Complex.normSq_nonneg z),Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖z‖-1)]

def normProfileLiftCLM : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLM ℂ normSq_hasTemperateGrowth normSq_polynomial_growth

def normProfileFourierCLM : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  (2/Real.sqrt 3:ℝ) •
    (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (Complex.conjCLE.trans (complexMulEquiv 2 (by norm_num)))).comp
      (SchwartzMap.fourierTransformCLM ℂ (V := ℂ) (E := ℂ))).comp
        normProfileLiftCLM).restrictScalars ℝ

lemma normProfileFourierCLM_apply (V : 𝓢(ℝ,ℂ)) (hV : HasCompactSupport (V : ℝ → ℂ)) :
    normProfileFourierCLM V = normProfileFourierSchwartz V hV (V.smooth ⊤) := by
  have he : normProfileLiftCLM V = normProfileSchwartz V hV (V.smooth ⊤) 1 (by norm_num) := by
    ext z
    simp only [normProfileLiftCLM,SchwartzMap.compCLM_apply,Function.comp_apply,
      normProfileSchwartz_apply,div_one]
  change (2/Real.sqrt 3 : ℝ) • traceFourierSchwartz (normProfileLiftCLM V) = _
  rw [he]
  ext z
  rfl

theorem normProfileFourier_finite_seminorm (I : Finset (ℕ × ℕ)) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ V : 𝓢(ℝ,ℂ),
      (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) (normProfileFourierCLM V) ≤
        C*(J.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) V := by
  let q : Seminorm ℝ 𝓢(ℂ,ℂ) := I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)
  have hq : Continuous q := Seminorm.continuous_finsetSup
    (fun i _ => (schwartz_withSeminorms ℝ ℂ ℂ).continuous_seminorm i)
  obtain ⟨J,C,hC,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ)
    (q.comp normProfileFourierCLM.toLinearMap) (hq.comp normProfileFourierCLM.continuous)
  refine ⟨J,C,NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC),?_⟩
  intro V
  exact Seminorm.le_def.mp hb V

end CubicFirstMoment

end

end OAI
