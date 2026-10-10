import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedGrowth
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRegularMellin

namespace OAI

/-! Uniform polynomial height bounds for the regularized scale integral.
The cutoff and the vanishing near zero are explicit. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticHeightTest (t : ℝ) (x : ℝ) : ℂ :=
  normPartitionWeight x*mellinPhase t x

lemma metaplecticHeightTest_compact (t : ℝ) : HasCompactSupport (metaplecticHeightTest t) :=
  phaseWeight_compact normPartitionWeight_compact t

lemma metaplecticHeightTest_positive (t : ℝ) : tsupport (metaplecticHeightTest t) ⊆ Ioi 0 :=
  phaseWeight_positive normPartitionWeight_positive_support t

lemma metaplecticHeightTest_smooth (t : ℝ) : ContDiff ℝ ∞ (metaplecticHeightTest t) :=
  phaseWeight_smooth normPartitionWeight_positive_support normPartitionWeight_smooth t

lemma metaplecticHeightTest_mellin (t : ℝ) (s : ℂ) :
    mellin (metaplecticHeightTest t) s = mellin normPartitionWeight (s+(t:ℂ)*Complex.I) :=
  mellin_mul_phase normPartitionWeight s t

lemma metaplecticRegularHeight_zero {X : ℝ} (hX : 0 < X) (hXsmall : X < 1/2)
    (r : Eisenstein) (t : ℝ) :
    metaplecticRegularScale r (metaplecticHeightTest t) X = 0 := by
  have hz := metaplecticCompleted_scale_small r 0 (metaplecticHeightTest t)
    (by norm_num : (0:ℝ) < 2) (fun x hx => by
      dsimp [metaplecticHeightTest]
      rw [normPartitionWeight_high hx,zero_mul]) hX hXsmall
  simp only [metaplecticRegularScale,hz,normPartitionStep_zero (by linarith : X ≤ 1),
    Complex.ofReal_zero,mul_zero,sub_zero]

theorem metaplecticRegularHeight_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ t : ℝ,
      ‖metaplecticRegularScale r (metaplecticHeightTest t) X‖ ≤
        C*X^(-(1/20000:ℝ))*(1+|t|)^N := by
  obtain ⟨C,N,hC,hbound⟩ := metaplecticCompleted_twisted_polynomial hV hr hsr
    normPartitionWeight normPartitionWeight_compact normPartitionWeight_positive_support
    normPartitionWeight_smooth (by norm_num : (0:ℝ) < 1/20000) (by norm_num)
  obtain ⟨M,hM,hMW⟩ := smooth_mellin_vertical_decay normPartitionWeight
    normPartitionWeight_compact normPartitionWeight_positive_support normPartitionWeight_smooth
    (5/6) 0
  let D : ℝ := ‖metaplecticCompletedResidue r‖*M*(4/3:ℝ)^((5/6:ℝ)+1/20000)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C+D,N,add_nonneg hC hD,?_⟩
  intro X hX t
  have hMWt : ‖mellin (metaplecticHeightTest t) (5/6)‖ ≤ M := by
    rw [metaplecticHeightTest_mellin]
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_ofNat] using hMW t
  have he : metaplecticRegularScale r (metaplecticHeightTest t) X =
      (metaplecticCompleted r 0 (metaplecticHeightTest t) X-
        metaplecticMain r 0 (metaplecticHeightTest t) X)+
      metaplecticCompletedResidue r*mellin (metaplecticHeightTest t) (5/6)*
        ((X^(5/6:ℝ):ℝ):ℂ)*(1-(normPartitionStep X:ℂ)) := by
    rw [metaplecticMain_zero_mode]
    dsimp [metaplecticRegularScale]
    ring
  have hstep : ‖1-(normPartitionStep X:ℂ)‖ ≤ 1 := by
    have h0 := Real.smoothTransition.nonneg (3*(X-1))
    have h1 := Real.smoothTransition.le_one (3*(X-1))
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by simpa only [normPartitionStep] using sub_nonneg.mpr h1)]
    dsimp [normPartitionStep]
    linarith
  have hrest : ‖metaplecticCompletedResidue r*mellin (metaplecticHeightTest t) (5/6)*
        ((X^(5/6:ℝ):ℝ):ℂ)*(1-(normPartitionStep X:ℂ))‖ ≤ D*X^(-(1/20000:ℝ)) := by
    by_cases hx : 4/3 ≤ X
    · rw [normPartitionStep_one hx,Complex.ofReal_one,sub_self,mul_zero,norm_zero]
      positivity
    · have hxp : X^(5/6:ℝ) ≤ (4/3:ℝ)^((5/6:ℝ)+1/20000)*X^(-(1/20000:ℝ)) := by
        calc
          _ = X^((5/6:ℝ)+1/20000)*X^(-(1/20000:ℝ)) := by
            rw [←Real.rpow_add hX]
            norm_num
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hX.le (le_of_not_ge hx) (by norm_num)) (by positivity)
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hX.le _)]
      calc
        _ ≤ ‖metaplecticCompletedResidue r‖*M*
            ((4/3:ℝ)^((5/6:ℝ)+1/20000)*X^(-(1/20000:ℝ)))*1 := by
          gcongr
        _ = _ := by dsimp [D]; ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hpow : 1 ≤ (1+|t|)^N := one_le_pow₀ (by linarith [abs_nonneg t])
  have hb := hbound X hX t
  change ‖metaplecticCompleted r 0 (metaplecticHeightTest t) X-
    metaplecticMain r 0 (metaplecticHeightTest t) X‖ ≤ _ at hb
  calc
    _ ≤ C*X^(-(1/20000:ℝ))*(1+|t|)^N+D*X^(-(1/20000:ℝ)) := add_le_add hb hrest
    _ ≤ C*X^(-(1/20000:ℝ))*(1+|t|)^N+D*X^(-(1/20000:ℝ))*(1+|t|)^N := by
      exact add_le_add le_rfl (le_mul_of_one_le_right
        (mul_nonneg hD (Real.rpow_nonneg hX.le _)) hpow)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
