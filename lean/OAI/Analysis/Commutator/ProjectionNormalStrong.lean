import Mathlib
import OAI.Analysis.Commutator.ProjectionNormalPositive

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma functional_cauchySchwarz (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (a : M) :
    ‖f a‖^2≤(f 1).re*(f (star a*a)).re := by
  have hi := norm_inner_le_norm (𝕜:=ℂ) (f.toPreGNS 1) (f.toPreGNS a)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
  have he (b : M) : ‖f.toPreGNS b‖^2=(f (star b*b)).re := by
    rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
    rfl
  rw [mul_pow,he 1,he a] at hs
  simpa only [f.preGNS_inner_def,f.ofPreGNS_toPreGNS,star_one,one_mul] using hs

theorem contraction_strong_null [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (T : ℕ → M) (hT : ∀ n,‖T n‖≤1)
    (ht : ∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    Tendsto (fun n => f (T n)) atTop (𝓝 0) := by
  have hpos (n : ℕ) : (0:M)≤ star (T n)*T n := star_mul_self_nonneg _
  have hnorm (n : ℕ) : ‖star (T n)*T n‖≤1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (T n),hT n]
  have hone (n : ℕ) : star (T n)*T n≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos n)).mp (hnorm n)
  have hs (x : H) : Tendsto (fun n => ((star (T n)*T n : M) : H →L[ℂ] H) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ ((ht x).norm.trans (by simp))
    intro n
    change ‖(star (T n) : H →L[ℂ] H) ((T n : H →L[ℂ] H) x)‖≤_
    calc
      _ ≤ ‖(star (T n) : H →L[ℂ] H)‖*‖(T n : H →L[ℂ] H) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖(T n : H →L[ℂ] H) x‖ := mul_le_mul_of_nonneg_right
        (by simpa using hT n) (norm_nonneg _)
      _ = _ := one_mul _
  have hlim := positive_strong_null M f hf (fun n => star (T n)*T n) hpos hone hs
  have hre : Tendsto (fun n => (f 1).re*(f (star (T n)*T n)).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.zero_re,mul_zero] using
      (Complex.continuous_re.tendsto 0 |>.comp hlim).const_mul (f 1).re
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hre.eventually_lt_const (sq_pos_of_pos hε))
  refine ⟨N,?_⟩
  intro n hn
  have hc := functional_cauchySchwarz M f (T n)
  have hh := hN n hn
  have hl : ‖f (T n)‖<ε := by nlinarith [norm_nonneg (f (T n))]
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using hl

end Kadison.PositiveWOT

end

end
end

end OAI
