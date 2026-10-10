import OAI.Analysis.ModularRecovery.FourierKernels

namespace OAI

/-! Strong spectral limits and orbit limits. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma tendsto_calculus_of_compact (D : RealSpectralCalculus H)
    (f : ℕ → BoundedContinuousFunction ℝ ℂ) (g : BoundedContinuousFunction ℝ ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (he : ∀ q : BoundedContinuousFunction ℝ ℂ, HasCompactSupport (q : ℝ → ℂ) →
      Tendsto (fun n => f n*q) atTop (𝓝 (g*q))) (h : H) :
    Tendsto (fun n => D.calculus (f n) h) atTop (𝓝 (D.calculus g h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨v,⟨q,hq,k,rfl⟩,hv⟩ := D.nondegenerate.exists_dist_lt h
    (show 0 < eps / (3*(C + ‖g‖ + 1)) by positivity)
  have hv' : ‖h-D.calculus q k‖ < eps / (3*(C+‖g‖+1)) := by
    simpa only [dist_eq_norm] using hv
  have hqconv : Tendsto (fun n => D.calculus (f n) (D.calculus q k)) atTop
      (𝓝 (D.calculus g (D.calculus q k))) := by
    have hc : Continuous (fun p : BoundedContinuousFunction ℝ ℂ => D.calculusCLM p k) :=
      D.calculusCLM.continuous.clm_apply continuous_const
    have ht := (hc.tendsto (g*q)).comp (he q hq)
    simpa only [Function.comp_def,calculusCLM_apply,map_mul,mul_apply_eq_comp] using ht
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hqconv (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ < eps/3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have heq : D.calculus (f n) h-D.calculus g h =
      (D.calculus (f n) (h-D.calculus q k)-D.calculus g (h-D.calculus q k))+
      (D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖D.calculus (f n) (h-D.calculus q k)-D.calculus g (h-D.calculus q k)‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := norm_add_le _ _
    _ ≤ C*‖h-D.calculus q k‖+‖g‖*‖h-D.calculus q k‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add
        ((D.norm_calculus_apply_le _ _).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)))
        (D.norm_calculus_apply_le _ _))
    _ ≤ (C+‖g‖+1)*‖h-D.calculus q k‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := by
      nlinarith [norm_nonneg (h-D.calculus q k)]
    _ < (C+‖g‖+1)*(eps/(3*(C+‖g‖+1)))+eps/3 :=
      add_lt_add (mul_lt_mul_of_pos_left hv' (by positivity)) hmid
    _ < eps := by
      field_simp
      nlinarith [norm_nonneg g]

lemma kernelMultiplier_strong_tendsto (D : RealSpectralCalculus H) (t : ℝ) (h : H) :
    Tendsto (fun n => D.calculus (kernelMultiplier n t) h) atTop
      (𝓝 (kernelFourier t • D.unitary t h)) := by
  have ht := D.tendsto_calculus_of_compact (fun n => kernelMultiplier n t)
    (kernelFourier t • spectralCharacter t) kernelMass_pos.le
    (fun n => norm_kernelMultiplier_le n t) (kernelMultiplier_mul_tendsto t) h
  simpa only [map_smul,smul_apply,unitary] using ht

end RealSpectralCalculus
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma tendsto_apply_of_tendsto_xi (S : StandardModularData H)
    (a : ℕ → S.M.toStarSubalgebra) (b : S.M.toStarSubalgebra)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hx : Tendsto (fun n => (a n:H →L[ℂ] H) S.xi) atTop (𝓝 ((b:H →L[ℂ] H) S.xi))) (h : H) :
    Tendsto (fun n => (a n:H →L[ℂ] H) h) atTop (𝓝 ((b:H →L[ℂ] H) h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hd := commutant_cyclic S.M S.xi S.separating
  obtain ⟨v,⟨c,hc,rfl⟩,hv⟩ := hd.exists_dist_lt h
    (show 0 < eps/(3*(C+‖b‖+1)) by positivity)
  have hv' : ‖h-c S.xi‖ < eps/(3*(C+‖b‖+1)) := by simpa only [dist_eq_norm] using hv
  have he (d : S.M.toStarSubalgebra) : (d:H →L[ℂ] H) (c S.xi) = c ((d:H →L[ℂ] H) S.xi) :=
    congrArg (fun f : H →L[ℂ] H => f S.xi) (VonNeumannAlgebra.mem_commutant_iff.mp hc d d.property)
  have ht : Tendsto (fun n => (a n:H →L[ℂ] H) (c S.xi)) atTop (𝓝 ((b:H →L[ℂ] H) (c S.xi))) := by
    simpa only [he,Function.comp_def] using (c.continuous.tendsto ((b:H →L[ℂ] H) S.xi)).comp hx
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ < eps/3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have heq : (a n:H →L[ℂ] H) h-(b:H →L[ℂ] H) h =
      ((a n:H →L[ℂ] H) (h-c S.xi)-(b:H →L[ℂ] H) (h-c S.xi))+
      ((a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖(a n:H →L[ℂ] H) (h-c S.xi)-(b:H →L[ℂ] H) (h-c S.xi)‖+
        ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ := norm_add_le _ _
    _ ≤ C*‖h-c S.xi‖+‖b‖*‖h-c S.xi‖+
        ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add
        (((a n:H →L[ℂ] H).le_opNorm _).trans (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)))
        ((b:H →L[ℂ] H).le_opNorm _))
    _ ≤ (C+‖b‖+1)*‖h-c S.xi‖+
        ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ := by
      nlinarith [norm_nonneg (h-c S.xi)]
    _ < (C+‖b‖+1)*(eps/(3*(C+‖b‖+1)))+eps/3 :=
      add_lt_add (mul_lt_mul_of_pos_left hv' (by positivity)) hmid
    _ < eps := by
      field_simp
      nlinarith [norm_nonneg b]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma kernelFourier_star (t : ℝ) : star (kernelFourier t) = kernelFourier t := by
  unfold kernelFourier
  rw [Complex.star_def,← integral_conj,
    ← integral_neg_eq_self (fun r => spectralCharacter t r*(kernelScalar r:ℂ)) volume]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [map_mul,spectralCharacter_arg_neg,kernelScalar_even,Complex.conj_ofReal,Complex.star_def]

lemma kernelFourier_eq_real (t : ℝ) : ((kernelFourier t).re:ℂ) = kernelFourier t :=
  Complex.conj_eq_iff_re.mp (kernelFourier_star t)

lemma kernelFourier_positive_near_zero : ∃ d : ℝ, 0 < d ∧
    ∀ t : ℝ, |t| < d → 0 < (kernelFourier t).re := by
  have hp : 0 < (kernelFourier 0).re := by rw [kernelFourier_zero,Complex.ofReal_re]; exact kernelMass_pos
  have he : ∀ᶠ t in 𝓝 (0:ℝ), 0 < (kernelFourier t).re :=
    (Complex.continuous_re.comp continuous_kernelFourier).continuousAt.eventually (eventually_gt_nhds hp)
  obtain ⟨d,hd,hdt⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨d,hd,fun t ht => hdt ?_⟩
  simpa only [Real.dist_eq,sub_zero] using ht

end BoundedRecovery

end
end
end

end OAI
