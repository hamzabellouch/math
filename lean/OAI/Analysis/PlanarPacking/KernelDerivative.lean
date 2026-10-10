import OAI.Analysis.PlanarPacking.Cardinal
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped Topology
lemma kernelMoment_hasDerivAt (ell : ℕ) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => kernelMoment ell s t) (kernelMoment (ell+1) s t) s := by
  have hd := ((((hasDerivAt_id s).ofReal_comp.const_mul (Complex.I*Real.pi*z t)).cexp).const_mul
    (lambda t*(Complex.I*Real.pi*z t)^ell))
  simpa only [kernelMoment,pow_succ,Complex.ofReal_one,id_eq,mul_one,one_mul,mul_assoc,
    mul_left_comm,mul_comm] using hd
lemma continuous_joint_kernel (ell : ℕ) :
    Continuous (fun st : ℝ×ℝ => kernelMoment ell st.1 st.2) := by
  unfold kernelMoment
  exact ((continuous_lambda.comp continuous_snd).mul
    ((continuous_const.mul (continuous_z.comp continuous_snd)).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul (continuous_z.comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp continuous_fst)))
lemma piece_hasDerivAt (p : CardinalData) (ell j : ℕ) (hj : j<6) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * kernelMoment ell s t)
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * kernelMoment (ell+1) s t) s := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn (fun st : ℝ×ℝ => kernelMoment (ell+1) st.1 st.2)
      (Set.Icc (s-1) (s+1) ×ˢ Set.Icc (0:ℝ) 1) from (continuous_joint_kernel _).continuousOn)
  have hr := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => density p j t * kernelMoment ell s t)
    (F' := fun s t => density p j t * kernelMoment (ell+1) s t)
    (s := Set.Icc (s-1) (s+1))
    (bound := fun _ => densityBound*(|p.c₀|+|p.d₀|+‖p.x‖)*max C 0)
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall fun x => (intervalIntegrable_iff.mp (piece_integrable p ell j hj x)).aestronglyMeasurable)
    (piece_integrable p ell j hj s)
    (intervalIntegrable_iff.mp (piece_integrable p (ell+1) j hj s)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx => by
      rw [norm_mul]
      exact mul_le_mul (density_bound p j (piece_interval hj (Set.uIoc_subset_uIcc ht)))
        ((hC (x,t) ⟨hx,piece_interval hj (Set.uIoc_subset_uIcc ht)⟩).trans (le_max_left _ _))
        (norm_nonneg _) (by have := densityBound_nonneg; positivity))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => (kernelMoment_hasDerivAt ell t x).const_mul _)
  exact hr.2
lemma K_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (K p ell) (K p (ell+1) s) s := by
  have ha := ((kernelMoment_hasDerivAt ell 0 s).const_mul (Pcoeff 0)).add
    (HasDerivAt.fun_sum (u := Finset.Icc (1:ℕ) 6) fun j _ =>
      (kernelMoment_hasDerivAt ell ((j:ℝ)/6) s).const_mul (2*Pcoeff j))
  have hi := HasDerivAt.fun_sum (u := Finset.range 6) fun j hj =>
    piece_hasDerivAt p ell j (Finset.mem_range.mp hj) s
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((ha.const_mul (p.C:ℂ)).add hi)
end SharpPlanar

end OAI
