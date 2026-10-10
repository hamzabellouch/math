import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ParticleBySpacetime

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma bounded_iteratedFDeriv_of_factor
    {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {g : W → (U →L[ℝ] W)} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {K : Set W} (hK : IsCompact K) (himage : ∀ x, f x ∈ K) (he : fderiv ℝ f=g ∘ f) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      obtain ⟨C,hC⟩ := hK.isBounded.exists_norm_le
      exact ⟨max C 0,le_max_right _ _,fun x => by
        simpa only [norm_iteratedFDeriv_zero] using (hC (f x) (himage x)).trans (le_max_left _ _)⟩
    | succ n =>
      have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
        ih i (by omega)
      choose B hB hbound using hb
      have hc (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
        obtain ⟨C,hC⟩ := (hK.image ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)))).isBounded.exists_norm_le
        exact ⟨max C 0,le_max_right _ _,fun x hx => (hC _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
      choose G hG hgbound using hc
      let D : ℝ := 1+∑ i, B i
      let C : ℝ := 1+∑ i, G i
      have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
      have hC : 0 ≤ C := add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => hG i))
      have hBD (i : Fin (n+1)) : B i ≤ D :=
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
      have hGC (i : Fin (n+1)) : G i ≤ C :=
        (Finset.single_le_sum (fun j _ => hG j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
      refine ⟨n.factorial*C*D^n,by positivity,fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv,he]
      apply norm_iteratedFDeriv_comp_le (n:=n) hg hf (by exact_mod_cast le_top) x
      · intro i hi
        exact (hgbound ⟨i,by omega⟩ (f x) (himage x)).trans (hGC _)
      · intro i hi hi'
        exact (hbound ⟨i,by omega⟩ x).trans ((hBD _).trans (le_self_pow₀ hD (by omega)))

private def velocityAugment (v : Vec) : ℝ × Vec := ((q v)⁻¹,velocity v)

private def velocityJet (w : ℝ × Vec) : Vec →L[ℝ] (ℝ × Vec) :=
  ((-w.1^2) • innerSL ℝ w.2).prod
    (w.1 • (ContinuousLinearMap.id ℝ Vec-(innerSL ℝ w.2).smulRight w.2))

private lemma velocityAugment_smooth : ContDiff ℝ ∞ velocityAugment :=
  (contDiff_q.inv (fun v => (q_pos v).ne')).prodMk contDiff_velocity

private lemma velocityJet_smooth : ContDiff ℝ ∞ velocityJet := by
  have hinner : ContDiff ℝ ∞ (fun w : ℝ × Vec => innerSL ℝ w.2) :=
    (innerSL ℝ (E:=Vec)).contDiff.comp contDiff_snd
  exact (ContinuousLinearMap.prodₗᵢ ℝ (E:=Vec) (F:=ℝ) (G:=Vec)).contDiff.comp
    (((contDiff_fst.pow 2).neg.smul hinner).prodMk
      (contDiff_fst.smul (contDiff_const.sub (hinner.smulRight contDiff_snd))))

private lemma velocityAugment_deriv : fderiv ℝ velocityAugment=velocityJet ∘ velocityAugment := by
  funext v
  have hq := (hasFDerivAt_inv (q_pos v).ne').comp v
    ((contDiff_q.differentiable (by simp : (∞:ℕ∞ω)≠0) v).hasFDerivAt)
  have hu := (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0) v).hasFDerivAt
  have hh := (hq.prodMk hu).fderiv
  change fderiv ℝ velocityAugment v=_ at hh
  rw [hh]
  ext h
  · simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,velocityJet,velocityAugment,
      smul_apply,innerSL_apply_apply,← dot_eq_inner,fderiv_q_apply]
    ring
  · simp only [ContinuousLinearMap.prod_apply,Function.comp_apply,velocityJet,velocityAugment,
      smul_apply,sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,← dot_eq_inner,fderiv_velocity_apply]

theorem velocity_derivatives_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖iteratedFDeriv ℝ n velocity v‖ ≤ C := by
  have himage (v : Vec) : velocityAugment v∈closedBall (0:ℝ × Vec) 1 := by
    rw [mem_closedBall_zero_iff,Prod.norm_mk]
    refine max_le ?_ (norm_velocity_lt_one v).le
    change ‖(q v)⁻¹‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (q_pos v).le)]
    apply (inv_le_one₀ (q_pos v)).mpr
    nlinarith [q_sq v,q_pos v,sq_nonneg ‖v‖]
  obtain ⟨C,hC,hb⟩ := bounded_iteratedFDeriv_of_factor velocityAugment_smooth velocityJet_smooth
    (isCompact_closedBall (0:ℝ × Vec) 1) himage velocityAugment_deriv n
  refine ⟨C,hC,fun v => ?_⟩
  have hh := (ContinuousLinearMap.snd ℝ ℝ Vec).norm_iteratedFDeriv_comp_left
    velocityAugment_smooth.contDiffAt (x:=v) (n:=n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n velocity v‖ ≤ _ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ ℝ Vec)
    (norm_nonneg _)).trans ((by simpa only [one_mul] using hb v)))

end RVM
end

end OAI
