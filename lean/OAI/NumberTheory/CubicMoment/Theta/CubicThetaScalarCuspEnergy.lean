import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarCuspSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunctionEnergyTransport

namespace OAI

/-! The scaled cusp cutoffs have uniformly bounded hyperbolic gradient.
The bound uses the unique high primitive row and exact Mobius transport. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaScalarCusp_upper {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ}
    (hp : 1<p.2) : cubicThetaScalarCusp N p=cubicThetaCuspCutoff (p.2/N) := by
  have he : cubicThetaScalarCusp N p=cubicThetaScalarCuspTerm N cubicThetaZeroRow p := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp
      (r.high_height_c_zero hp (cubicThetaScalarCuspTerm_high hN hn)))
  rw [he]
  simp only [cubicThetaScalarCuspTerm,CubicThetaBottomRow.height,cubicThetaZeroRow,norm]
  norm_num

lemma cubicThetaScalarCusp_local_zero {N : ℝ} (hN : 1<N) {p : ℂ × ℝ}
    (hp : 0<p.2) (hr : ∀ r : CubicThetaBottomRow, r.height p≤1) :
    cubicThetaScalarCusp N =ᶠ[𝓝 p] (fun _ => 0) := by
  classical
  obtain ⟨K,hKn,hK,hpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaScalarCusp_compact_sum hN.le hK hpos
  have hrows : ∀ᶠ q in 𝓝 p, ∀ r∈S, r.height q<N := by
    apply (eventually_all_finset S).mpr
    intro r _
    exact (r.height_contDiffAt hp).continuousAt.eventually (gt_mem_nhds ((hr r).trans_lt hN))
  filter_upwards [hKn,hrows] with q hq hrows
  rw [hS q hq]
  exact Finset.sum_eq_zero (fun r h => cubicThetaScalarCuspTerm_zero N
    (by linarith) r (hrows r h).le)

lemma cubicThetaScalarCusp_energy_invariant {N : ℝ} (hN : 1≤N)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) :
    p.2^2*cubicThetaFunctionEnergy (cubicThetaScalarCusp N) p=
      (cubicThetaMobius (cubicThetaPrincipalComplex g) p).2^2*
        cubicThetaFunctionEnergy (cubicThetaScalarCusp N)
          (cubicThetaMobius (cubicThetaPrincipalComplex g) p) := by
  have he : (fun q => cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaPrincipalComplex g) q))
      =ᶠ[𝓝 p] cubicThetaScalarCusp N := by
    filter_upwards [isOpen_lt continuous_const continuous_snd |>.mem_nhds hp] with q hq
    exact cubicThetaScalarCusp_invariant N g hq
  have hd := he.fderiv_eq (𝕜:=ℝ)
  have hf := (cubicThetaScalarCusp_smooth hN).contDiffAt
    (isOpen_lt continuous_const continuous_snd |>.mem_nhds
      (cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g) hp))
  have ht := cubicThetaFunctionEnergy_mobius (cubicThetaScalarCusp N)
    (cubicThetaPrincipalComplex g) hp (hf.differentiableAt (by simp))
  simpa only [cubicThetaFunctionEnergy,hd] using ht

lemma cubicThetaCuspCutoff_scaled_energy (N v : ℝ) :
    v^2*‖deriv (fun t => cubicThetaCuspCutoff (t/N)) v‖^2=
      (v/N)^2*‖deriv cubicThetaCuspCutoff (v/N)‖^2 := by
  have hd := (cubicThetaCuspCutoff_smooth.differentiable (by simp) (v/N)).hasDerivAt.scomp v
    ((hasDerivAt_id v).div_const N)
  have he : deriv (fun t => cubicThetaCuspCutoff (t/N)) v=
      (1/N) • deriv cubicThetaCuspCutoff (v/N) := hd.deriv
  rw [he]
  simp only [one_div,norm_smul,norm_inv,Real.norm_eq_abs,sq_abs,mul_pow,inv_pow,div_pow]
  ring

lemma cubicThetaScalarCusp_energy_bound :
    ∃ B≥0, ∀ N : ℝ, 2≤N → ∀ p : ℂ × ℝ, 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (cubicThetaScalarCusp N) p≤B := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaCuspCutoff_deriv_bound
  refine ⟨B,hB,?_⟩
  intro N hN p hp
  have hN1 : 1≤N := by linarith
  have hupper (q : ℂ × ℝ) (hq : 1<q.2) :
      q.2^2*cubicThetaFunctionEnergy (cubicThetaScalarCusp N) q≤B := by
    have he : cubicThetaScalarCusp N =ᶠ[𝓝 q] (fun y => cubicThetaCuspCutoff (y.2/N)) := by
      filter_upwards [isOpen_lt continuous_const continuous_snd |>.mem_nhds hq] with y hy
      exact cubicThetaScalarCusp_upper hN1 hy
    have hd := he.fderiv_eq (𝕜:=ℝ)
    have hc : DifferentiableAt ℝ cubicThetaCuspCutoff (q.2/N) :=
      cubicThetaCuspCutoff_smooth.differentiable (by simp) _
    have hi : DifferentiableAt ℝ (fun t : ℝ => t/N) q.2 := differentiableAt_id.div_const N
    have hf : DifferentiableAt ℝ (fun t => cubicThetaCuspCutoff (t/N)) q.2 :=
      DifferentiableAt.comp (f:=fun t : ℝ => t/N) (g:=cubicThetaCuspCutoff) q.2 hc hi
    change q.2^2*cubicThetaTangentEnergy
      ((fderiv ℝ (cubicThetaScalarCusp N) q).comp _)≤B
    rw [hd]
    change q.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaCuspCutoff (y.2/N)) q≤B
    rw [cubicThetaFunctionEnergy_vertical hf,cubicThetaCuspCutoff_scaled_energy]
    exact (hbound (q.2/N)).trans (by
      by_cases h : q.2/N∈Icc (1:ℝ) 2
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h]; exact hB)
  by_cases h : ∃ r : CubicThetaBottomRow, 1<r.height p
  · obtain ⟨r,hr⟩ := h
    rw [cubicThetaScalarCusp_energy_invariant hN1 r.completion hp]
    apply hupper
    change 1<(cubicThetaBottomRow r.completion).height p
    rwa [r.completion_row]
  · have hr : ∀ r : CubicThetaBottomRow, r.height p≤1 := by
      simpa only [not_exists,not_lt] using h
    have he := (cubicThetaScalarCusp_local_zero (by linarith : 1<N) hp hr).fderiv_eq (𝕜:=ℝ)
    simp only [cubicThetaFunctionEnergy,he,fderiv_const_apply,ContinuousLinearMap.zero_comp,
      cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero]
    exact hB

end CubicFirstMoment

end

end OAI
