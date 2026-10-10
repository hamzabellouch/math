import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarCuspEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarCuspVanishing

namespace OAI

/-! Uniform value and hyperbolic differential bounds for the compact
arithmetic exhaustion. Its finite cusp set is fixed while the height grows. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff BigOperators
namespace CubicFirstMoment

lemma cubicThetaScalarCuspQuotient_energy_bound :
    ∃ B≥0, ∀ (δ : SL(2,Eisenstein)) (N : ℝ), 2≤N → ∀ p : ℂ × ℝ, 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaScalarCuspQuotient δ N
        (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p≤B := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaScalarCusp_energy_bound
  refine ⟨B,hB,?_⟩
  intro δ N hN p hp
  have he : (fun y => cubicThetaScalarCuspQuotient δ N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)))=ᶠ[𝓝 p]
      (fun y => cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y)) := by
    filter_upwards [isOpen_lt continuous_const continuous_snd |>.mem_nhds hp] with y hy
    exact cubicThetaScalarCuspQuotient_coordinates δ N hy
  have hf := (cubicThetaScalarCusp_smooth (by linarith : 1≤N)).contDiffAt
    (isOpen_lt continuous_const continuous_snd |>.mem_nhds (cubicThetaMobius_height_pos (cubicThetaFullComplex δ⁻¹) hp))
  have ht := cubicThetaFunctionEnergy_mobius (cubicThetaScalarCusp N)
    (cubicThetaFullComplex δ⁻¹) hp (hf.differentiableAt (by simp))
  unfold cubicThetaFunctionEnergy
  rw [he.fderiv_eq (𝕜:=ℝ)]
  change p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaScalarCusp N
    (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y)) p≤B
  rw [ht]
  exact hbound N hN _ (cubicThetaMobius_height_pos _ hp)

lemma cubicThetaCompactCuspCutoff_norm (T : Finset SL(2,Eisenstein))
    {N : ℝ} (hN : 1≤N) (q : CubicThetaQuotient) :
    ‖cubicThetaCompactCuspCutoff T N q‖≤1+(T.card:ℝ) := by
  classical
  calc
    _ ≤ ‖(1:ℂ)‖+‖∑ δ∈T,cubicThetaScalarCuspQuotient δ N q‖ := norm_sub_le _ _
    _ ≤ 1+∑ δ∈T,‖cubicThetaScalarCuspQuotient δ N q‖ := by
      simpa only [norm_one] using add_le_add le_rfl
        (norm_sum_le T (fun δ => cubicThetaScalarCuspQuotient δ N q))
    _ ≤ 1+(T.card:ℝ) := by
      have h := Finset.sum_le_sum (fun δ (_ : δ∈T) => cubicThetaScalarCuspQuotient_norm δ hN q)
      simpa using add_le_add_left h 1

lemma cubicThetaCompactCuspCutoff_energy_bound (T : Finset SL(2,Eisenstein)) :
    ∃ B≥0, ∀ N : ℝ, 2≤N → ∀ p : ℂ × ℝ, 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaCompactCuspCutoff T N
        (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p≤B := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaScalarCuspQuotient_energy_bound
  refine ⟨(T.card:ℝ)^2*B,mul_nonneg (sq_nonneg _) hB,?_⟩
  intro N hN p hp
  let f := fun δ y => cubicThetaScalarCuspQuotient δ N
    (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
  have hf (δ : SL(2,Eisenstein)) : DifferentiableAt ℝ (f δ) p :=
    ((cubicThetaScalarCuspQuotient_smooth δ (by linarith : 1≤N)).contDiffAt
      (isOpen_lt continuous_const continuous_snd |>.mem_nhds hp)).differentiableAt (by simp)
  have he := cubicThetaFunctionEnergy_one_sub (DifferentiableAt.fun_sum (fun δ (_ : δ∈T) => hf δ))
  change p.2^2*cubicThetaFunctionEnergy (fun y => 1-∑ δ∈T,f δ y) p≤_
  rw [he]
  calc
    _ ≤ p.2^2*((T.card:ℝ)*∑ δ∈T,cubicThetaFunctionEnergy (f δ) p) :=
      mul_le_mul_of_nonneg_left (cubicThetaFunctionEnergy_sum_le T f p (fun δ _ => hf δ)) (sq_nonneg _)
    _ = (T.card:ℝ)*∑ δ∈T,p.2^2*cubicThetaFunctionEnergy (f δ) p := by
      rw [← Finset.mul_sum]; ring
    _ ≤ (T.card:ℝ)*∑ δ∈T,B := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun δ _ => hbound δ N hN p hp)) (Nat.cast_nonneg _)
    _ = (T.card:ℝ)^2*B := by simp; ring

end CubicFirstMoment

end

end OAI
