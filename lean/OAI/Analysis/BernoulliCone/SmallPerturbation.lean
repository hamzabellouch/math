import OAI.Analysis.BernoulliCone.HarmonicWeakLaplacian

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma perturbation_lower {K : ℝ≥0} {f : E → E} (hf : LipschitzWith K f)
    (x y : E) : (1-(K:ℝ))*‖x-y‖ ≤ ‖(x+f x)-(y+f y)‖ := by
  have hh := norm_sub_le ((x+f x)-(y+f y)) (f x-f y)
  have hi : ((x+f x)-(y+f y))-(f x-f y) = x-y := by abel
  rw [hi] at hh
  have h := hf.dist_le_mul x y
  rw [dist_eq_norm,dist_eq_norm] at h
  nlinarith

lemma perturbation_bijective {K : ℝ≥0} {f : E → E} (hf : LipschitzWith K f)
    (hK : K < 1) : Function.Bijective (fun x => x+f x) := by
  have hK' : (K:ℝ) < 1 := hK
  constructor
  · intro x y h
    have hh := perturbation_lower hf x y
    change x+f x = y+f y at h
    rw [h,sub_self,norm_zero] at hh
    have hn : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro z
    have hc : ContractingWith K (fun x => z-f x) := by
      refine ⟨hK,LipschitzWith.of_dist_le_mul ?_⟩
      intro x y
      simpa only [dist_sub_left] using hf.dist_le_mul x y
    let x := ContractingWith.fixedPoint (fun x => z-f x) hc
    have hh : z-f x=x := hc.fixedPoint_isFixedPt
    use x
    exact (eq_sub_iff_add_eq.mp hh.symm)

/-- A small globally Lipschitz perturbation of the identity is an actual
bi-Lipschitz homeomorphism, obtained by the contraction theorem. -/
def perturbationHomeomorph {K : ℝ≥0} {f : E → E} (hf : LipschitzWith K f)
    (hK : K < 1) : E ≃ₜ E := by
  let e := Equiv.ofBijective (fun x => x+f x) (perturbation_bijective hf hK)
  have hK' : 0 < 1-(K:ℝ) := sub_pos.mpr hK
  have hinv : LipschitzWith ⟨(1-(K:ℝ))⁻¹,(inv_pos.mpr hK').le⟩ e.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := perturbation_lower hf (e.symm x) (e.symm y)
    change (1-(K:ℝ))*‖e.symm x-e.symm y‖ ≤ ‖e (e.symm x)-e (e.symm y)‖ at hh
    rw [e.apply_symm_apply,e.apply_symm_apply] at hh
    simp only [dist_eq_norm]
    change ‖e.symm x-e.symm y‖ ≤ (1-(K:ℝ))⁻¹*‖x-y‖
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hK').mpr (by simpa only [mul_comm] using hh)
  exact ⟨e,continuous_id.add hf.continuous,hinv.continuous⟩

@[simp] lemma perturbationHomeomorph_apply {K : ℝ≥0} {f : E → E} (hf : LipschitzWith K f)
    (hK : K < 1) (x : E) : perturbationHomeomorph hf hK x = x+f x := rfl

lemma perturbationHomeomorph_symm_lipschitz {K : ℝ≥0} {f : E → E}
    (hf : LipschitzWith K f) (hK : K < 1) :
    LipschitzWith ⟨(1-(K:ℝ))⁻¹,(inv_pos.mpr (sub_pos.mpr hK : 0 < 1-(K:ℝ))).le⟩
      (perturbationHomeomorph hf hK).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let e := perturbationHomeomorph hf hK
  have hh := perturbation_lower hf (e.symm x) (e.symm y)
  change (1-(K:ℝ))*‖e.symm x-e.symm y‖ ≤ ‖e (e.symm x)-e (e.symm y)‖ at hh
  rw [e.apply_symm_apply,e.apply_symm_apply] at hh
  simp only [dist_eq_norm]
  change ‖e.symm x-e.symm y‖ ≤ (1-(K:ℝ))⁻¹*‖x-y‖
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sub_pos.mpr hK : 0 < 1-(K:ℝ))).mpr (by simpa only [mul_comm] using hh)

lemma perturbationHomeomorph_symm_fixed {K : ℝ≥0} {f : E → E}
    (hf : LipschitzWith K f) (hK : K < 1) {x : E} (hx : f x=0) :
    (perturbationHomeomorph hf hK).symm x=x := by
  apply (perturbationHomeomorph hf hK).injective
  simp [hx]
end Bernoulli.Shape

end
end

end OAI
