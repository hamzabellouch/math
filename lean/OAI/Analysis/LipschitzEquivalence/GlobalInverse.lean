import OAI.Analysis.LipschitzEquivalence.BanachAssembly

namespace OAI

universe uE uF

noncomputable section

namespace LipschitzCounterexample
namespace GlobalInverse
open Set
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem proper_finite_perturbation (S : Submodule ℝ E) [FiniteDimensional ℝ S]
    (f : E → E) (hf : Continuous f) (hn : ∀ x, ‖f x‖ = ‖x‖)
    (hS : ∀ x, x - f x ∈ S) : IsProperMap f := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf, fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hb : IsCompact ((fun s : S => (s : E)) '' Metric.closedBall (0 : S) (2*C)) :=
    (isCompact_closedBall (0 : S) (2*C)).image continuous_subtype_val
  apply (hK.add hb).of_isClosed_subset (hK.isClosed.preimage hf)
  intro x hx
  apply Set.mem_add.2
  refine ⟨f x, hx, x-f x, ?_, by abel⟩
  refine ⟨⟨x-f x, hS x⟩, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x - f x‖ ≤ 2*C
  have hn' : ‖x‖ ≤ C := by rw [← hn x]; exact hC _ hx
  exact (norm_sub_le _ _).trans (by linarith [hC _ hx])

theorem finite_perturbation_bijective (S : Submodule ℝ E) [FiniteDimensional ℝ S]
    (f : E → E) (hl : IsLocalHomeomorph f) (hn : ∀ x, ‖f x‖ = ‖x‖)
    (hS : ∀ x, x - f x ∈ S) : Function.Bijective f := by
  apply covering_bijective f (proper_covering f (proper_finite_perturbation S f hl.continuous hn hS) hl) 0
  refine ⟨0, norm_eq_zero.mp (by rw [hn, norm_zero]), fun x hx => ?_⟩
  apply norm_eq_zero.mp
  rw [← hn, hx, norm_zero]

theorem bijective_of_close_isometry [CompleteSpace E]
    (L : E ≃ₗᵢ[ℝ] F) (T : E →L[ℝ] F) (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1)
    (hT : ∀ x, ‖T x - L x‖ ≤ a * ‖x‖) : Function.Bijective T := by
  let A : E →L[ℝ] E := L.symm.toLinearIsometry.toContinuousLinearMap.comp T
  have hnorm : ‖(1 : E →L[ℝ] E) - A‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_bound _ ha0
    intro x
    change ‖x - L.symm (T x)‖ ≤ _
    rw [← L.norm_map (x - L.symm (T x)), map_sub, L.apply_symm_apply, norm_sub_rev]
    exact hT x
  have hu : IsUnit A := by
    have hunit := isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt hnorm ha)
    simpa only [sub_sub_cancel] using hunit
  have hA : Function.Bijective A := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  have heq : (fun x => L (A x)) = T := by ext x; simp [A]
  rw [← heq]
  exact L.bijective.comp hA

end GlobalInverse
end LipschitzCounterexample

namespace LipschitzCounterexample
namespace GlobalInverse
open Set
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_bounds (L : E ≃ₗᵢ[ℝ] F) (T : E →L[ℝ] F) (a : ℝ)
    (hT : ∀ x, ‖T x - L x‖ ≤ a * ‖x‖) (x : E) :
    (1-a)*‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1+a)*‖x‖ := by
  have h := hT x
  have hl := norm_sub_norm_le (L x) (T x)
  have hu := norm_sub_norm_le (T x) (L x)
  rw [L.norm_map, norm_sub_rev] at hl
  rw [L.norm_map] at hu
  constructor <;> linarith

variable [CompleteSpace E] [CompleteSpace F]

def derivativeEquiv (L : E ≃ₗᵢ[ℝ] F) (T : E →L[ℝ] F) (a : ℝ)
    (ha0 : 0 ≤ a) (ha : a < 1) (hT : ∀ x, ‖T x - L x‖ ≤ a * ‖x‖) : E ≃L[ℝ] F :=
  ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr (bijective_of_close_isometry L T a ha0 ha hT).1)
    (LinearMap.range_eq_top.mpr (bijective_of_close_isometry L T a ha0 ha hT).2)

@[simp] theorem derivativeEquiv_apply (L : E ≃ₗᵢ[ℝ] F) (T : E →L[ℝ] F) (a : ℝ)
    (ha0 : 0 ≤ a) (ha : a < 1) (hT : ∀ x, ‖T x - L x‖ ≤ a * ‖x‖) (x : E) :
    derivativeEquiv L T a ha0 ha hT x = T x := rfl

theorem localHomeomorph_of_deriv_close (f : E → F) (T : E → E →L[ℝ] F)
    (L : E → E ≃ₗᵢ[ℝ] F) (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1)
    (hf : ∀ x, HasStrictFDerivAt f (T x) x)
    (hT : ∀ x z, ‖T x z - L x z‖ ≤ a * ‖z‖) : IsLocalHomeomorph f := by
  intro x
  have hd : HasStrictFDerivAt f (derivativeEquiv (L x) (T x) a ha0 ha (hT x) : E →L[ℝ] F) x := hf x
  exact ⟨hd.toOpenPartialHomeomorph f, hd.mem_toOpenPartialHomeomorph_source, rfl⟩

theorem global_bounds_of_deriv_close (f : E ≃ F) (T : E → E →L[ℝ] F)
    (L : E → E ≃ₗᵢ[ℝ] F) (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1)
    (hf : ∀ x, HasStrictFDerivAt f (T x) x)
    (hT : ∀ x z, ‖T x z - L x z‖ ≤ a * ‖z‖) :
    (∀ x y, ‖f x-f y‖ ≤ (1+a)*‖x-y‖) ∧
    (∀ x y, (1-a)*‖x-y‖ ≤ ‖f x-f y‖) := by
  have hdf : Differentiable ℝ f := fun x => (hf x).hasFDerivAt.differentiableAt
  have hu (x : E) : ‖fderiv ℝ f x‖ ≤ 1+a := by
    rw [(hf x).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    exact fun z => (derivative_bounds (L x) (T x) a (hT x) z).2
  have hlf : LipschitzWith ⟨1+a, by linarith⟩ f :=
    lipschitzWith_of_nnnorm_fderiv_le hdf hu
  let Ti (y : F) := derivativeEquiv (L (f.symm y)) (T (f.symm y)) a ha0 ha (hT (f.symm y))
  have hdg (y : F) : HasStrictFDerivAt f.symm ((Ti y).symm : F →L[ℝ] E) y := by
    have hd : HasStrictFDerivAt f (Ti y : E →L[ℝ] F) (f.symm y) := hf _
    have hi := hd.to_local_left_inverse (g := f.symm)
      (Filter.Eventually.of_forall (fun x => f.symm_apply_apply x))
    simpa only [f.apply_symm_apply] using hi
  have hg (y : F) : ‖fderiv ℝ f.symm y‖ ≤ 1/(1-a) := by
    rw [(hdg y).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    have hz := (derivative_bounds (L (f.symm y)) (T (f.symm y)) a
      (hT (f.symm y)) ((Ti y).symm z)).1
    have he : T (f.symm y) ((Ti y).symm z) = z := (Ti y).apply_symm_apply z
    rw [he] at hz
    change ‖(Ti y).symm z‖ ≤ 1/(1-a)*‖z‖
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ (by linarith : 0 < 1-a)).2 (by nlinarith)
  have hlg : LipschitzWith ⟨1/(1-a), by positivity⟩ f.symm :=
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hdg y).hasFDerivAt.differentiableAt) hg
  refine ⟨fun x y => hlf.norm_sub_le x y, fun x y => ?_⟩
  have h := hlg.norm_sub_le (f x) (f y)
  simp only [f.symm_apply_apply] at h
  change ‖x-y‖ ≤ 1/(1-a)*‖f x-f y‖ at h
  rw [one_div_mul_eq_div] at h
  have := (le_div_iff₀ (by linarith : 0 < 1-a)).1 h
  nlinarith

end GlobalInverse
end LipschitzCounterexample

end

end OAI
