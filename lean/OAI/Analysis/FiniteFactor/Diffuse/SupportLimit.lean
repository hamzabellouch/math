import OAI.Analysis.FiniteFactor.Diffuse.OperatorSupport

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma one_sub_star_mul_contraction (T:H→L[ℂ]H) (hT:‖T‖≤1) :
    ‖1-star T*T‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x-(star T) (T x)‖≤1*‖x‖
  rw [one_mul]
  have ht : ‖star T‖≤1 := by simpa [ContinuousLinearMap.star_eq_adjoint] using hT
  have hb : ‖(star T) (T x)‖≤‖T x‖ := by
    calc
      _ ≤ ‖star T‖*‖T x‖ := (star T).le_opNorm _
      _ ≤ 1*‖T x‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = _ := one_mul _
  have hi : RCLike.re (inner ℂ x ((star T) (T x)))=‖T x‖^2 := by
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜:=ℂ) _
  have he := norm_sub_sq (𝕜:=ℂ) x ((star T) (T x))
  rw [hi] at he
  nlinarith [norm_nonneg (x-(star T) (T x)),norm_nonneg x,norm_nonneg (T x),
    norm_nonneg ((star T) (T x))]

lemma rangeSupport_eq_one_sub_kernel (T:H→L[ℂ]H) :
    rangeSupport T=1-(star T).ker.starProjection := by
  have h := ContinuousLinearMap.orthogonal_ker (star T)
  rw [←ContinuousLinearMap.star_eq_adjoint,star_star] at h
  change T.range.topologicalClosure.starProjection = ContinuousLinearMap.id ℂ H - (star T).ker.starProjection
  simpa only [h] using (Submodule.starProjection_orthogonal (star T).ker)

lemma cesaro_star_mul_tendsto (T:H→L[ℂ]H) (hT:‖T‖≤1) (x:H) :
    Tendsto (fun n=>cesaro (1-star T*T) n x) atTop
      (𝓝 (T.ker.starProjection x)) := by
  have hstar : star (1-star T*T)=1-star T*T := by simp
  have hker : (1-(1-star T*T)).ker=T.ker := by
    rw [sub_sub_cancel]
    exact ContinuousLinearMap.ker_adjoint_comp_self T
  simpa only [hker] using cesaro_tendsto_fixedProjection (1-star T*T)
    (one_sub_star_mul_contraction T hT) hstar x

end Nonhyperlinear.Diffuseness

end

end OAI
