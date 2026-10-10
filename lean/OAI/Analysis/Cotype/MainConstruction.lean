import OAI.Analysis.Cotype.IdentityWalshDecay
import OAI.Analysis.Cotype.FiniteCotypeBounds
import OAI.Analysis.Cotype.ParameterChoice

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]

theorem identity_walsh_decay_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) :
    Filter.Tendsto (fun N => walshNorm N (ContinuousLinearMap.id ℝ X)) Filter.atTop (nhds 0) := by
  obtain ⟨q,CF,hq,hCF,hF⟩ := finiteCotype_fixed_bounds hX
  obtain ⟨r,CY,hr,hCY,hY⟩ := finiteCotype_fixed_bounds hXd
  obtain ⟨m,hm,hDd,hDp,hcut,hcutm,hsize⟩ := exists_admissible_cotype_parameters q r CF CY hq hr hCF hCY
  exact identity_walsh_decay_of_fixedCotype hAP m (CY*(m : ℝ)^(1/2-1/r))
    (CF*(m : ℝ)^(1/2-1/q)) hDd hDp (hY m) (hF m) hcut hcutm hsize

theorem no_uniform_l1_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) :
    ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) :=
  no_uniform_l1_of_walsh_decay (identity_walsh_decay_of_AP_cotype_cotype hAP hX hXd)

end Cotype

end

end OAI
