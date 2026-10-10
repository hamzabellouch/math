import OAI.Analysis.Cotype.UniformDecay
import OAI.Analysis.Cotype.CompactDomainSource
import OAI.Analysis.Cotype.WalshMainEstimates

namespace OAI

noncomputable section

universe u
namespace Cotype
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]

theorem identity_walsh_decay_of_fixedCotype (hAP : ApproximationProperty X)
    (m : ℕ) (Ddual Dprimal : ℝ) (hDd : 1 ≤ Ddual) (hDp : 1 ≤ Dprimal)
    (hdual : FixedCotypeBound (X →L[ℝ] ℝ) m Ddual)
    (hprimal : FixedCotypeBound X m Dprimal)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*(12*Ddual)*Real.sqrt m)))
        ((m : ℝ)*(1/(2*24*Dprimal*Real.sqrt m)))) :
    Filter.Tendsto (fun N => walshNorm N (ContinuousLinearMap.id ℝ X)) Filter.atTop (nhds 0) := by
  have hm : 0 < m := by omega
  obtain ⟨n₀,hn₀,hρ,hall⟩ := exists_uniform_walsh_decay.{u,u} m (12*Ddual) Dprimal
    (by linarith) hDp hcut hcutm hsize
  have hbound (N : ℕ) : walshNorm N (ContinuousLinearMap.id ℝ X) ≤ 2*uniformDecayRate m n₀ N := by
    have hρ0 : 0 ≤ uniformDecayRate m n₀ N := by unfold uniformDecayRate; positivity
    apply walshNorm_le_of_bound _ (by positivity)
    intro f
    let E := Submodule.span ℝ (Set.range f)
    let : FiniteDimensional ℝ E := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
    obtain ⟨c⟩ := exists_compactDomain_source hm hdual E
    let := c.normedGroup
    let := c.normedSpace
    let := c.completeSpace
    let F : Cube N → c.G := fun u => c.iota ⟨f u, Submodule.subset_span ⟨u,rfl⟩⟩
    have hF (u : Cube N) : ‖F u‖ ≤ ‖f u‖ := by
      calc
        _ ≤ ‖c.iota‖ * ‖(⟨f u, Submodule.subset_span ⟨u,rfl⟩⟩ : E)‖ := c.iota.le_opNorm _
        _ ≤ ‖f u‖ := by
          simpa using mul_le_of_le_one_left (norm_nonneg (f u)) c.norm_iota
    have hJ : walshNorm N c.J ≤ 2*uniformDecayRate m n₀ N := by
      have h := compactMap_walsh_bound hAP c.J c.compact N hρ0
        (fun A hA => (hall c.G X A c.dual_cotype hprimal hA).2 N)
      exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left c.norm_J hρ0])
    have he : operatorWalsh c.J F = operatorWalsh (ContinuousLinearMap.id ℝ X) f := by
      funext v
      unfold operatorWalsh vectorWalsh
      congr 1; funext u
      change character v u • c.J (F u) = character v u • f u
      rw [show c.J (F u) = f u from c.factor ⟨f u,Submodule.subset_span ⟨u,rfl⟩⟩]
    rw [← he]
    exact (operatorWalsh_le_walshNorm c.J F).trans
      (mul_le_mul hJ (cubeL2_mono hF) (cubeL2_nonneg F) (by positivity))
  apply squeeze_zero (fun N => walshNorm_nonneg N _) hbound
  simpa using hρ.const_mul 2

theorem no_uniform_l1_of_fixedCotype (hAP : ApproximationProperty X)
    (m : ℕ) (Ddual Dprimal : ℝ) (hDd : 1 ≤ Ddual) (hDp : 1 ≤ Dprimal)
    (hdual : FixedCotypeBound (X →L[ℝ] ℝ) m Ddual)
    (hprimal : FixedCotypeBound X m Dprimal)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*(12*Ddual)*Real.sqrt m)))
        ((m : ℝ)*(1/(2*24*Dprimal*Real.sqrt m)))) :
    ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) :=
  no_uniform_l1_of_walsh_decay
    (identity_walsh_decay_of_fixedCotype hAP m Ddual Dprimal hDd hDp hdual hprimal hcut hcutm hsize)

end Cotype

end

end OAI
