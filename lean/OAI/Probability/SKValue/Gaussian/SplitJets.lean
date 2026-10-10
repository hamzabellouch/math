import Mathlib
import OAI.Probability.SKValue.Gaussian.SplitShape
import OAI.Probability.SKValue.Equations.UniformPolynomial

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma splitTerminal_jets_limit (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ iteratedDeriv k (deriv (splitTerminal γ t n)) x)
      (fun x ↦ iteratedDeriv k (deriv (phi W γ t)) x) := by
  have ht:(t:ℝ)∈Ico (0:ℝ) 1 := ⟨t.property.1.le,t.property.2⟩
  have hl:TendstoUniformly (fun n x ↦ iteratedDeriv k (deriv (splitTerminal γ t n)) x)
      (fun x ↦ iteratedDeriv k (deriv (phi W γ t)) x) atTop := by
    simpa only [iteratedDeriv_succ',splitTerminal_eq,Function.comp_def] using
      (splitSmooth_jet_limits W γ t ht (k+1)).comp (fun x:ℝ ↦ (⟨(t:ℝ),⟨t.property.1.le,le_rfl⟩⟩,x))
  obtain ⟨C,hC,hb⟩:=splitSmooth_bulk_jets γ t ht k
  have hbd:∀ n x,|iteratedDeriv k (deriv (splitTerminal γ t n)) x| ≤ C := by
    intro n x
    rw [splitTerminal_eq]
    exact hb n t ⟨t.property.1.le,le_rfl⟩ k le_rfl x
  exact ⟨hl,C,hC,hbd,fun x ↦ le_of_tendsto (hl.tendsto_at x).abs (Eventually.of_forall (fun n ↦ hbd n x))⟩
lemma split_spatialJet_limit (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ spatialJet (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) k x)
      (spatialJet (γ.coeff t) (phi W γ t) k) := by
  have hc:BoundedUniformLimit (fun n (_:ℝ) ↦ γ.coeff t+(gridDelta n:ℝ)) (fun _ ↦ γ.coeff t) := by
    apply BoundedUniformLimit.seq
    · change Tendsto (fun n:ℕ ↦ γ.coeff t+1/(n+1:ℝ)) atTop (𝓝 (γ.coeff t))
      simpa only [add_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (γ.coeff t))
    · refine ⟨γ.coeff t+1,by linarith [γ.nonneg _ ⟨t.property.1.le,t.property.2⟩],fun n ↦ ?_⟩
      rw [abs_of_nonneg (add_nonneg (γ.nonneg _ ⟨t.property.1.le,t.property.2⟩) (gridDelta n).coe_nonneg)]
      exact add_le_add le_rfl (gridDelta_le_one n)
  exact hc.mul (splitTerminal_jets_limit W γ t k)
end SKValue

end

end OAI
