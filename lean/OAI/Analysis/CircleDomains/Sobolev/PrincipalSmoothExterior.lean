import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothApproximation
import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm
import OAI.Analysis.CircleDomains.Selection.ExteriorDecay

namespace OAI

/-! The constructed smooth principal maps obey one common exterior bound
and decay estimate, obtained from the coefficient area theorem. -/
open Set Filter Asymptotics Bornology
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

lemma holomorphic_exterior (n : ℕ) {z : ℂ} (hz : R+2 ≤ ‖z‖) :
    DifferentiableAt ℂ (S.map n : ℂ → ℂ) z := by
  apply differentiableAt_of_partialBar_zero ((S.smooth n).differentiable (by simp) z)
  rw [S.equation n z, S.coefficient_zero n z hz, zero_mul]

lemma principal (n : ℕ) :
    Tendsto (fun z => S.map n z-z) (cobounded ℂ) (𝓝 0) := by
  have h := cauchyTransform_zero_at_infty (S.density n)
  rw [Metric.cobounded_eq_cocompact]
  simpa only [S.values, add_sub_cancel_left] using h

lemma principal_bigO (n : ℕ) :
    (fun z => S.map n z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  apply principal_bigO_of_exterior_holomorphic _ (S.principal n)
  exact (eventually_cobounded_le_norm (R+2)).mono fun z hz => S.holomorphic_exterior n hz

lemma exterior_bounds (harea : ExteriorCoefficientAreaTheorem) {T : ℝ}
    (hT : 0 < T) (hRT : R+2 ≤ T) :
    (∀ n z, 2*T ≤ ‖z‖ → ‖S.map n z-z‖ ≤ T) ∧
    ∀ n z, 2*T ≤ ‖z‖ → ‖S.map n z-z‖ ≤ 2*T^2/‖z‖ := by
  have hd (n : ℕ) : DifferentiableOn ℂ (S.map n : ℂ → ℂ) {z | T < ‖z‖} :=
    fun z hz => (S.holomorphic_exterior n (hRT.trans hz.le)).differentiableWithinAt
  exact ⟨fun n => harea.scaled_exterior_bound hT (hd n)
      (S.map n).injective.injOn (S.principal_bigO n),
    fun n => harea.scaled_exterior_decay hT (hd n)
      (S.map n).injective.injOn (S.principal_bigO n)⟩

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
