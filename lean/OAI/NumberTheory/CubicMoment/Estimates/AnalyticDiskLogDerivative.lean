import StrongPNT.Erdos970.PNT2_LogDerivative

namespace OAI

/-! The local logarithmic-derivative estimate at the fixed radii needed
for the Hecke zero-free argument. -/
noncomputable section
open Filter Set Erdos970
open scoped Topology BigOperators
namespace CubicFirstMoment

def diskLogDerivativeConstant : ℝ :=
  16*(2/3:ℝ)^2/((2/3:ℝ)-1/2)^3+
    1/(((7/8:ℝ)^2/(3/4:ℝ)-3/4)*Real.log ((7/8:ℝ)/(3/4:ℝ)))

theorem normalized_disk_logDeriv (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ ‖ρ‖ ≤ (3/4:ℝ) ∧ f ρ=0) ∧
      ∀ z : ℂ, ‖z‖ ≤ (1/2:ℝ) → f z ≠ 0 →
        ‖logDeriv f z-∑ ρ ∈ Z, ((analyticOrderAt f ρ).toNat:ℂ)/(z-ρ)‖ ≤
          diskLogDerivativeConstant*Real.log B := by
  classical
  have ha : ∀ z ∈ Metric.closedBall (0:ℂ) 1, AnalyticAt ℂ f z :=
    fun z _ => hf.analyticAt z
  have hfin : (zerosetKfR (3/4:ℝ) (by norm_num) f).Finite :=
    lem_Contra_finiteKR (3/4:ℝ) (by norm_num) (by norm_num) f ha
      ⟨0,by simp,hf0 ▸ one_ne_zero⟩
  have hex : ∀ ρ : ℂ, ∃ g : ℂ → ℂ,
      ρ ∈ zerosetKfR (3/4:ℝ) (by norm_num) f →
      AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        ∀ᶠ z in 𝓝 ρ, f z=(z-ρ)^(analyticOrderAt f ρ).toNat*g z := by
    intro ρ
    by_cases hρ : ρ ∈ zerosetKfR (3/4:ℝ) (by norm_num) f
    · obtain ⟨g,hg⟩ := lem_analytic_zero_factor (7/8:ℝ) (3/4:ℝ)
        (by norm_num) (by norm_num) (by norm_num) f ha (hf0 ▸ one_ne_zero) ρ hρ
      exact ⟨g,fun _ => hg⟩
    · exact ⟨fun _ => 1,fun h => (hρ h).elim⟩
  choose g hg using hex
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro ρ
    simp only [Set.Finite.mem_toFinset,zerosetKfR,Set.mem_ofPred_eq,
      Metric.mem_closedBall,dist_zero_right]
  · intro z hz hzero
    have hz' : z ∈ Metric.closedBall (0:ℂ) (1/2:ℝ) \ zerosetKfR (3/4:ℝ) (by norm_num) f :=
      ⟨by simpa using hz,fun h => hzero h.2⟩
    have h := final_ineq1 B hB (1/2:ℝ) (2/3:ℝ) (7/8:ℝ) (3/4:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      f ha hf0 hfin (h_σ := g) hg
      (fun w hw => hb w (by simpa using hw)) z hz'
    exact h

end CubicFirstMoment

end

end OAI
