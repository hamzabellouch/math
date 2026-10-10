import OAI.NumberTheory.CubicMoment.Estimates.AnalyticDiskLogDerivative

namespace OAI

/-! The Jensen multiplicity bound at the same fixed radii used by the
Hecke logarithmic-derivative estimate. -/
noncomputable section
open Filter Set Erdos970
open scoped Topology BigOperators
namespace CubicFirstMoment

theorem normalized_disk_zero_mass (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B)
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ ‖ρ‖ ≤ (3/4:ℝ) ∧ f ρ=0) :
    ∑ ρ ∈ Z, ((analyticOrderAt f ρ).toNat:ℝ) ≤
      (1/Real.log ((7/8:ℝ)/(3/4:ℝ)))*Real.log B := by
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
  have he : Z=hfin.toFinset := by
    ext ρ
    simp only [hZ,Set.Finite.mem_toFinset,zerosetKfR,Set.mem_ofPred_eq,
      Metric.mem_closedBall,dist_zero_right]
  rw [he]
  exact lem_sum_m_rho_bound B (7/8:ℝ) (3/4:ℝ) hB (by norm_num)
    (by norm_num) (by norm_num) f ha (hf0 ▸ one_ne_zero) hf0 hfin g hb hg

end CubicFirstMoment

end

end OAI
