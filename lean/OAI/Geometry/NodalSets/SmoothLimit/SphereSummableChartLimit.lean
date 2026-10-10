import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientDistanceLaws
import OAI.Geometry.NodalSets.SmoothLimit.FiniteJetSummableTailLemmas

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sphere_coefficient_jet_increment_bound (P : Finset Base) (J : ℕ)
    (a b : SphereEnergyData)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a.density)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (p : Base) (hp : p ∈ P) (k : ℕ) (hk : k ≤ J)
    (z : BaseModel) (hz : z ∈ sphereAtlasCore) :
    dist (iteratedFDeriv ℝ k (intrinsicChartCoefficient a.tensor a.density p) z)
      (iteratedFDeriv ℝ k (intrinsicChartCoefficient b.tensor b.density p) z) ≤
      sphereCoefficientDistance P J a.tensor a.density b.tensor b.density := by
  have hca := intrinsic_coefficient_chart_smooth a.tensor a.smooth a.symm a.pos a.density ha
  have hcb := intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb
  have h := norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J
    (fun p z ↦ intrinsicChartCoefficient b.tensor b.density p z-
      intrinsicChartCoefficient a.tensor a.density p z)
    (fun p _ ↦ (hcb p).sub (hca p)) p hp k hk z hz
  rw [fun_iteratedFDeriv_sub_apply
    ((hcb p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((hca p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt] at h
  simpa only [sphereCoefficientDistance,dist_eq_norm, norm_sub_rev] using h

theorem sphere_summable_chart_limit (P : Finset Base) (d : ℕ → SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density)
    (hseq : ∀ J, Summable (fun n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density))
    (p : Base) (hp : p ∈ P) :
    ∃ c : BaseModel → CoefficientPoint BaseModel,
      ContDiffOn ℝ ∞ c (interior sphereAtlasCore) ∧
      ∀ z ∈ interior sphereAtlasCore,
        Tendsto (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p z)
          atTop (𝓝 (c z)) := by
  obtain ⟨c,hc,ht⟩ := smooth_limit_of_summable_jets
    (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p)
    (fun n ↦ intrinsic_coefficient_chart_smooth (d n).tensor (d n).smooth
      (d n).symm (d n).pos (d n).density (hd n) p)
    (interior sphereAtlasCore) isOpen_interior
    (fun J n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density) hseq
    (fun k n z hz ↦ sphere_coefficient_jet_increment_bound P k (d n) (d (n+1))
      (hd n) (hd (n+1)) p hp k le_rfl z (interior_subset hz))
  refine ⟨c,hc,?_⟩
  intro z hz
  have h := (continuousMultilinearCurryFin0 ℝ BaseModel (CoefficientPoint BaseModel)).continuous.tendsto
    (iteratedFDeriv ℝ 0 c z) |>.comp ((ht 0).tendsto_at hz)
  exact h

end
end Yau.Target

end OAI
