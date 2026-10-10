import Mathlib
import OAI.Geometry.Cannon.Flows.BoundaryRecordFlow
import OAI.Geometry.Cannon.Flows.CenterNeighborhood

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual CannonMagnification CannonPacking CannonApprox CannonCells CannonCharts
open CannonNode CannonAnnular Set Metric Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_modulus_bounded (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    ∃ B : ℝ, ∀ n, modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d) ≤ B := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet
  by_contra! hunbounded
  obtain ⟨Q,hQ,CP,hCP,hpack,L,hL,hpaths,Ns,hNs,R,⟨F⟩⟩ :=
    boundary_record_flow D hδ φ d hd hdia hdc ι p hpsep hpnet hunbounded
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  have hrlim : Tendsto (fun n => (a^(Ns n))⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hNs.tendsto_atTop
  exact boundary_no_record_flow D hδ (fun n => ι (Ns n)) (fun n => p (Ns n))
    (fun n => (a^(Ns n))⁻¹) (fun _ => inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _))
    hrlim (fun n => hpnet (Ns n)) R Q (lt_of_lt_of_le (by norm_num : 0 < 2) hQ)
    CP hCP.le hpack L hL hpaths F

end CannonRelease

end
end
end
end

end OAI
