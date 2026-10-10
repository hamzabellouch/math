import OAI.Analysis.CircleDomains.Sobolev.ModelScalarEnergy
import OAI.Analysis.CircleDomains.Transfer.ModelPriorityContinuity
import OAI.Analysis.CircleDomains.Sobolev.PriorityL2Approximation

namespace OAI

/-! Construct the actual continuous horizontal priority coordinate with
any prescribed L2 error and prescribed neighborhoods of the source ends. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_horizontal_priority_approximation (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (b : ℕ → ℂ) (hb : ∀ n, (b n : Sphere) ∉ G)
    (z : ℕ → Sphere) (hz : ∀ n, M.projection (z n) = (b n : Sphere))
    (hcover : ∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
      ∃ n, b n = q)
    {K : ℝ} (hc : ∀ n, ‖(finiteCoord (z n)).re‖ ≤ K)
    (W : ℕ → Set ℂ) (hW : ∀ n, W n ∈ 𝓝 (b n))
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ → ℝ) (χ : ℕ → ℂ → ℝ),
      (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (b n) (r n) ⊆ W n) ∧
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (b n) (r n) ∧ (∀ q, χ n q ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ q in 𝓝 (b n), χ n q = 1)) ∧
      let X := fun q : ℂ => M.horizontalSection (q : Sphere)
      let P := fun q => priorityInfiniteValue (fun n => χ n q) (fun n => (finiteCoord (z n)).re) (X q)
      Continuous P ∧
      MemLp (fun q => fderiv ℝ P q-fderiv ℝ X q) 2
        (volume.restrict ({q : ℂ | (q : Sphere) ∈ G} ∩ ball 0 R)) ∧
      (eLpNorm (fun q => fderiv ℝ P q-fderiv ℝ X q) 2
        (volume.restrict ({q : ℂ | (q : Sphere) ∈ G} ∩ ball 0 R))).toReal < ε := by
  let D := {q : ℂ | (q : Sphere) ∈ G}
  let B := Dᶜ
  let X := fun q : ℂ => M.horizontalSection (q : Sphere)
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  obtain ⟨A, hA, hbound⟩ := M.function_bounded_on_source_ball hinf R
  let L := max K A
  have hL : 0 ≤ L := hA.trans (le_max_right _ _)
  have hX : ContDiffOn ℝ ∞ X Bᶜ := by
    simpa only [B, compl_compl] using M.horizontalSection_plane_smooth hG
  have hXb : ∀ q ∈ D ∩ ball 0 R, ‖X q‖ ≤ L := by
    intro q hq
    have he : X q = (M.function q).re := by
      simpa only [X, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hq.1
    rw [he]
    exact (show ‖(M.function q).re‖ ≤ ‖M.function q‖ by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M.function q)).trans
      ((hbound q hq.1 hq.2).trans (le_max_right _ _))
  obtain ⟨r, χ, hr, hrt, hrW, hχ, hLp, he⟩ := exists_priority_L2_approximation
    hD.isClosed_compl (hD.inter isOpen_ball) (by simpa only [B, compl_compl] using (inter_subset_left : D ∩ ball 0 R ⊆ D))
    b hb W hW (fun n => (finiteCoord (z n)).re) X hX hL
    (fun n => (hc n).trans (le_max_left _ _)) hXb
    (M.horizontalSection_plane_memLp hG hinf R) hε
  refine ⟨r, χ, hr, hrt, hrW, hχ, ?_, hLp, he⟩
  exact M.priority_horizontal_plane_continuous hsard hsch hG hconn hinf hTD z b hz hcover r hrt χ
    (fun n => (hχ n).1.continuous)
    (fun n => (subset_tsupport (χ n)).trans (hχ n).2.2.1)
    (fun q n => (hχ n).2.2.2.1 q) (fun n => (hχ n).2.2.2.2) hc

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
