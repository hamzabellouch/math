import OAI.Analysis.CircleDomains.Topology.HomeomorphicLevelContinuum
import OAI.Analysis.CircleDomains.Topology.LimitLevelContinuum
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace OAI

/-! Every point of an actual limiting homeomorphic height belongs to
a nondegenerate compact continuum of its level in each centred disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_level_continuum
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Set ℂ, IsCompact C ∧ IsConnected C ∧ C.Nontrivial ∧ x ∈ C ∧
      C ⊆ closedBall x r ∧ (∀ y ∈ C, v y = v x) ∧
      (C ∩ sphere x r).Nonempty := by
  choose K hK hc hx hsub hlevel hmeet using
    (fun n => homeomorphic_level_continuum (φ n) x hr)
  obtain ⟨C, hCc, hconn, hxC, hCS, hCv, hCE⟩ :=
    exists_limit_level_continuum (isCompact_closedBall x r) isClosed_sphere
      (fun n z => (φ n z).im) hv
      ((tendstoLocallyUniformly_iff_forall_isCompact.mp hlim) _ (isCompact_closedBall x r))
      K hc hsub hx hlevel hmeet
  obtain ⟨y, hyC, hy⟩ := hCE
  have hne : x ≠ y := by
    intro he
    rw [← he, mem_sphere, dist_self] at hy
    exact hr.ne' hy.symm
  exact ⟨C, hCc, hconn, ⟨x, hxC, y, hyC, hne⟩, hxC, hCS, hCv, y, hyC, hy⟩

end CircleDomainRigidity

end

end OAI
