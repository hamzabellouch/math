import OAI.Analysis.CircleDomains.Sobolev.CircleSmoothingTolerance
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace OAI

/-! A smoothing discrepancy tending to zero leaves both endpoints of
every bounded local real band unchanged. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem tendsto_zero_of_abs_le_tolerance
    {X : Type*} {l : Filter X} {r e : X → ℝ}
    (he : Tendsto e l (𝓝 0)) (hbound : ∀ᶠ x in l, |r x| ≤ e x) :
    Tendsto r l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hbound, (tendsto_order.mp he).2 ε hε] with x hx he'
  simpa only [dist_zero_right, Real.norm_eq_abs] using hx.trans_lt he'

 theorem bounded_bands_eq_of_sub_tendsto_zero
    {X : Type*} {l : Filter X} [NeBot l] {u v : X → ℝ}
    (hul : IsBoundedUnder (· ≥ ·) l u) (huu : IsBoundedUnder (· ≤ ·) l u)
    (hsub : Tendsto (fun x => v x - u x) l (𝓝 0)) :
    liminf v l = liminf u l ∧ limsup v l = limsup u l := by
  let r := fun x => v x - u x
  have heq : u + r = v := by
    funext x
    dsimp [r]
    ring
  have heq' : r + u = v := by rw [add_comm, heq]
  have hrl : IsBoundedUnder (· ≥ ·) l r := hsub.isBoundedUnder_ge
  have hru : IsBoundedUnder (· ≤ ·) l r := hsub.isBoundedUnder_le
  have hlo := le_liminf_add (u := u) (v := r) hul huu hrl hru.isCoboundedUnder_ge
  have hhi := liminf_add_le (u := r) (v := u) hrl hru hul huu.isCoboundedUnder_ge
  have hsuplo := le_limsup_add (u := u) (v := r) huu hul.isCoboundedUnder_le hru hrl
  have hsuphi := limsup_add_le (u := u) (v := r) hul huu hrl.isCoboundedUnder_le hru
  have hliminf : liminf r l = 0 := hsub.liminf_eq
  have hlimsup : limsup r l = 0 := hsub.limsup_eq
  rw [heq, hliminf, add_zero] at hlo hsuplo
  rw [heq', hlimsup, zero_add] at hhi
  rw [heq, hlimsup, add_zero] at hsuphi
  exact ⟨le_antisymm hhi hlo, le_antisymm hsuphi hsuplo⟩

namespace OpenPlanePartition
variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem adjustedCircleMix_sub (u v : ι → EuclideanPlane → ℝ) (w : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ρ.adjustedCircleMix u v w x - w x = ρ.mix (fun k y => v k y - u k y) x := by
  have he : (fun k y => v k y + (w y - u k y)) =
      (fun k y => (v k y - u k y) + w y) := by
    funext k y
    ring
  rw [adjustedCircleMix, he, ρ.mix_add_scalar _ w hx, add_sub_cancel_right]

 theorem adjustedCircleMix_bands_eq
    (u v : ι → EuclideanPlane → ℝ) (w e : EuclideanPlane → ℝ)
    (hbound : ∀ x ∈ Ω, |ρ.mix (fun k y => v k y - u k y) x| ≤ e x)
    {s : EuclideanPlane} (hs : s ∈ closure (Ω : Set EuclideanPlane))
    (he : Tendsto e (𝓝[(Ω : Set EuclideanPlane)] s) (𝓝 0))
    (hwl : IsBoundedUnder (· ≥ ·) (𝓝[(Ω : Set EuclideanPlane)] s) w)
    (hwu : IsBoundedUnder (· ≤ ·) (𝓝[(Ω : Set EuclideanPlane)] s) w) :
    liminf (ρ.adjustedCircleMix u v w) (𝓝[(Ω : Set EuclideanPlane)] s) =
        liminf w (𝓝[(Ω : Set EuclideanPlane)] s) ∧
      limsup (ρ.adjustedCircleMix u v w) (𝓝[(Ω : Set EuclideanPlane)] s) =
        limsup w (𝓝[(Ω : Set EuclideanPlane)] s) := by
  let : NeBot (𝓝[(Ω : Set EuclideanPlane)] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  apply bounded_bands_eq_of_sub_tendsto_zero hwl hwu
  apply tendsto_zero_of_abs_le_tolerance he
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [ρ.adjustedCircleMix_sub u v w hx]
  exact hbound x hx

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
