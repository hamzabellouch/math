import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.GeneratingKernel

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance actionKernelDualNormedAddCommGroup : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance actionKernelDualNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance actionKernelBilinearNormedAddCommGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance actionKernelBilinearNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma generating_kernel_velocity_zero {B : E×F → ℝ} {Q V : E → F}
    {g : F → F →L[ℝ] F →L[ℝ] ℝ} {R : F → F →L[ℝ] ℝ} {p w : E}
    (hB : ContDiffAt ℝ 2 B (p,Q p)) (hmin : IsLocalMin B (p,Q p))
    (hQ : DifferentiableAt ℝ Q p) (hV : DifferentiableAt ℝ V p)
    (hg : DifferentiableAt ℝ g (Q p)) (hR : DifferentiableAt ℝ R (Q p))
    (hpos : ∀ u : F, u ≠ 0 → 0 < g (Q p) u u)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ a : E, fderiv ℝ B (v,Q v) (a,0) = 0)
    (hcot : ∀ᶠ v in 𝓝 p, ∀ u : F,
      fderiv ℝ B (v,Q v) (0,u) = g (Q v) (V v) u + R (Q v) u)
    (hker : fderiv ℝ Q p w = 0) : fderiv ℝ V p w = 0 := by
  have hz (u : F) : g (Q p) (fderiv ℝ V p w) u = 0 := by
    have heq : (fun v => fderiv ℝ B (v,Q v) (0,u)) =ᶠ[𝓝 p]
        fun v => g (Q v) (V v) u + R (Q v) u := hcot.mono (fun _ hv => hv u)
    have hd := ((((hg.hasFDerivAt.comp p hQ.hasFDerivAt).clm_apply hV.hasFDerivAt).clm_apply
      (hasFDerivAt_const u p)).add
      ((hR.hasFDerivAt.comp p hQ.hasFDerivAt).clm_apply (hasFDerivAt_const u p))).fderiv
    change fderiv ℝ (fun v => g (Q v) (V v) u + R (Q v) u) p = _ at hd
    have hh := localMin_generating_cotangent_kernel hB hmin hQ hstat hker u
    rw [heq.fderiv_eq,hd] at hh
    simpa [hker] using hh
  by_contra hn
  exact (hpos _ hn).ne' (hz _)

lemma generating_graph_position_immersion {B : E×F → ℝ} {Q V : E → F}
    {g : F → F →L[ℝ] F →L[ℝ] ℝ} {R : F → F →L[ℝ] ℝ} {p : E}
    (hB : ContDiffAt ℝ 2 B (p,Q p)) (hmin : IsLocalMin B (p,Q p))
    (hQ : DifferentiableAt ℝ Q p) (hV : DifferentiableAt ℝ V p)
    (hg : DifferentiableAt ℝ g (Q p)) (hR : DifferentiableAt ℝ R (Q p))
    (hpos : ∀ u : F, u ≠ 0 → 0 < g (Q p) u u)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ a : E, fderiv ℝ B (v,Q v) (a,0) = 0)
    (hcot : ∀ᶠ v in 𝓝 p, ∀ u : F,
      fderiv ℝ B (v,Q v) (0,u) = g (Q v) (V v) u + R (Q v) u)
    (himm : Function.Injective (fderiv ℝ (fun v => (Q v,V v)) p)) :
    Function.Injective (fderiv ℝ Q p) := by
  intro u v huv
  have hw : fderiv ℝ Q p (u-v) = 0 := by rw [map_sub,huv,sub_self]
  have hv := generating_kernel_velocity_zero hB hmin hQ hV hg hR hpos hstat hcot hw
  apply sub_eq_zero.mp
  apply himm
  rw [(hQ.hasFDerivAt.prodMk hV.hasFDerivAt).fderiv]
  simp [hw,hv]

end

lemma weighted_square_le (a b : ℝ) {s t : ℝ} (hs : 0<s) (ht : 0<t) :
    (a+b)^2/(s+t) ≤ a^2/s+b^2/t := by
  rw [div_add_div _ _ hs.ne' ht.ne']
  apply (div_le_div_iff₀ (add_pos hs ht) (mul_pos hs ht)).mpr
  nlinarith [sq_nonneg (t*a-s*b)]

lemma three_leg_energy_le {M : Type*} [PseudoMetricSpace M]
    (x b q y : M) {L ε r : ℝ} (hL : 0<L) (hε : 0<ε)
    (hb : dist x b ≤ L*r) :
    dist x y^2/(2*(L+2*ε)) ≤ L*r^2/2 + dist b q^2/(2*ε) + dist q y^2/(2*ε) := by
  have htri : dist x y ≤ L*r+(dist b q+dist q y) :=
    (dist_triangle x b y).trans (add_le_add hb (dist_triangle b q y))
  have hsq : dist x y^2 ≤ (L*r+(dist b q+dist q y))^2 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  have h₁ := weighted_square_le (L*r) (dist b q+dist q y) hL (by linarith : 0<2*ε)
  have h₂ := weighted_square_le (dist b q) (dist q y) hε hε
  have he : (L*r)^2/L = L*r^2 := by field_simp
  rw [he] at h₁
  have h₂' : (dist b q+dist q y)^2/(2*ε) ≤ dist b q^2/ε+dist q y^2/ε := by
    simpa only [two_mul] using h₂
  have hh := (div_le_div_of_nonneg_right hsq (show 0≤L+2*ε by positivity)).trans
    (h₁.trans (add_le_add le_rfl h₂'))
  have hh' := div_le_div_of_nonneg_right hh (show (0:ℝ)≤2 by norm_num)
  calc
    dist x y^2/(2*(L+2*ε)) = (dist x y^2/(L+2*ε))/2 := by rw [div_div,mul_comm]
    _ ≤ (L*r^2+(dist b q^2/ε+dist q y^2/ε))/2 := hh'
    _ = _ := by field_simp; ring

end WeakMTWTransport

end

end OAI
