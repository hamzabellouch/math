import Mathlib

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

namespace WeakMTWTransport
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma endomorphism_isInvertible_iff_isUnit (L : Y →L[ℝ] Y) : L.IsInvertible ↔ IsUnit L := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr e.bijective
  · intro h
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp h
    exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hb.1)
      (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma isOpen_invertible_endomorphism : IsOpen {L : Y →L[ℝ] Y | L.IsInvertible} := by
  simpa only [endomorphism_isInvertible_iff_isUnit] using
    (Units.isOpen : IsOpen {L : Y →L[ℝ] Y | IsUnit L})

lemma exists_smooth_implicit_neighborhood (F : X × Y → Y) (hF : ContDiff ℝ ∞ F)
    (a : X) (b : Y) (hi : (fderiv ℝ F (a,b) ∘L inr ℝ X Y).IsInvertible) :
    ∃ U : X → Y, ∃ S : Set X, IsOpen S ∧ a ∈ S ∧ ContDiffOn ℝ ∞ U S ∧ U a = b ∧
      ∀ x ∈ S, F (x,U x) = F (a,b) := by
  let U := hF.contDiffAt.implicitFunction (by simp) hi
  have hU : ContDiffAt ℝ ∞ U a := hF.contDiffAt.contDiffAt_implicitFunction (by simp) hi
  have hb : U a = b := hF.contDiffAt.implicitFunction_apply_self (by simp) hi
  have hc : ∀ᶠ x in 𝓝 a, ContDiffAt ℝ 1 U x :=
    (hU.of_le (by simp : (1:ℕ∞ω) ≤ (∞:ℕ∞ω))).eventually (by simp)
  have hid : Continuous (fun p : X × Y => fderiv ℝ F p ∘L inr ℝ X Y) :=
    (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  have hin : ∀ᶠ p in 𝓝 (a,b), (fderiv ℝ F p ∘L inr ℝ X Y).IsInvertible :=
    hid.continuousAt (isOpen_invertible_endomorphism.mem_nhds hi)
  have hgraph : ContinuousAt (fun x => (x,U x)) a := continuousAt_id.prodMk hU.continuousAt
  have hgi : ∀ᶠ x in 𝓝 a, (fderiv ℝ F (x,U x) ∘L inr ℝ X Y).IsInvertible :=
    hgraph (by simpa only [hb] using! hin)
  have heq : ∀ᶠ x in 𝓝 a, F (x,U x) = F (a,b) :=
    hF.contDiffAt.eventually_apply_implicitFunction (by simp) hi
  obtain ⟨V,hVsub,hV,hbase⟩ := mem_nhds_iff.mp
    (hF.contDiffAt.eventually_apply_eq_iff_implicitFunction (by simp) hi)
  have hgin : ∀ᶠ x in 𝓝 a, (x,U x) ∈ V :=
    hgraph (by simpa only [hb] using! hV.mem_nhds hbase)
  obtain ⟨S,hSsub,hS,ha⟩ := mem_nhds_iff.mp (hc.and (hgi.and (heq.and hgin)))
  refine ⟨U,S,hS,ha,?_,hb,fun x hx => (hSsub hx).2.2.1⟩
  intro x hx
  have hh := hSsub hx
  let W := hF.contDiffAt.implicitFunction (by simp) hh.2.1
  have hW : ContDiffAt ℝ ∞ W x := hF.contDiffAt.contDiffAt_implicitFunction (by simp) hh.2.1
  have hwx : W x = U x := hF.contDiffAt.implicitFunction_apply_self (by simp) hh.2.1
  have hWgraph : ContinuousAt (fun z => (z,W z)) x := continuousAt_id.prodMk hW.continuousAt
  have hWV : ∀ᶠ z in 𝓝 x, (z,W z) ∈ V := hWgraph (by simpa only [hwx] using hV.mem_nhds hh.2.2.2)
  have hev : U =ᶠ[𝓝 x] W := by
    filter_upwards [hWV,hF.contDiffAt.eventually_apply_implicitFunction (by simp) hh.2.1] with z hz hz'
    apply (hVsub hz).mp
    exact hz'.trans hh.2.2.1
  exact (hW.congr_of_eventuallyEq hev).contDiffWithinAt

end WeakMTWTransport

end

end OAI
