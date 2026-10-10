import Mathlib
import OAI.Analysis.Crouzeix.ConformalCollar

namespace OAI

/-! Interior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

namespace CrouzeixHilbert.Conformal

structure InteriorCollar (U : Set ℂ) where
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  closure_subset_domain : closure U ⊆ domain
  radius : ℝ
  one_lt_radius : 1 < radius
  f : ℂ → ℂ
  h : ℂ → ℂ
  analytic_f : AnalyticOnNhd ℂ f domain
  analytic_h : AnalyticOnNhd ℂ h (ball 0 radius)
  injective_f : InjOn f domain
  injective_h : InjOn h (ball 0 radius)
  bijective_f : BijOn f U (ball 0 1)
  bijective_h : BijOn h (ball 0 1) U
  closed_f : BijOn f (closure U) (closedBall 0 1)
  closed_h : BijOn h (closedBall 0 1) (closure U)
  inverse : InvOn h f domain (f '' domain)
  disk_subset : ball 0 radius ⊆ f '' domain
  boundary_norm : ∀ z ∈ frontier U, ‖f z‖ = 1

theorem exists_interiorCollar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) (hne : U.Nonempty)
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) : Nonempty (InteriorCollar U) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨V,ρ,f,h,hV,hUV,hρ,hfa,hha,hfi,hhi,hfb,hhb,hfc,hhc,_,_,_,hfn,hinv,hd⟩ :=
    exists_conformal_collar hU hb hc ha hchart
  exact ⟨⟨V,hV,hUV,ρ,hρ,f,h,hfa,hha,hfi,hhi,hfb,hhb,hfc,hhc,hinv,hd,hfn⟩⟩

namespace InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma zero_mem_disk : (0 : ℂ) ∈ ball 0 R.radius := mem_ball_zero_iff.mpr (by simpa using R.one_lt_radius.trans' zero_lt_one)

lemma h_zero_mem : R.h 0 ∈ U := R.bijective_h.mapsTo (mem_ball_self zero_lt_one)

lemma f_h_zero : R.f (R.h 0) = 0 := R.inverse.2 (R.disk_subset R.zero_mem_disk)

lemma closedDisk_subset : closedBall (0 : ℂ) 1 ⊆ ball 0 R.radius := closedBall_subset_ball R.one_lt_radius

lemma h_mem_domain {z : ℂ} (hz : z ∈ ball 0 R.radius) : R.h z ∈ R.domain := by
  obtain ⟨w,hw,hwz⟩ := R.disk_subset hz
  rw [← hwz, R.inverse.1 hw]
  exact hw

end InteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
