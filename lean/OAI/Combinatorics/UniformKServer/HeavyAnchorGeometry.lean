import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyProcess
import OAI.Combinatorics.UniformKServer.HeavySeparation
import OAI.Combinatorics.UniformKServer.AnchorRamp
import OAI.Combinatorics.UniformKServer.GeometricMass

namespace OAI

                                          
section

/-! Literal moving-label geometry and potential release for one heavy update. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem moved_step (S T : State X Λ r) (hr : 0≤r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R∈Set.Icc (16*r) (20*r)) (l : Λ)
    (ho : l∈S.present) (hn : l∈(step S T hr hΛ h x R hR).present)
    (hm : S.center l≠(step S T hr hΛ h x R hR).center l) :
    h ∧ (step S T hr hΛ h x R hR).center l=x ∧ 8*r<dist (S.center l) x ∧
      dist (S.center l) x≤40*r ∧
      ∀ p,covers (step S T hr hΛ h x R hR) l p↔dist x p≤R := by
  unfold step at hn hm ⊢
  split_ifs at hn hm ⊢ with ht
  · have he : l=chosen S x R (fresh S T hr hΛ) := by
      by_contra hl
      exact hm (by simp only [HeavyRecords.insert,Function.update_of_ne hl])
    have hd := ht.2 (S.center l) (mem_image.mpr ⟨l,ho,rfl⟩)
    have hu := reused_distance S hr x R hR _ (fresh_absent S T hr hΛ).1 l ho hn
    have ha : (HeavyRecords.insert S hr x R hR (fresh S T hr hΛ) (fresh_absent S T hr hΛ).1).center l=x := by
      simp only [HeavyRecords.insert,he,Function.update_self]
    rw [ha] at hu
    refine ⟨ht.1,ha,by simpa only [dist_comm] using hd,hu,?_⟩
    intro p
    rw [covers_insert_iff]
    have hs := chosen_not_survivor S hr x R hR.2 (fresh S T hr hΛ) (fresh_absent S T hr hΛ).1
    simp only [he,hs,true_and,false_and,or_false]
  · exact (hm rfl).elim

theorem geom_mass (μ : X→ℝ) (x : X) (R : ℝ) :
    AnchorRamp.mass μ (AnchorRamp.ball x R)=GeometricMass.mass μ x R := by
  simp only [AnchorRamp.mass,AnchorRamp.ball,sum_filter,GeometricMass.mass]

theorem release (S T : State X Λ r) (hr : 0<r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R∈Set.Icc (16*r) (20*r)) (l : Λ)
    (ho : l∈S.present) (hn : l∈(step S T hr.le hΛ h x R hR).present)
    (hm : S.center l≠(step S T hr.le hΛ h x R hR).center l)
    (μ : X→ℝ) (hμ : ∀ p,0≤μ p) (γ δ b u : ℝ) (hγ : γ<1) (hδ : δ≤1/100)
    (hb : 0≤b) (hu : 0<u)
    (hH : 1≤GeometricMass.mass μ x (γ*r))
    (hh : h→GeometricMass.mass μ x (51200*r)≤(1+δ)*GeometricMass.mass μ x (γ*r))
    (hd : u≤(6/5)*(1+∑ p∈univ.filter (covers (step S T hr.le hΛ h x R hR) l),μ p)) :
    r*b/u*(∑ p∈univ.filter (covers (step S T hr.le hΛ h x R hR) l),μ p*
      (AnchorRamp.value r ((step S T hr.le hΛ h x R hR).center l) p-AnchorRamp.value r (S.center l) p))≤
      -(1/4)*r*b := by
  obtain ⟨htrue,ha,hfar,_hclose,hcovers⟩ := moved_step S T hr.le hΛ h x R hR l ho hn hm
  let C := univ.filter (covers (step S T hr.le hΛ h x R hR) l)
  have hsub : AnchorRamp.ball x (γ*r)⊆C := by
    intro p hp
    apply mem_filter.mpr
    refine ⟨mem_univ _,(hcovers p).mpr ?_⟩
    have hg : γ*r≤R := by nlinarith [hR.1]
    exact (mem_filter.mp hp).2.trans hg
  have houter : C⊆AnchorRamp.ball x (51200*r) := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _,((hcovers p).mp (mem_filter.mp hp).2).trans (by nlinarith [hR.2])⟩
  have hc : AnchorRamp.mass μ C≤GeometricMass.mass μ x (51200*r) := by
    rw [←geom_mass]
    exact sum_le_sum_of_subset_of_nonneg houter (fun p _ _=>hμ p)
  have hc' : AnchorRamp.mass μ C≤(1+δ)*AnchorRamp.mass μ (AnchorRamp.ball x (γ*r)) := by
    rw [geom_mass]
    exact hc.trans (hh htrue)
  have hdrop := AnchorRamp.integral_drop μ hμ C r γ δ hr hγ (S.center l) x hfar hsub hc'
  have hden : u≤(6/5)*(2+δ)*AnchorRamp.mass μ (AnchorRamp.ball x (γ*r)) := by
    rw [geom_mass] at hc' ⊢
    change u≤(6/5)*(1+AnchorRamp.mass μ C) at hd
    nlinarith only [hd,hc',hH]
  simpa only [ha] using AnchorRamp.payment r b u _ _ δ hr.le hb hu (by rw [geom_mass]; linarith) hδ hden hdrop

end UniformKServer.HeavyProcess

end


end

end OAI
