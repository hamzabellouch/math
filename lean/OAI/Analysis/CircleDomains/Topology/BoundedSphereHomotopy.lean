import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan
import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension
import Mathlib.Topology.Homotopy.Basic

namespace OAI

/-! A bounded-displacement plane map extends to a sphere map homotopic
to the identity by the straight-line homotopy. Uniform properness proves
joint continuity at infinity. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

 def straightSphereHomotopy (F : ℂ → ℂ) (t : unitInterval × Sphere) : Sphere :=
  extendAtInfinity (fun z => z+(t.1:ℝ) • (F z-z)) t.2

 theorem continuous_straightSphereHomotopy {F : ℂ → ℂ} (hF : Continuous F)
    {C : ℝ} (_hC : 0 ≤ C) (hbound : ∀ z, ‖F z-z‖ ≤ C) :
    Continuous (straightSphereHomotopy F) := by
  have hdiff (s : unitInterval) (z : ℂ) : ‖(z+(s:ℝ) • (F z-z))-z‖ ≤ C := by
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
    exact (mul_le_mul s.property.2 (hbound z) (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  rw [continuous_iff_continuousAt]
  rintro ⟨s,p⟩
  cases p using OnePoint.rec with
  | coe z =>
    have hc : ContinuousAt finiteCoord (z : Sphere) :=
      (continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds (by simp))
    have hsnd : ContinuousAt (fun t : unitInterval × Sphere => t.2) (s,(z : Sphere)) :=
      continuous_snd.continuousAt
    have hcoord : ContinuousAt (fun t : unitInterval × Sphere => finiteCoord t.2)
        (s,(z : Sphere)) := hc.comp_of_eq hsnd rfl
    have hg : ContinuousAt (fun t : unitInterval × Sphere =>
        (finiteCoord t.2+(t.1:ℝ) • (F (finiteCoord t.2)-finiteCoord t.2) : ℂ)) (s,(z:Sphere)) :=
      hcoord.add
        ((continuous_subtype_val.comp continuous_fst).continuousAt.smul
          ((hF.continuousAt.comp hcoord).sub
            hcoord))
    apply (OnePoint.continuous_coe.continuousAt.comp hg).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually
      (isClosed_singleton.isOpen_compl.mem_nhds (show (z:Sphere) ∉ {OnePoint.infty} by simp))] with t ht
    obtain ⟨w,hw⟩ := OnePoint.ne_infty_iff_exists.mp ht
    simp only [straightSphereHomotopy,Function.comp_apply]
    rw [← hw]
    simp only [extendAtInfinity_coe,finiteCoord_coe]
  | infty =>
    change Tendsto (straightSphereHomotopy F) (𝓝 (s,OnePoint.infty)) (𝓝 OnePoint.infty)
    apply _root_.tendsto_nhds.mpr
    intro O hO hOO
    have hK := ((OnePoint.isOpen_iff_of_mem hOO).mp hO).2
    obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
    let B := ((↑) : ℂ → Sphere) '' closedBall 0 (R+C)
    have hB : IsClosed B :=
      (OnePoint.isClosed_image_coe).mpr ⟨isClosed_closedBall,isCompact_closedBall _ _⟩
    have hBinf : OnePoint.infty ∉ B := OnePoint.infty_notMem_image_coe
    filter_upwards [continuous_snd.continuousAt.eventually
      (hB.isOpen_compl.mem_nhds hBinf)] with t ht
    change straightSphereHomotopy F t ∈ O
    cases hp : t.2 using OnePoint.rec with
    | infty => simpa only [straightSphereHomotopy,hp,extendAtInfinity_infty] using hOO
    | coe z =>
      have hz : R+C < ‖z‖ := by
        have hn : z ∉ closedBall 0 (R+C) := by
          intro hz
          exact ht ⟨z,hz,hp.symm⟩
        simpa only [mem_closedBall_zero_iff,not_le] using hn
      change extendAtInfinity (fun z => z+(t.1:ℝ) • (F z-z)) t.2 ∈ O
      rw [hp,extendAtInfinity_coe]
      by_contra hn
      have hsmall : ‖z+(t.1:ℝ) • (F z-z)‖ ≤ R := hR _ hn
      have htriangle := norm_le_norm_sub_add z (z+(t.1:ℝ) • (F z-z))
      rw [norm_sub_rev] at htriangle
      have hd := hdiff t.1 z
      linarith

 theorem homotopic_id_of_bounded_displacement {F : ℂ → ℂ} (hF : Continuous F)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, ‖F z-z‖ ≤ C)
    (hExt : Continuous (extendAtInfinity F)) :
    ContinuousMap.Homotopic (⟨extendAtInfinity F,hExt⟩ : C(Sphere,Sphere)) (ContinuousMap.id Sphere) := by
  apply ContinuousMap.Homotopic.symm
  refine ⟨{
    toFun := straightSphereHomotopy F
    continuous_toFun := continuous_straightSphereHomotopy hF hC hbound
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    cases x using OnePoint.rec <;> simp [straightSphereHomotopy,extendAtInfinity]
  · intro x
    cases x using OnePoint.rec <;> simp [straightSphereHomotopy,extendAtInfinity]

end CircleDomainRigidity

end

end OAI
