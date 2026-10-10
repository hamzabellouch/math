import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaCharge
import OAI.Combinatorics.UniformKServer.EpochSide

namespace OAI

                                      
section

/-! Prepared side jumps: no parameter drift is charged at unchanged held
coordinates. Wholesale jumps use the actual prepared feasibility inequality. -/
noncomputable section
namespace UniformKServer.EpochSideCharge
open Finset UniformKServer.AdaptiveSide UniformKServer.EpochSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem whole {p q : Config ι} (hp : valid p) (hq : valid q)
    (B v : ι → ℝ) {D : ℝ} (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i)
    (hv : DomainTransport.domain q.active 11 v)
    (hf : ∀ i, D*v i ≤ 5*B i) :
    |potential q B D v-potential p B D v| ≤ 6*(slope p+slope q)*(∑ i, B i) := by
  unfold potential SideTracker.potential
  rw [←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have hp' := SideParameterChanges.coordinate_bound_all hp i (hv.1 i) (coordinate_le_sum hv i) (B:=B i) (D:=D)
  have hq' := SideParameterChanges.coordinate_bound_all hq i (hv.1 i) (coordinate_le_sum hv i) (B:=B i) (D:=D)
  rw [abs_of_nonneg hD,abs_of_nonneg (hB i)] at hp' hq'
  have hp'' := mul_le_mul_of_nonneg_left (hf i) (slope_nonneg hp)
  have hq'' := mul_le_mul_of_nonneg_left (hf i) (slope_nonneg hq)
  exact (abs_sub _ _).trans (by nlinarith)

theorem jump {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    (ell cw : ℝ) (b : ℕ → ℝ)
    (hb : ∀ t, SideReferenceSchedule.reset a p t=false → b t=b (t+1))
    (hp : ∀ t, AdaptiveSide.valid (param a p ell cw b t)) (t : ℕ) (B v : ι → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*a (t+1) i)
    (hv : DomainTransport.domain (param a p ell cw b (t+1)).active 11 v)
    (hf : ∀ i, D*v i ≤ ((param a p ell cw b t).b+theta (param a p ell cw b t) i)*B i) :
    |potential (param a p ell cw b (t+1)) B D v-potential (param a p ell cw b t) B D v| ≤
      480*(2000*(ell/cw+1))*(EpochAlphaCharge.sizeCharge (a t) (a (t+1))+
        SideReferenceSchedule.wholesale a p t) := by
  have hK : 0 ≤ 2000*(ell/cw+1) := slope_nonneg (hp t)
  have hprep := SideParameterChanges.prepared_upper (hp t) B v D hB hf
  by_cases hr : SideReferenceSchedule.reset a p t=true
  · have hh := whole (hp t) (hp (t+1)) B v hD hB hv hprep
    have hsb := sum_le_sum (s:=univ) (fun i _ => hBb i)
    rw [←mul_sum] at hsb
    change _ ≤ 40*EpochGeometry.total (a (t+1)) at hsb
    have hmul := mul_le_mul_of_nonneg_left hsb hK
    have hsz := mul_nonneg hK (EpochAlphaCharge.size_nonneg (ha t) (ha (t+1)))
    have ht := mul_nonneg hK (EpochGeometry.total_nonneg (ha t))
    change |potential (param a p ell cw b (t+1)) B D v-potential (param a p ell cw b t) B D v| ≤
      6*(2000*(ell/cw+1)+2000*(ell/cw+1))*(∑ i, B i) at hh
    rw [SideReferenceSchedule.wholesale,ite_eq_left hr]
    nlinarith
  · have hr' := Bool.eq_false_iff.mpr hr
    have he := EpochAlphaCharge.not_reset_base hr'
    have hh := SideParameterChanges.parameter_jump (hp t) (hp (t+1))
      (congrArg EpochGeometry.total he) rfl rfl (hb t hr') B v hD hB hv hprep
    have hsp : (∑ i, if SideParameterChanges.size (param a p ell cw b t) i=
        SideParameterChanges.size (param a p ell cw b (t+1)) i then 0 else B i) ≤
        ∑ i, if a t i=a (t+1) i then 0 else B i := by
      apply sum_le_sum
      intro i _
      by_cases hi : a t i=a (t+1) i
      · have hj := size_same (ha t) (ha (t+1)) he ell cw (b t) (b (t+1)) hi
        change SideParameterChanges.size (param a p ell cw b t) i=
          SideParameterChanges.size (param a p ell cw b (t+1)) i at hj
        simp only [ite_eq_left hi,ite_eq_left hj,le_refl]
      · simp only [ite_eq_right hi]
        split_ifs
        · exact hB i
        · exact le_rfl
    have hsp' := (hsp.trans (EpochAlphaCharge.sparse (ha t) hBb))
    have hmul := mul_le_mul_of_nonneg_left hsp' hK
    change |potential (param a p ell cw b (t+1)) B D v-potential (param a p ell cw b t) B D v| ≤
      6*(2000*(ell/cw+1)+2000*(ell/cw+1))*_ at hh
    rw [SideReferenceSchedule.wholesale,ite_eq_right hr,add_zero]
    nlinarith

end UniformKServer.EpochSideCharge

end


end

end OAI
