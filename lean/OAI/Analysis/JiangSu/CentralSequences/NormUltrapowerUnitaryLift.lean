import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerMaps
import OAI.Analysis.JiangSu.CStarAlgebras.CStarPolarNormalization

namespace OAI

section

noncomputable section
namespace NormUltra.QuotientAlgebra
open Filter Topology CStarPolar DirectComparison
open scoped CStarAlgebra ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local instance : Module ℝ (lp (fun _ : ℕ => A) ∞) := Module.complexToReal _

 def boundedUnitary (v : ℕ → unitary A) : BoundedFamilies (fun _ : ℕ => A) :=
  ⟨fun n => v n,memℓp_infty ⟨1,by
    rintro _ ⟨n,rfl⟩
    change ‖(v n:A)‖≤1
    by_cases h : Nontrivial A
    · let _ := h
      exact (CStarRing.norm_coe_unitary (v n)).le
    · have := not_nontrivial_iff_subsingleton.mp h
      rw [Subsingleton.elim (v n : A) 0,norm_zero]
      norm_num⟩⟩

omit [PartialOrder A] [StarOrderedRing A] in
 theorem unitary_representative (U : Ultrafilter ℕ)
    (u : unitary (QuotientAlgebra (fun _ : ℕ => A) U)) :
    ∃ v : ℕ → unitary A,mk U (boundedUnitary v)=(u : QuotientAlgebra (fun _ : ℕ => A) U) := by
  classical
  by_cases hA : Nontrivial A
  swap
  · have := not_nontrivial_iff_subsingleton.mp hA
    have hzero (x : BoundedFamilies (fun _ : ℕ => A)) : x=0 := by ext n; exact Subsingleton.elim _ _
    refine ⟨fun _ => 1,?_⟩
    obtain ⟨x,hx⟩ := mk_surjective (u : QuotientAlgebra (fun _ : ℕ => A) U)
    rw [←hx,hzero x,hzero (boundedUnitary (fun _ : ℕ => (1:unitary A)))]
  let _ := hA
  obtain ⟨x,hx⟩ := mk_surjective (u : QuotientAlgebra (fun _ : ℕ => A) U)
  let q := mkHom (A := fun _ : ℕ => A) (U := U)
  have hql : q (star x*x)=1 := by
    change star (mk U x)*mk U x=1
    rw [hx]
    exact u.2.1
  have hqr : q (x*star x)=1 := by
    change mk U x*star (mk U x)=1
    rw [hx]
    exact u.2.2
  have hleft : Tendsto (fun n => ‖star (x n)*x n-1‖) (U : Filter ℕ) (𝓝 0) :=
    (mk_eq_mk_iff (star x*x) (boundedDiagonal (1:A))).mp hql
  have hright : Tendsto (fun n => ‖x n*star (x n)-1‖) (U : Filter ℕ) (𝓝 0) :=
    (mk_eq_mk_iff (x*star x) (boundedDiagonal (1:A))).mp hqr
  let z := x*cfcₙ cutoffInverseSqrt (star x*x)
  have hzcoord (n : ℕ) : z n=CStarPolar.normalize (x n) := by
    change x n*(cfcₙ cutoffInverseSqrt (star x*x)) n= _
    rw [bounded_cfc_apply cutoffInverseSqrt cutoff_continuous cutoff_zero (star x*x)
      (fun n => IsSelfAdjoint.star_mul_self (x n)) n]
    rw [cfcₙ_eq_cfc cutoff_continuous.continuousOn cutoff_zero]
    rfl
  have hqz : q z=(u : QuotientAlgebra (fun _ : ℕ => A) U) := by
    rw [show q z=q x*q (cfcₙ cutoffInverseSqrt (star x*x)) from map_mul q x _,
      q.map_cfcₙ cutoffInverseSqrt (star x*x) cutoff_continuous.continuousOn cutoff_zero
        (by fun_prop) (IsSelfAdjoint.star_mul_self x) ((IsSelfAdjoint.star_mul_self x).map q),hql,
      cfcₙ_eq_cfc cutoff_continuous.continuousOn cutoff_zero,cfc_apply_one,cutoff_one,map_one,mul_one]
    exact hx
  let good (n : ℕ) : Prop := ‖star (x n)*x n-1‖<1/2 ∧ ‖x n*star (x n)-1‖<1/2
  have hgood : ∀ᶠ n in (U : Filter ℕ),good n :=
    (hleft.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and
      (hright.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  let v (n : ℕ) : unitary A := if hn : good n then
    ⟨CStarPolar.normalize (x n),normalize_unitary hn.1 hn.2⟩ else 1
  refine ⟨v,(show mk U (boundedUnitary v)=q z from ?_).trans hqz⟩
  apply (mk_eq_mk_iff _ _).mpr
  change Tendsto (fun n => ‖(boundedUnitary v) n-z n‖) (U : Filter ℕ) (𝓝 0)
  apply (tendsto_congr' (show (fun n => ‖(boundedUnitary v) n-z n‖) =ᶠ[(U : Filter ℕ)]
    fun _ => (0:ℝ) from ?_)).mpr tendsto_const_nhds
  filter_upwards [hgood] with n hn
  simp [boundedUnitary,v,hn,hzcoord n]

end NormUltra.QuotientAlgebra

end
end

end OAI
