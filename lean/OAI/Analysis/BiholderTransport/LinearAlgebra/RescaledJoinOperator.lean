import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.InverseProfile

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteRescaled (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma fixedJoinAction_regular_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : V×V => (T • p,z))
    (0,T • p) (contDiffAt_const.prodMk contDiffAt_id)
  change ContDiffAt ℝ ∞ (splitNormalAction x (h/T) (T • p)) (0,T • p) at hBc
  have H := hBc.comp (f := fun z : V×V => (z.1,T • z.2)) (0,p)
    (contDiffAt_fst.prodMk ((contDiffAt_const (c := T)).smul contDiffAt_snd))
  have heq : fixedJoinAction x h T p=(fun z : V×V =>
      T⁻¹*splitNormalAction x (h/T) (T • p) (z.1,T • z.2)) :=
    funext (fixedJoinAction_rescale x hT.ne' p)
  rw [heq]
  exact contDiffAt_const.mul H

lemma fixedJoinOperator_regular_rescale {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T) :
    fixedJoinOperator x h T p=T • fixedJoinOperator x (h/T) 1 (T • p) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (T • p,z))
    (0,T • p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  ext d
  apply ext_inner_right ℝ
  intro k
  simp only [smul_apply,real_inner_smul_left,fixedJoinOperator_inner]
  rw [fixedJoinMiddle_rescale hT.ne' hB]
  have H := fixedJoinMiddle_rescale (x := x) (h := h/T) (p := T • p) (T := 1)
    (by norm_num) (by simpa only [Function.comp_def,div_one,one_smul] using hB) d k
  simpa only [div_one,one_smul,one_mul] using congrArg (fun r : ℝ => T*r) H.symm

lemma fixedJoinOperator_regular_nonneg {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    0 ≤ inner ℝ (fixedJoinOperator x h T p v) v := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  have hmin := injectivityDomain_subset_minimizingVectors x hp
  have hleft := contracted_minimizer_mem_injectivityDomain hmin ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  rw [fixedJoinOperator_regular_rescale hp hh hhT,
    smul_apply,real_inner_smul_left,fixedJoinOperator_inner]
  exact mul_nonneg hT.le (fixedJoinMiddle_one_nonneg ht ht1 hmin hleft hright v)

lemma fixedJoinOperator_inverse_nonneg {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T)
    (hDR : ∀ v, fixedJoinOperator x h T p (R v)=v)
    (v : TangentSpace 𝓘(ℝ,Model n) x) : 0 ≤ inner ℝ (R v) v := by
  have H := fixedJoinOperator_regular_nonneg hp hh hhT (R v)
  rw [hDR,real_inner_comm] at H
  exact H

end WeakMTWTransport

end

end OAI
