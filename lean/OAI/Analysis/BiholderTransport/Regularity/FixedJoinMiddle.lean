import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.StationaryPullback

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

section
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinMiddle_eq_slice {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p v w=fderiv ℝ
      (fderiv ℝ (fun b => fixedJoinAction x h T p (0,b))) p v w := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let I : V →L[ℝ] V×V := (0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine (f := fixedJoinAction x h T p) I 0 p
    (by simpa [I] using hB) v w
  simpa [I,fixedJoinMiddle_apply] using H.symm

lemma fixedJoinMiddle_symmetric {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p v w=fixedJoinMiddle x h T p w v :=
  (hB.isSymmSndFDerivAt (by norm_num)).eq (0,v) (0,w)

end

lemma fixedJoinMiddle_one_nonneg {x : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hh : 0<h) (hh1 : h<1)
    (hp : p∈minimizingVectors x) (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    0 ≤ fixedJoinMiddle x h 1 p v v := by
  have HB := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (p,z))
    (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have HB2 := HB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := fixedJoinMiddle_rescale (x := x) (h := h) (p := p) (T := 1)
    (by norm_num) (by simpa only [Function.comp_def,div_one,one_smul] using HB2) v v
  simp only [div_one,one_smul,one_mul] at H
  rw [H,←splitTrialValue_eq_hessian hleft hright]
  exact splitTrialValue_nonneg hh hh1 hp hleft hright

end WeakMTWTransport

end

end OAI
