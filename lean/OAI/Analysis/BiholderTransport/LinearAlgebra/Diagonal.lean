import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactDifferential
import OAI.Analysis.BiholderTransport.Regularity.Reversal

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section Diagonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma diagonal_stationary_hessian_identity {F : E×E → ℝ} {p : E}
    (hF : ContDiffAt ℝ 2 F (p,p))
    (hstat : ∀ᶠ v in 𝓝 p, ∀ k, fderiv ℝ F (v,v) (0,k)=0) (a k : E) :
    fderiv ℝ (fderiv ℝ F) (p,p) (0,a) (0,k)=
      -fderiv ℝ (fderiv ℝ F) (p,p) (a,0) (0,k) := by
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let L : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)
  have hD := ((hdf.hasFDerivAt.comp (f := fun v : E => (v,v)) p L.hasFDerivAt).clm_apply
    (hasFDerivAt_const ((0:E),k) p)).fderiv
  have heq : (fun v : E => fderiv ℝ F (v,v) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have hz : fderiv ℝ (fun v : E => fderiv ℝ F (v,v) (0,k)) p=0 := by
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have H := congrArg (fun A : E →L[ℝ] ℝ => A a) (hD.symm.trans hz)
  simp only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,map_zero,zero_add,
    ContinuousLinearMap.flip_apply,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at H
  have hsplit : (a,a)=(a,0)+((0:E),a) := by ext <;> simp
  rw [hsplit,map_add,add_apply] at H
  linarith
end Diagonal
section SplitFactor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma diagonalSplitAction_hessian_identity {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p∈injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,a) (0,k)=
      -fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (a,0) (0,k) := by
  exact diagonal_stationary_hessian_identity
    ((diagonalSplitAction_contDiffAt hleft hright).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((split_regular_legs_near hleft hright).mono
      (fun v hv k => diagonalSplitAction_stationary ht ht1 hv.1 hv.2 k)) a k

lemma exists_suffix_log_in_prefix_coordinates {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ q : TangentSpace 𝓘(ℝ,Model n) x →
        TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      ContDiffAt ℝ ∞ q p ∧
      (∀ᶠ v in 𝓝 p, q v∈injectivityDomain (riemannianExp x p)) ∧
      (∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (q v)=riemannianExp x (t • v)) := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let s := tangentScale (1-t) (sprayFlow t z)
  have hs : s.2∈injectivityDomain s.1 := hright
  have hr := reverseRay_injectivityDomain hs
  have he : (reverseRay s).1=riemannianExp x p := by
    change (sprayFlow 1 s).1=riemannianExp x p
    rw [←riemannianExp_eq_sprayFlow]
    exact shifted_exp_endpoint x p t
  have he' := reverseRay_endpoint s
  change riemannianExp (reverseRay s).1 (reverseRay s).2=(sprayFlow t z).1 at he'
  rw [←riemannianExp_smul] at he'
  generalize hrdef : reverseRay s=r at hr he he'
  rcases r with ⟨y,r⟩
  dsimp only at he hr he'
  subst y
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hr
  rw [he'] at hκ0 hκ hκright
  let q := fun v : TangentSpace 𝓘(ℝ,Model n) x => κ (riemannianExp x (t • v))
  have hE : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞
      (fun v => riemannianExp x (t • v)) p :=
    (contMDiff_riemannianExp_fiber x _).comp p (show ContDiffAt ℝ ∞ (fun v : TangentSpace 𝓘(ℝ,Model n) x => t • v) p from
      by fun_prop).contMDiffAt
  have hq : ContDiffAt ℝ ∞ q p := (hκ.comp p hE).contDiffAt
  refine ⟨q,hq,?_,hE.continuousAt.eventually hκright⟩
  apply hq.continuousAt.preimage_mem_nhds
  apply (isOpen_injectivityDomain _).mem_nhds
  change κ (riemannianExp x (t • p))∈_
  rw [hκ0]
  exact hr

end SplitFactor
end WeakMTWTransport

end

end

end

end OAI
