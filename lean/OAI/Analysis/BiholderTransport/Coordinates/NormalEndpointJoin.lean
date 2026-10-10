import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.PrefixAction
import OAI.Analysis.BiholderTransport.Coordinates.FixedJoinSmooth
import OAI.Analysis.BiholderTransport.Regularity.FixedJoinMiddle

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

local instance tangentFiniteNormalEndpoint (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def normalEndpointJoinAction (x y : M) (h : ℝ)
    (q : TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost x (riemannianExp x (h • q.2))/h+
    cost (riemannianExp x (h • q.2)) (riemannianExp y q.1)/(1-h)

lemma normalEndpointJoinAction_contDiffAt {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hend : riemannianExp x p=y)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (normalEndpointJoinAction x y h) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  have hP : ContDiffAt ℝ ∞ (fun b : V => cost x (riemannianExp x (h • b))/h) p := by
    have H := (prefixAction_contDiffAt hleft).comp p (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [prefixAction,Function.comp_def,riemannianExp_zero] using H
  have hA : ContMDiffAt 𝓘(ℝ,W×V) 𝓘(ℝ,Model n) ∞
      (fun q : W×V => riemannianExp x (h • q.2)) (0,p) :=
    (contMDiff_riemannianExp_fiber x (h • p)).comp (0,p)
      (((contDiffAt_const (c := h)).smul contDiffAt_snd).contMDiffAt)
  have hB : ContMDiffAt 𝓘(ℝ,W×V) 𝓘(ℝ,Model n) ∞
      (fun q : W×V => riemannianExp y q.1) (0,p) :=
    (contMDiff_riemannianExp_fiber y 0).comp (0,p) contDiffAt_fst.contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  dsimp only at hc
  rw [shifted_exp_endpoint,hend] at hc
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (h • p),riemannianExp (n := n) y 0) := by
    simpa only [riemannianExp_smul,riemannianExp_zero] using hc
  exact (hP.comp (0,p) contDiffAt_snd).add ((hc'.comp (0,p) (hA.prodMk hB)).contDiffAt.div_const (1-h))

lemma normalEndpointJoinAction_factor {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hh1 : h<1) (hend : riemannianExp x p=y)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hL : ContDiffAt ℝ ∞ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v)
    (d k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h 1 p d k=
      -fderiv ℝ (fderiv ℝ (normalEndpointJoinAction x y h)) (0,p)
        (fderiv ℝ L p d,0) (0,k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := normalEndpointJoinAction (n := n) x y h
  have hB := normalEndpointJoinAction_contDiffAt hend hleft hright
  have hB2 := hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hBL : ContDiffAt ℝ 2 B (L p,p) := by simpa only [hLp] using hB2
  have hstat : ∀ᶠ v in 𝓝 p, ∀ k : V, fderiv ℝ B (L v,v) (0,k)=0 := by
    have hmap : ContinuousAt (fun v : V => (L v,v)) p := hL.continuousAt.prodMk continuousAt_id
    have hBn := hmap.eventually ((hBL.of_le (m := 1) (by norm_num)).eventually (by norm_num))
    filter_upwards [split_regular_legs_near hleft hright,hBn,hLi] with v hvreg hvB hvi
    change ContDiffAt ℝ 1 B (L v,v) at hvB
    intro k
    have heq : (fun b => B (L v,b))=(fun b => diagonalSplitAction x h (v,b)) := by
      funext b
      simp only [B,normalEndpointJoinAction,hvi,diagonalSplitAction,splitNormalAction,riemannianExp_zero]
    rw [←fderiv_snd_slice (hvB.differentiableAt (by norm_num)) k,heq,
      fderiv_snd_slice ((diagonalSplitAction_contDiffAt hvreg.1 hvreg.2).differentiableAt (by simp))]
    exact diagonalSplitAction_stationary hh hh1 hvreg.1 hvreg.2 k
  have hFactor := diagonal_stationary_factorization hBL
    (hL.differentiableAt (by simp)).hasFDerivAt hstat
  have hfixed := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq : (fun b : V => fixedJoinAction x h 1 p (0,b))=(fun b => B (0,b)) := by
    funext b
    simp only [fixedJoinAction,B,normalEndpointJoinAction,riemannianExp_zero,one_smul,hend]
  rw [fixedJoinMiddle_eq_slice hfixed,heq,second_fderiv_snd_slice hB2]
  simpa only [hLp] using hFactor d k

end WeakMTWTransport

end

end OAI
