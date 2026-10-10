import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.SplitPairing

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logJoinAction (z : M) (a : ℝ) (P : E → ℝ)
    (g : E → TangentSpace 𝓘(ℝ,Model n) z)
    (w : TangentSpace 𝓘(ℝ,Model n) z × E) : ℝ :=
  P w.2+a*normalCost z w.1 (g w.2)

lemma logJoinAction_contDiffAt {z : M} {a : ℝ} {P : E → ℝ}
    {g : E → TangentSpace 𝓘(ℝ,Model n) z} {p : E}
    {q : TangentSpace 𝓘(ℝ,Model n) z}
    (hq : q∈injectivityDomain z) (hP : ContDiffAt ℝ ∞ P p)
    (hg : ContDiffAt ℝ ∞ g p) (hg0 : g p=0) :
    ContDiffAt ℝ ∞ (logJoinAction z a P g) (q,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  have hA : ContMDiffAt 𝓘(ℝ,V×E) 𝓘(ℝ,Model n) ∞
      (fun w : V×E => riemannianExp z (g w.2)) (q,p) :=
    (contMDiff_riemannianExp_fiber z _).comp (q,p)
      ((hg.comp (q,p) contDiffAt_snd).contMDiffAt)
  have hB : ContMDiffAt 𝓘(ℝ,V×E) 𝓘(ℝ,Model n) ∞
      (fun w : V×E => riemannianExp z w.1) (q,p) :=
    (contMDiff_riemannianExp_fiber z _).comp (q,p) contDiffAt_fst.contMDiffAt
  have hC : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun w : M×M => cost w.1 w.2) (riemannianExp z (g p),riemannianExp z q) := by
    simpa only [hg0,riemannianExp_zero] using
      cost_contMDiffAt_of_injectivityDomain
        (⟨z,q⟩ : TangentBundle 𝓘(ℝ,Model n) M) hq
  have HC := (hC.comp (f := fun w : V×E =>
    (riemannianExp z (g w.2),riemannianExp z w.1)) (q,p) (hA.prodMk hB)).contDiffAt
  change ContDiffAt ℝ ∞ (fun w : V×E => normalCost z w.1 (g w.2)) (q,p) at HC
  exact (hP.comp (q,p) contDiffAt_snd).add (contDiffAt_const.mul HC)

lemma logJoinAction_middle_gradient {z : M} {a : ℝ} {P : E → ℝ}
    {g : E → TangentSpace 𝓘(ℝ,Model n) z} {p : E}
    {q : TangentSpace 𝓘(ℝ,Model n) z}
    (hq : q∈injectivityDomain z) (hP : DifferentiableAt ℝ P p)
    (hg : DifferentiableAt ℝ g p) (hg0 : g p=0)
    (hB : DifferentiableAt ℝ (logJoinAction z a P g) (q,p)) (k : E) :
    fderiv ℝ (logJoinAction z a P g) (q,p) (0,k)=
      fderiv ℝ P p k-a*inner ℝ q (fderiv ℝ g p k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  have hC : DifferentiableAt ℝ (normalCost z q) (g p) := by
    rw [hg0]
    exact (normalCost_contDiffAt hq).differentiableAt (by simp)
  have hd := hP.hasFDerivAt.add ((hC.hasFDerivAt.comp p hg.hasFDerivAt).const_smul a)
  have HI := (hasFDerivAt_const q p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hD := hB.hasFDerivAt.comp (f := fun b : E => (q,b)) p HI
  have H := congrArg (fun L : E →L[ℝ] ℝ => L k) (hD.unique hd)
  change fderiv ℝ (logJoinAction z a P g) (q,p) (0,k)=
    fderiv ℝ P p k+a*fderiv ℝ (normalCost z q) (g p) (fderiv ℝ g p k) at H
  rw [hg0,normalCost_fderiv_zero hq] at H
  linarith

lemma logJoinAction_mixed {z : M} {a : ℝ} {P : E → ℝ}
    {g : E → TangentSpace 𝓘(ℝ,Model n) z} {p : E}
    {q : TangentSpace 𝓘(ℝ,Model n) z}
    (hq : q∈injectivityDomain z) (hP : ContDiffAt ℝ ∞ P p)
    (hg : ContDiffAt ℝ ∞ g p) (hg0 : g p=0)
    (d : TangentSpace 𝓘(ℝ,Model n) z) (k : E) :
    fderiv ℝ (fderiv ℝ (logJoinAction z a P g)) (q,p) (d,0) (0,k)=
      -a*inner ℝ d (fderiv ℝ g p k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  have hB := logJoinAction_contDiffAt hq hP hg hg0 (a := a)
  have hB2 := hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HI := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const p q)
  have hd := (((hB2.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun r : V => (r,p)) q HI).clm_apply
      (hasFDerivAt_const ((0:V),k) q)
  have he : (fun r : V => fderiv ℝ (logJoinAction z a P g) (r,p) (0,k)) =ᶠ[𝓝 q]
      (fun r => fderiv ℝ P p k-a*inner ℝ r (fderiv ℝ g p k)) := by
    filter_upwards [(isOpen_injectivityDomain z).mem_nhds hq] with r hr
    exact logJoinAction_middle_gradient hr (hP.differentiableAt (by simp))
      (hg.differentiableAt (by simp)) hg0
      ((logJoinAction_contDiffAt hr hP hg hg0).differentiableAt (by simp)) k
  have hi : HasFDerivAt (fun r : V => fderiv ℝ P p k-a*inner ℝ r (fderiv ℝ g p k))
      (-a • innerSL ℝ (fderiv ℝ g p k)) q := by
    convert! ((((innerSL ℝ (fderiv ℝ g p k)).hasFDerivAt (x := q)).const_smul (-a)).const_add
      (fderiv ℝ P p k)) using 1
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,sub_eq_add_neg,real_inner_comm,neg_mul,innerSL_apply_apply]
  have H := congrArg (fun L : V →L[ℝ] ℝ => L d)
    ((hd.congr_of_eventuallyEq he.symm).unique hi)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,zero_add,
    ContinuousLinearMap.comp_zero,ContinuousLinearMap.flip_apply,
    smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_comm] at H
  exact H

end WeakMTWTransport

end

end OAI
