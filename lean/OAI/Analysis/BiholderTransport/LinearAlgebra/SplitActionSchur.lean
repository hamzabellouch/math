import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.StrictDividedAction
import OAI.Analysis.BiholderTransport.LinearAlgebra.StationarySchur
import OAI.Analysis.BiholderTransport.Calculus.SliceDerivatives

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

lemma splitNormalAction_schur_equality {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : p∈injectivityDomain x) (ht : 0 < t) (ht1 : t < 1) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      (∀ d k, fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p)
        (0,R d) (0,k)=inner ℝ d k) ∧
      (∀ d, hessianValue x p d=hessianValue x (t • p) d/t-inner ℝ (R d) d) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := splitNormalAction x t p
  obtain ⟨b,hb,hb0,hcontact⟩ := exists_smooth_joining_selector hp ht ht1
  let R := fderiv ℝ b 0
  have hbd : HasFDerivAt b R 0 := (hb.differentiableAt (by simp)).hasFDerivAt
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hBc : ContDiffAt ℝ ∞ B (0,p) :=
    (splitNormalAction_contDiffAt hleft hright).comp (f := fun z : V×V => (p,z))
      (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ᶠ a in 𝓝 (0:V), DifferentiableAt ℝ (normalCost x p) a :=
    ((normalCost_contDiffAt hp).of_le (m := 1) (by simp)).eventually (by norm_num) |>.mono
      (fun _ h => h.differentiableAt (by norm_num))
  have hle : ∀ᶠ z in 𝓝 ((0:V),p), normalCost x p z.1 ≤ B z :=
    Eventually.of_forall (fun z => normalCost_le_splitNormalAction x p z.1 z.2 ht ht1)
  have hstat : ∀ᶠ a in 𝓝 (0:V), ∀ k : V, fderiv ℝ B (a,b a) (0,k)=0 := by
    have hmap := (hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk hbd
    have hBnear : ∀ᶠ a in 𝓝 (0:V), DifferentiableAt ℝ B (a,b a) := by
      have HC : ContDiffAt ℝ 1 B (0,b 0) := by rw [hb0]; exact hBc.of_le (by simp)
      exact (hmap.continuousAt.eventually (HC.eventually (by norm_num))).mono
        (fun _ h => h.differentiableAt (by norm_num))
    filter_upwards [hBnear,hcontact] with a ha hc
    intro k
    have hlocal : IsLocalMin (fun v : V => B (a,v)) (b a) := by
      apply Filter.Eventually.of_forall
      intro v
      change splitNormalAction x t p (a,b a) ≤ splitNormalAction x t p (a,v)
      rw [←hc]
      exact normalCost_le_splitNormalAction x p a v ht ht1
    have hd := ha.hasFDerivAt.comp (f := fun v : V => (a,v)) (b a)
      ((hasFDerivAt_const a (b a)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (b a)))
    have H := congrArg (fun A : V →L[ℝ] ℝ => A k) (hd.fderiv.symm.trans hlocal.fderiv_eq_zero)
    change fderiv ℝ B (a,b a) (0,k)=0 at H
    exact H
  have hmix (d k : V) : fderiv ℝ (fderiv ℝ B) (0,p) (d,0) (0,k)= -inner ℝ d k := by
    rw [splitNormalAction_mixed_pairing ht.ne' hleft hright,real_inner_comm]
  refine ⟨R,stationary_graph_middle_equation hB hbd hb0 hstat hmix,?_⟩
  intro d
  have HH := stationary_contact_hessian hB hbd hb0 hf hle hcontact
  have HE := congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ => A d d) HH.fderiv
  change normalHessian x p d d = fderiv ℝ (fderiv ℝ B) (0,p) (d,R d) (d,0) at HE
  have hsplit : (d,R d)=((d,0):V×V)+(0,R d) := by simp
  rw [hsplit,map_add,add_apply,(hB.isSymmSndFDerivAt (by norm_num)).eq (0,R d) (d,0),hmix] at HE
  rw [←splitTrialValue_eq_hessian hleft hright,splitTrialValue_source] at HE
  rw [hessianValue_eq_normalHessian hp,HE,real_inner_comm d (R d)]
  ring

end WeakMTWTransport

end

end OAI
