import Mathlib
import OAI.Geometry.NearbyLagrangian.CompleteFlow
import OAI.Geometry.NearbyLagrangian.FlowLevels
import OAI.Geometry.NearbyLagrangian.Stabilization

namespace OAI

/-! Continuous parameter flows and paired negative-domain equivalences. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.ODE
open Set Filter Metric
open scoped Topology NNReal
variable {B E : Type*} [TopologicalSpace B] [CompactSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure ParamCompleteFlow (F : B × E → E) where
  toFun : (B × E) × ℝ → E
  continuous_toFun : Continuous toFun
  initial : ∀ b x, toFun ((b,x),0) = x
  derivative : ∀ b x t, HasDerivAt (fun s => toFun ((b,x),s))
    (F (b,toFun ((b,x),t))) t

namespace ParamCompleteFlow
variable {F : B × E → E} (φ : ParamCompleteFlow F)

def specialize (b : B) : CompleteFlow (fun x => F (b,x)) where
  toFun p := φ.toFun ((b,p.1),p.2)
  continuous_toFun := φ.continuous_toFun.comp
    ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  initial := φ.initial b
  derivative := φ.derivative b

end ParamCompleteFlow

theorem exists_paramCompleteFlow (F : B × E → E) (hF : Continuous F)
    {L K : ℝ≥0} (hL : ∀ b x, ‖F (b,x)‖ ≤ L)
    (hK : ∀ b, LipschitzWith K (fun x => F (b,x))) :
    Nonempty (ParamCompleteFlow F) := by
  let A : C(B,E) → C(B,E) := fun u =>
    ⟨fun b => F (b,u b), hF.comp (continuous_id.prodMk u.continuous)⟩
  have hLA (u : C(B,E)) : ‖A u‖ ≤ L :=
    ((A u).norm_le L.coe_nonneg).mpr (fun b => hL b (u b))
  have hKA : LipschitzWith K A := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    apply (ContinuousMap.dist_le (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
    intro b
    exact ((hK b).dist_le_mul (u b) (v b)).trans
      (mul_le_mul_of_nonneg_left
        (ContinuousMap.dist_le dist_nonneg |>.mp le_rfl b) K.coe_nonneg)
  obtain ⟨ψ⟩ := exists_completeFlow A hLA hKA
  let Φ : (B × E) × ℝ → E := fun p => ψ.toFun (ContinuousMap.const B p.1.2,p.2) p.1.1
  have hΦ : Continuous Φ := by
    exact continuous_eval.comp ((ψ.continuous_toFun.comp
      ((ContinuousMap.continuous_const'.comp (continuous_snd.comp continuous_fst)).prodMk
        continuous_snd)).prodMk (continuous_fst.comp continuous_fst))
  refine ⟨⟨Φ,hΦ,?_,?_⟩⟩
  · intro b x
    change ψ.toFun (ContinuousMap.const B x,0) b = x
    rw [ψ.initial]
    rfl
  · intro b x t
    have hd := (ContinuousMap.evalCLM ℝ b).hasFDerivAt.comp_hasDerivAt t
      (ψ.derivative (ContinuousMap.const B x) t)
    exact hd

end NearbyLagrangian.ODE

namespace NearbyLagrangian.ODE.CompleteFlow
open Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E} (φ : CompleteFlow F)

theorem push_sublevel {f : E → ℝ} (hf : Differentiable ℝ f)
    {S : Set E} (hS : ∀ x ∈ S, ∀ t, φ.toFun (x,t) ∈ S)
    (hF : ∀ x ∈ S, 0 ≤ fderiv ℝ f x (F x))
    {ε c δ : ℝ} (hδ : 0 ≤ δ) (htime : 2*ε ≤ c*δ)
    (hstrip : ∀ x ∈ S, |f x| ≤ ε → c ≤ fderiv ℝ f x (F x))
    {x : E} (hx : x ∈ S) (hfx : f x ≤ ε) : f (φ.toFun (x,-δ)) ≤ -ε := by
  by_contra! hfail
  have hmono := φ.observable_monotone hf hS hF hx
  have hd (t : ℝ) : HasDerivAt (fun s => f (φ.toFun (x,s)))
      (fderiv ℝ f (φ.toFun (x,t)) (F (φ.toFun (x,t)))) t :=
    (hf (φ.toFun (x,t))).hasFDerivAt.comp_hasDerivAt t (φ.derivative x t)
  have hs (t : ℝ) (ht : t ∈ Icc (-δ) 0) : |f (φ.toFun (x,t))| ≤ ε := by
    apply abs_le.mpr
    constructor
    · exact hfail.le.trans (hmono ht.1)
    · simpa only [φ.initial] using (hmono ht.2).trans (show f (φ.toFun (x,0)) ≤ ε by
        rw [φ.initial]; exact hfx)
  have hmean := (convex_Icc (-δ) (0:ℝ)).mul_sub_le_image_sub_of_le_deriv
    (show ContinuousOn (fun t => f (φ.toFun (x,t))) (Icc (-δ) 0) from
      ((hf.continuous.comp φ.continuous_toFun).comp
        (continuous_const.prodMk continuous_id)).continuousOn)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (C := c) (fun t ht => by
      rw [(hd t).deriv]
      exact hstrip _ (hS x hx t) (hs t (interior_subset ht)))
    (-δ) ⟨le_rfl,neg_nonpos.mpr hδ⟩ 0 ⟨neg_nonpos.mpr hδ,le_rfl⟩
    (neg_nonpos.mpr hδ)
  rw [φ.initial] at hmean
  linarith

end NearbyLagrangian.ODE.CompleteFlow

namespace NearbyLagrangian.Tubes
open Set Filter Metric
open scoped Topology NNReal
variable {B E : Type*} [TopologicalSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E]

def NegativeIn (S : Set E) (f : B × E → ℝ) := {p : B × E // p.2 ∈ S ∧ f p ≤ 0}
instance (S : Set E) (f : B × E → ℝ) : TopologicalSpace (NegativeIn S f) :=
  inferInstanceAs (TopologicalSpace {p : B × E // p.2 ∈ S ∧ f p ≤ 0})

def negativeInProjection (S : Set E) (f : B × E → ℝ) : C(NegativeIn S f,B) :=
  ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

def pairedNegativeFlowEquiv {F : B × E → E} (φ : ODE.ParamCompleteFlow F)
    {K : ℝ≥0} (hK : ∀ b, LipschitzWith K (fun x => F (b,x)))
    {S : Set E} (hS : ∀ b x, x ∈ S → ∀ t, φ.toFun ((b,x),t) ∈ S)
    {f g : B × E → ℝ} (hf : ∀ b, Differentiable ℝ (fun x => f (b,x)))
    (hg : ∀ b, Differentiable ℝ (fun x => g (b,x)))
    (hFf : ∀ b x, x ∈ S → 0 ≤ fderiv ℝ (fun x => f (b,x)) x (F (b,x)))
    (hFg : ∀ b x, x ∈ S → 0 ≤ fderiv ℝ (fun x => g (b,x)) x (F (b,x)))
    {ε c δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (htime : 2*ε ≤ c*δ)
    (hstripf : ∀ b x, x ∈ S → |f (b,x)| ≤ ε →
      c ≤ fderiv ℝ (fun x => f (b,x)) x (F (b,x)))
    (hstripg : ∀ b x, x ∈ S → |g (b,x)| ≤ ε →
      c ≤ fderiv ℝ (fun x => g (b,x)) x (F (b,x)))
    (hclose : ∀ b x, x ∈ S → |f (b,x)-g (b,x)| ≤ ε) :
    FiberwiseHomotopyEquiv (negativeInProjection S f) (negativeInProjection S g) := by
  have hto (b : B) (x : E) (hx : x ∈ S) (hfx : f (b,x) ≤ 0) :
      g (b,φ.toFun ((b,x),-δ)) ≤ 0 := by
    have hbound : g (b,x) ≤ ε := by
      have h := (abs_le.mp (hclose b x hx)).1
      linarith
    exact ((φ.specialize b).push_sublevel (hg b) (hS b) (hFg b) hδ htime
      (hstripg b) hx hbound).trans (neg_nonpos.mpr hε)
  have hinv (b : B) (x : E) (hx : x ∈ S) (hgx : g (b,x) ≤ 0) :
      f (b,φ.toFun ((b,x),-δ)) ≤ 0 := by
    have hbound : f (b,x) ≤ ε := by
      have h := (abs_le.mp (hclose b x hx)).2
      linarith
    exact ((φ.specialize b).push_sublevel (hf b) (hS b) (hFf b) hδ htime
      (hstripf b) hx hbound).trans (neg_nonpos.mpr hε)
  let a : C(NegativeIn S f,NegativeIn S g) :=
    ⟨fun p => ⟨(p.1.1,φ.toFun (p.1,-δ)),hS _ _ p.2.1 _,hto _ _ p.2.1 p.2.2⟩,
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (φ.continuous_toFun.comp (continuous_subtype_val.prodMk continuous_const))).subtype_mk _⟩
  let b : C(NegativeIn S g,NegativeIn S f) :=
    ⟨fun p => ⟨(p.1.1,φ.toFun (p.1,-δ)),hS _ _ p.2.1 _,hinv _ _ p.2.1 p.2.2⟩,
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (φ.continuous_toFun.comp (continuous_subtype_val.prodMk continuous_const))).subtype_mk _⟩
  have htime' (t : unitInterval) : -(1-(t:ℝ))*(2*δ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr t.2.2)) (by positivity)
  have hstayf (p : NegativeIn S f) (t : unitInterval) :
      f (p.1.1,φ.toFun (p.1,-(1-(t:ℝ))*(2*δ))) ≤ 0 := by
    have hm := (φ.specialize p.1.1).observable_monotone (hf p.1.1) (hS p.1.1)
      (hFf p.1.1) p.2.1 (htime' t)
    exact hm.trans (by simpa only [ODE.ParamCompleteFlow.specialize, φ.initial] using p.2.2)
  have hstayg (p : NegativeIn S g) (t : unitInterval) :
      g (p.1.1,φ.toFun (p.1,-(1-(t:ℝ))*(2*δ))) ≤ 0 := by
    have hm := (φ.specialize p.1.1).observable_monotone (hg p.1.1) (hS p.1.1)
      (hFg p.1.1) p.2.1 (htime' t)
    exact hm.trans (by simpa only [ODE.ParamCompleteFlow.specialize, φ.initial] using p.2.2)
  let left : (b.comp a).Homotopy (ContinuousMap.id _) := {
    toFun := fun p => ⟨(p.2.1.1,φ.toFun (p.2.1,-(1-(p.1:ℝ))*(2*δ))),
      hS _ _ p.2.2.1 _,hstayf p.2 p.1⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
        (φ.continuous_toFun.comp ((continuous_subtype_val.comp continuous_snd).prodMk
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).neg.mul continuous_const)))
    map_zero_left := by
      intro p
      apply Subtype.ext
      refine Prod.ext (by rfl) ?_
      change φ.toFun (p.1,-(1-(0:ℝ))*(2*δ)) =
        φ.toFun ((p.1.1,φ.toFun (p.1,-δ)),-δ)
      have h := (φ.specialize p.1.1).add (hK p.1.1) p.1.2 (-δ) (-δ)
      simpa only [ODE.ParamCompleteFlow.specialize, sub_zero, neg_one_mul,
        show -δ + -δ = -(2*δ) by ring] using h.symm
    map_one_left := by
      intro p
      apply Subtype.ext
      refine Prod.ext (by rfl) ?_
      change φ.toFun (p.val, -(1-(1:ℝ))*(2*δ)) = p.val.2
      simpa only [sub_self,neg_zero,zero_mul] using φ.initial p.val.1 p.val.2
    }
  let right : (a.comp b).Homotopy (ContinuousMap.id _) := {
    toFun := fun p => ⟨(p.2.1.1,φ.toFun (p.2.1,-(1-(p.1:ℝ))*(2*δ))),
      hS _ _ p.2.2.1 _,hstayg p.2 p.1⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
        (φ.continuous_toFun.comp ((continuous_subtype_val.comp continuous_snd).prodMk
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).neg.mul continuous_const)))
    map_zero_left := by
      intro p
      apply Subtype.ext
      refine Prod.ext (by rfl) ?_
      change φ.toFun (p.1,-(1-(0:ℝ))*(2*δ)) =
        φ.toFun ((p.1.1,φ.toFun (p.1,-δ)),-δ)
      have h := (φ.specialize p.1.1).add (hK p.1.1) p.1.2 (-δ) (-δ)
      simpa only [ODE.ParamCompleteFlow.specialize, sub_zero, neg_one_mul,
        show -δ + -δ = -(2*δ) by ring] using h.symm
    map_one_left := by
      intro p
      apply Subtype.ext
      refine Prod.ext (by rfl) ?_
      change φ.toFun (p.val, -(1-(1:ℝ))*(2*δ)) = p.val.2
      simpa only [sub_self,neg_zero,zero_mul] using φ.initial p.val.1 p.val.2
    }
  exact ⟨a,b,fun _ => rfl,fun _ => rfl,left,right,fun _ _ => rfl,fun _ _ => rfl⟩

end NearbyLagrangian.Tubes

end

end OAI
