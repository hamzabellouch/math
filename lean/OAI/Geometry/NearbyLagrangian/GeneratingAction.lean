import Mathlib
import OAI.Geometry.NearbyLagrangian.NearIdentity

namespace OAI

/-! Liouville action identities and compact mixed generating functions. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def euclideanLiouville (z : E × E) : E × E →L[ℝ] ℝ :=
  (innerSL ℝ z.2).comp (fst ℝ E E)

lemma euclideanLiouville_apply (z v : E × E) :
    euclideanLiouville z v = inner ℝ z.2 v.1 := rfl

def mixedSigma (A : E × E → ℝ) (j : E × E → E × E) (y : E × E) : ℝ :=
  A (j y) + inner ℝ ((j y).1 - y.1) y.2

omit [InnerProductSpace ℝ E] in
lemma mixed_inverse_snd {ψ : E × E → E × E} (e : (E × E) ≃ₜ (E × E))
    (he : ∀ z, e z = mixedMap ψ z) (y : E × E) : (e.symm y).2 = y.2 := by
  have h := congrArg Prod.snd (e.apply_symm_apply y)
  simpa only [he, mixedMap] using h

omit [InnerProductSpace ℝ E] in
lemma mixed_inverse_fst {ψ : E × E → E × E} (e : (E × E) ≃ₜ (E × E))
    (he : ∀ z, e z = mixedMap ψ z) (y : E × E) : (ψ (e.symm y)).1 = y.1 := by
  have h := congrArg Prod.fst (e.apply_symm_apply y)
  simpa only [he, mixedMap] using h

lemma contDiff_mixedSigma {A : E × E → ℝ} {j : E × E → E × E}
    (hA : ContDiff ℝ ∞ A) (hj : ContDiff ℝ ∞ j) : ContDiff ℝ ∞ (mixedSigma A j) :=
  (hA.comp hj).add ((hj.fst.sub contDiff_fst).inner ℝ contDiff_snd)

theorem hasFDerivAt_mixedSigma {ψ : E × E → E × E} {A : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    (hψ : Differentiable ℝ ψ) (hj : Differentiable ℝ e.symm)
    (hA : ∀ z, HasFDerivAt A
      ((euclideanLiouville (ψ z)).comp (fderiv ℝ ψ z) - euclideanLiouville z) z)
    (y : E × E) : HasFDerivAt (mixedSigma A e.symm)
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y := by
  have hdj := (hj y).hasFDerivAt
  have hdx := ((hψ (e.symm y)).hasFDerivAt.comp y hdj).fst
  have hxfun : (fun t => (ψ (e.symm t)).1) = Prod.fst :=
    funext (mixed_inverse_fst e he)
  simp only [Function.comp_apply] at hdx
  rw [hxfun] at hdx
  have hxlin := hdx.unique (hasFDerivAt_fst (𝕜 := ℝ) (p := y))
  have hcalc := ((hA (e.symm y)).comp y hdj).add
    ((hdj.fst.sub hasFDerivAt_fst).inner ℝ hasFDerivAt_snd)
  convert! hcalc using 1
  apply ContinuousLinearMap.ext
  intro v
  have hx : (fderiv ℝ ψ (e.symm y) (fderiv ℝ e.symm y v)).1 = v.1 := by
    exact congrArg (fun L : E × E →L[ℝ] E => L v) hxlin
  simp only [Pi.sub_apply, add_apply, sub_apply, comp_apply, prod_apply, coe_fst', coe_snd',
    euclideanLiouville_apply, innerSL_apply_apply, fderivInnerCLM_apply, inner_sub_left]
  rw [hx, mixed_inverse_snd e he]
  simp only [real_inner_comm]
  ring

theorem hasCompactSupport_mixedSigma {ψ : E × E → E × E} {A : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    {K : Set (E × E)} (hK : IsCompact K)
    (hψK : ∀ z ∉ K, ψ z = z) (hAK : ∀ z ∉ K, A z = 0) :
    HasCompactSupport (mixedSigma A e.symm) := by
  apply HasCompactSupport.intro (hK.image e.continuous)
  intro y hy
  have hjK : e.symm y ∉ K := by
    intro hk
    exact hy ⟨e.symm y,hk,e.apply_symm_apply y⟩
  have hjy : e.symm y = y := by
    have hh := e.apply_symm_apply y
    rw [he] at hh
    simpa only [mixedMap, hψK _ hjK, Prod.mk.eta] using hh
  unfold mixedSigma
  rw [hAK _ hjK, hjy]
  simp

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

section Differential
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma hasFDerivAt_fderiv_apply_const {f : V → W} (hf : ContDiff ℝ ∞ f)
    (x v : V) : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((fderiv ℝ (fderiv ℝ f) x).flip v) x := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  simpa only [comp_zero, zero_add] using hd.clm_apply (hasFDerivAt_const v x)

end Differential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def flowVelocity (φ : ℝ × (E × E) → E × E) (q : ℝ × (E × E)) : E × E :=
  fderiv ℝ φ q (1,0)

def actionIntegrand (φ : ℝ × (E × E) → E × E) (H : ℝ × (E × E) → ℝ)
    (q : ℝ × (E × E)) : ℝ :=
  inner ℝ (φ q).2 (flowVelocity φ q).1 - H (q.1,φ q)

lemma contDiff_actionIntegrand {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (actionIntegrand φ H) := by
  have hv : ContDiff ℝ ∞ (flowVelocity φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  exact (hφ.snd.inner ℝ hv.fst).sub (hH.comp (contDiff_fst.prodMk hφ))

theorem cartan_action_identity {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (q : ℝ × (E × E))
    (hHam : ∀ w : E × E,
      inner ℝ (flowVelocity φ q).2 w.1 - inner ℝ w.2 (flowVelocity φ q).1 =
        - fderiv ℝ H (q.1,φ q) (0,w))
    (v : E × E) :
    fderiv ℝ (fun r => inner ℝ (φ r).2 (fderiv ℝ φ r (0,v)).1) q (1,0) =
      fderiv ℝ (actionIntegrand φ H) q (0,v) := by
  have hdφ := (hφ.differentiable (by simp) q).hasFDerivAt
  have hdv := hasFDerivAt_fderiv_apply_const hφ q (0,v)
  have hdt := hasFDerivAt_fderiv_apply_const hφ q (1,0)
  have hdH := ((hH.differentiable (by simp) (q.1,φ q)).hasFDerivAt).comp q
    (hasFDerivAt_fst.prodMk hdφ)
  have hleft := (hdφ.snd.inner ℝ hdv.fst).fderiv
  have hright := ((hdφ.snd.inner ℝ hdt.fst).sub hdH).fderiv
  have hsym := ((hφ.contDiffAt (x := q)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top))
    (1,0) (0,v)
  have hh := hHam (fderiv ℝ φ q (0,v))
  rw [hleft]
  change _ = fderiv ℝ
    ((fun r => inner ℝ (φ r).2 (fderiv ℝ φ r (1,0)).1) -
      H ∘ (fun r => (r.1,φ r))) q (0,v)
  rw [hright]
  simp only [comp_apply, sub_apply, prod_apply, coe_fst', coe_snd',
    fderivInnerCLM_apply, flip_apply]
  rw [hsym]
  dsimp [flowVelocity] at hh
  linarith

theorem hasDerivAt_pullbackLiouvilleEval {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (z v : E × E)
    (hHam : ∀ w : E × E,
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w)) :
    HasDerivAt (fun s => inner ℝ (φ (s,z)).2 (fderiv ℝ φ (s,z) (0,v)).1)
      (fderiv ℝ (actionIntegrand φ H) (t,z) (0,v)) t := by
  have hsm : ContDiff ℝ ∞ (fun q => inner ℝ (φ q).2
      (fderiv ℝ φ q (0,v)).1) :=
    hφ.snd.inner ℝ ((hφ.fderiv_right (by simp)).clm_apply contDiff_const).fst
  have hd := ((hsm.differentiable (by simp) (t,z)).hasFDerivAt.comp t
    (hasFDerivAt_prodMk_left t z)).hasDerivAt
  convert! hd using 1
  simp only [comp_apply, inl_apply,
    cartan_action_identity hφ hH (t,z) hHam v]

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Interval

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem hasFDerivAt_intervalIntegral_contDiff {F : ℝ × V → W}
    (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : V) :
    HasFDerivAt (fun y => ∫ t in a..b, F (t,y))
      (∫ t in a..b, (fderiv ℝ F (t,x)).comp (inr ℝ ℝ V)) x := by
  obtain ⟨hd,hc⟩ := contDiff_one_iff_fderiv.mp hF
  have hc' : Continuous (fun q : ℝ × V =>
      (fderiv ℝ F q).comp (inr ℝ ℝ V)) := hc.clm_comp continuous_const
  have hcompact : IsCompact (uIcc a b ×ˢ Metric.closedBall x 1) :=
    isCompact_uIcc.prod (isCompact_closedBall x 1)
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hc'.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (t,y))
    (F' := fun y t => (fderiv ℝ F (t,y)).comp (inr ℝ ℝ V))
    (bound := fun _ => C) (s := Metric.ball x 1) (Metric.ball_mem_nhds x zero_lt_one)
  · exact Filter.Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  · exact (hc'.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro y hy
    exact hC (t,y) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hy⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t y _ =>
      (hd (t,y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set MeasureTheory
open scoped ContDiff InnerProductSpace Interval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def flowLiouville (φ : ℝ × (E × E) → E × E) (q : ℝ × (E × E)) : (E × E) →L[ℝ] ℝ :=
  (euclideanLiouville (φ q)).comp ((fderiv ℝ φ q).comp (inr ℝ ℝ (E × E)))

lemma flowLiouville_apply (φ : ℝ × (E × E) → E × E) (q : ℝ × (E × E)) (v : E × E) :
    flowLiouville φ q v = inner ℝ (φ q).2 (fderiv ℝ φ q (0,v)).1 := rfl

lemma contDiff_flowLiouville {φ : ℝ × (E × E) → E × E} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (flowLiouville φ) := by
  exact (((innerSL ℝ).contDiff.comp hφ.snd).clm_comp contDiff_const).clm_comp
    ((hφ.fderiv_right (by simp)).clm_comp contDiff_const)

def hamiltonianAction (φ : ℝ × (E × E) → E × E) (H : ℝ × (E × E) → ℝ)
    (a b : ℝ) (z : E × E) : ℝ := ∫ t in a..b, actionIntegrand φ H (t,z)

variable [ProperSpace E]

theorem hasFDerivAt_hamiltonianAction {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hHam : ∀ t z (w : E × E),
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w))
    (a b : ℝ) (z : E × E) :
    HasFDerivAt (hamiltonianAction φ H a b)
      (flowLiouville φ (b,z)-flowLiouville φ (a,z)) z := by
  have hL := contDiff_actionIntegrand hφ hH
  have hd := hasFDerivAt_intervalIntegral_contDiff
    (hL.of_le (show (1 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) a b z
  have hc : Continuous (fun t =>
      (fderiv ℝ (actionIntegrand φ H) (t,z)).comp (inr ℝ ℝ (E × E))) :=
    ((hL.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_id.prodMk continuous_const)).clm_comp continuous_const
  have heq : (∫ t in a..b,
        (fderiv ℝ (actionIntegrand φ H) (t,z)).comp (inr ℝ ℝ (E × E))) =
      flowLiouville φ (b,z)-flowLiouville φ (a,z) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable a b)]
    simp only [comp_apply, inr_apply, sub_apply, flowLiouville_apply]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hasDerivAt_pullbackLiouvilleEval hφ hH t z v (hHam t z)
    · exact (hc.clm_apply continuous_const).intervalIntegrable a b
  rw [heq] at hd
  exact hd

theorem contDiff_hamiltonianAction {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hHam : ∀ t z (w : E × E),
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w)) (a b : ℝ) :
    ContDiff ℝ ∞ (hamiltonianAction φ H a b) := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨fun z => (hasFDerivAt_hamiltonianAction hφ hH hHam a b z).differentiableAt,?_⟩
  have hdf : fderiv ℝ (hamiltonianAction φ H a b) =
      fun z => flowLiouville φ (b,z)-flowLiouville φ (a,z) :=
    funext fun z => (hasFDerivAt_hamiltonianAction hφ hH hHam a b z).fderiv
  rw [hdf]
  exact ((contDiff_flowLiouville hφ).comp (contDiff_const.prodMk contDiff_id)).sub
    ((contDiff_flowLiouville hφ).comp (contDiff_const.prodMk contDiff_id))

omit [ProperSpace E] in
lemma flowVelocity_eq_zero_of_stationary {φ : ℝ × (E × E) → E × E}
    (hφ : ContDiff ℝ ∞ φ) (z : E × E) (hst : ∀ t, φ (t,z) = z) (t : ℝ) :
    flowVelocity φ (t,z) = 0 := by
  have hd := ((hφ.differentiable (by simp) (t,z)).hasFDerivAt.comp t
    (hasFDerivAt_prodMk_left t z)).hasDerivAt
  have hfun : (fun s => φ (s,z)) = fun _ => z := funext hst
  change HasDerivAt (fun s => φ (s,z)) (flowVelocity φ (t,z)) t at hd
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const t z)

omit [ProperSpace E] in

theorem hasCompactSupport_hamiltonianAction {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set (E × E)} (hK : IsCompact K)
    (hst : ∀ z ∉ K, ∀ t, φ (t,z) = z)
    (hH : ∀ z ∉ K, ∀ t, H (t,z) = 0) (a b : ℝ) :
    HasCompactSupport (hamiltonianAction φ H a b) := by
  apply HasCompactSupport.intro hK
  intro z hz
  have hzero : ∀ t, actionIntegrand φ H (t,z) = 0 := by
    intro t
    simp only [actionIntegrand, flowVelocity_eq_zero_of_stationary hφ z (hst z hz) t,
      Prod.fst_zero, inner_zero_right, hst z hz t, hH z hz t, sub_zero]
  simp only [hamiltonianAction, hzero, intervalIntegral.integral_zero]

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma flowLiouville_slice {φ : ℝ × (E × E) → E × E}
    (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (z : E × E) :
    flowLiouville φ (t,z) = (euclideanLiouville (φ (t,z))).comp
      (fderiv ℝ (fun x => φ (t,x)) z) := by
  have hd := (hφ.differentiable (by simp) (t,z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right t z)
  change HasFDerivAt (fun x => φ (t,x)) _ z at hd
  rw [hd.fderiv]
  rfl

lemma flowLiouville_initial {φ : ℝ × (E × E) → E × E}
    (hφ : ContDiff ℝ ∞ φ) (a : ℝ) (hi : ∀ z, φ (a,z) = z) (z : E × E) :
    flowLiouville φ (a,z) = euclideanLiouville z := by
  rw [flowLiouville_slice hφ, hi]
  have he : (fun x => φ (a,x)) = id := funext hi
  rw [he, fderiv_id, comp_id]

variable [ProperSpace E]

theorem hasFDerivAt_hamiltonianAction_initial {φ : ℝ × (E × E) → E × E}
    {H : ℝ × (E × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hHam : ∀ t z (w : E × E),
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w))
    (a b : ℝ) (hi : ∀ z, φ (a,z) = z) (z : E × E) :
    HasFDerivAt (hamiltonianAction φ H a b)
      ((euclideanLiouville (φ (b,z))).comp (fderiv ℝ (fun x => φ (b,x)) z) -
        euclideanLiouville z) z := by
  simpa only [flowLiouville_slice hφ b z, flowLiouville_initial hφ a hi z]
    using hasFDerivAt_hamiltonianAction hφ hH hHam a b z

theorem exists_compact_mixed_generating_function
    {φ : ℝ × (E × E) → E × E} {H : ℝ × (E × E) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hHam : ∀ t z (w : E × E),
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w))
    (a b : ℝ) (hi : ∀ z, φ (a,z) = z)
    {K : Set (E × E)} (hK : IsCompact K)
    (hst : ∀ z ∉ K, ∀ t, φ (t,z) = z)
    (hHK : ∀ z ∉ K, ∀ t, H (t,z) = 0)
    (c : ℝ≥0) (hc : c < 1)
    (hsmall : ∀ z, ‖fderiv ℝ (fun x => φ (b,x)) z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c) :
    ∃ (e : (E × E) ≃ₜ (E × E)) (σ : E × E → ℝ),
      (∀ z, e z = mixedMap (fun x => φ (b,x)) z) ∧
      ContDiff ℝ ∞ e.symm ∧ ContDiff ℝ ∞ σ ∧ HasCompactSupport σ ∧
      ∀ y, HasFDerivAt σ
        ((innerSL ℝ ((φ (b,e.symm y)).2-y.2)).comp (fst ℝ E E) +
          (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y := by
  let ψ : E × E → E × E := fun x => φ (b,x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.prodMk contDiff_id)
  let e := mixedHomeomorph ψ hψ c hc hsmall
  have he : ∀ z, e z = mixedMap ψ z := fun z => mixedHomeomorph_apply ψ hψ c hc hsmall z
  have hj : ContDiff ℝ ∞ e.symm := contDiff_mixedHomeomorph_symm ψ hψ c hc hsmall
  let A := hamiltonianAction φ H a b
  have hA : ContDiff ℝ ∞ A := contDiff_hamiltonianAction hφ hH hHam a b
  refine ⟨e, mixedSigma A e.symm, he, hj, contDiff_mixedSigma hA hj, ?_, ?_⟩
  · apply hasCompactSupport_mixedSigma e he hK (fun z hz => hst z hz b)
    intro z hz
    have hzero : ∀ t, actionIntegrand φ H (t,z) = 0 := by
      intro t
      simp only [actionIntegrand, flowVelocity_eq_zero_of_stationary hφ z (hst z hz) t,
        Prod.fst_zero, inner_zero_right, hst z hz t, hHK z hz t, sub_zero]
    simp only [A, hamiltonianAction, hzero, intervalIntegral.integral_zero]
  · intro y
    exact hasFDerivAt_mixedSigma e he (hψ.differentiable (by simp))
      (hj.differentiable (by simp)) (hasFDerivAt_hamiltonianAction_initial hφ hH hHam a b hi) y

end NearbyLagrangian.Transport

end

end OAI
