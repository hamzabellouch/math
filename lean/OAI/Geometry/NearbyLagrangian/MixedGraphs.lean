import Mathlib
import OAI.Geometry.NearbyLagrangian.PhaseRegularity
import OAI.Geometry.NearbyLagrangian.GeneratingAction

namespace OAI

/-! Mixed graph equations, displacement bounds and twist regularity. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mixed_partial_derivatives {ψ : E × E → E × E} {σ : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E))
    (hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y)
    (X p : E) :
    fderiv ℝ (fun q => σ (X,q)) p = innerSL ℝ ((e.symm (X,p)).1-X) ∧
    fderiv ℝ (fun Y => σ (Y,p)) X = innerSL ℝ ((ψ (e.symm (X,p))).2-p) := by
  constructor
  · have hp := ((hd (X,p)).comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) X p)).fderiv
    change fderiv ℝ (fun q => σ (X,q)) p = _ at hp
    rw [hp]
    apply ContinuousLinearMap.ext
    intro v
    simp only [comp_apply, add_apply, coe_fst', coe_snd', inr_apply, map_zero, zero_add]
  · have hX := ((hd (X,p)).comp X (hasFDerivAt_prodMk_left (𝕜 := ℝ) X p)).fderiv
    change fderiv ℝ (fun Y => σ (Y,p)) X = _ at hX
    rw [hX]
    apply ContinuousLinearMap.ext
    intro v
    simp only [comp_apply, add_apply, coe_fst', coe_snd', inl_apply, map_zero, add_zero]

theorem mixed_graph_iff {ψ : E × E → E × E} {σ : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    (hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y)
    (x p X : E) :
    (ψ (x,p)).1 = X ↔ fderiv ℝ (fun q => σ (X,q)) p = innerSL ℝ (x-X) := by
  rw [(mixed_partial_derivatives e hd X p).1]
  have heinj : Function.Injective (innerSL ℝ : E → E →L[ℝ] ℝ) := by
    intro u v h
    have hh : ‖u-v‖ = 0 := by
      rw [← innerSL_apply_norm ℝ (u-v), map_sub, h, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hh)
  constructor
  · intro hx
    have hy : e (x,p) = (X,p) := by simp only [he, mixedMap, hx]
    have hj : e.symm (X,p) = (x,p) := by rw [← hy, e.symm_apply_apply]
    rw [hj]
  · intro hx
    have hfst : (e.symm (X,p)).1 = x := by
      have hh := congrArg (fun z : E => z+X) (heinj hx)
      simpa only [sub_add_cancel] using hh
    have hj : e.symm (X,p) = (x,p) := Prod.ext hfst (mixed_inverse_snd e he (X,p))
    have hh := e.apply_symm_apply (X,p)
    rw [hj, he] at hh
    exact congrArg Prod.fst hh

lemma mixed_graph_output {ψ : E × E → E × E} {σ : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    (hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y)
    (x p : E) :
    innerSL ℝ (ψ (x,p)).2 = innerSL ℝ p +
      fderiv ℝ (fun X => σ (X,p)) (ψ (x,p)).1 := by
  rw [(mixed_partial_derivatives e hd _ p).2]
  have hy : e (x,p) = ((ψ (x,p)).1,p) := he (x,p)
  rw [← hy, e.symm_apply_apply, map_sub]
  abel

theorem mixed_momentum_derivative_bound {ψ : E × E → E × E} {σ : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    (hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y)
    {δ : ℝ} (hb : ∀ z, ‖ψ z-z‖ < δ) (X p : E) :
    ‖fderiv ℝ (fun q => σ (X,q)) p‖ < δ := by
  rw [(mixed_partial_derivatives e hd X p).1, innerSL_apply_norm]
  have hh : ‖(e.symm (X,p)).1-X‖ ≤ ‖ψ (e.symm (X,p))-e.symm (X,p)‖ := by
    have hf : (ψ (e.symm (X,p))).1 = X := mixed_inverse_fst e he (X,p)
    have hn := _root_.norm_fst_le (ψ (e.symm (X,p))-e.symm (X,p))
    change ‖(ψ (e.symm (X,p))).1 - (e.symm (X,p)).1‖ ≤ _ at hn
    rw [hf] at hn
    simpa only [norm_sub_rev] using hn
  exact hh.trans_lt (hb _)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in

lemma mapsTo_compact_support {ψ : E × E → E × E} (hψ : Function.Injective ψ)
    {K : Set (E × E)} (hst : ∀ z ∉ K, ψ z = z) : MapsTo ψ K K := by
  intro z hz
  by_contra hn
  have hh : ψ (ψ z) = ψ z := hst (ψ z) hn
  have he : ψ z = z := hψ hh
  apply hn
  rwa [he]

omit [InnerProductSpace ℝ E] in

lemma mixed_image_projection {ψ : E × E → E × E} (hψ : Function.Injective ψ)
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    {K : Set (E × E)} (hst : ∀ z ∉ K, ψ z = z) (y : E × E)
    (hy : y ∈ e '' K) : y.1 ∈ Prod.fst '' K := by
  obtain ⟨z,hz,rfl⟩ := hy
  refine ⟨ψ z, mapsTo_compact_support hψ hst hz, ?_⟩
  rw [he]
  rfl

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open Set ContinuousLinearMap
open scoped ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mixedSigma_zero_off_projection {ψ : E × E → E × E} {A : E × E → ℝ}
    (hψ : Function.Injective ψ) (e : (E × E) ≃ₜ (E × E))
    (he : ∀ z, e z = mixedMap ψ z) {K : Set (E × E)}
    (hst : ∀ z ∉ K, ψ z = z) (hA : ∀ z ∉ K, A z = 0)
    (X : E) (hX : X ∉ Prod.fst '' K) (p : E) : mixedSigma A e.symm (X,p) = 0 := by
  have hjK : e.symm (X,p) ∉ K := by
    intro hk
    apply hX
    exact mixed_image_projection hψ e he hst (X,p)
      ⟨e.symm (X,p),hk,e.apply_symm_apply (X,p)⟩
  have hjy : e.symm (X,p) = (X,p) := by
    have hh := e.apply_symm_apply (X,p)
    rw [he] at hh
    simpa only [mixedMap, hst _ hjK, Prod.mk.eta] using hh
  unfold mixedSigma
  rw [hA _ hjK, hjy]
  simp

variable [CompleteSpace E] [ProperSpace E]

theorem exists_controlled_mixed_generator
    (φ : ℝ × (E × E) → E × E) (H : ℝ × (E × E) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hHam : ∀ t z (w : E × E),
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w))
    (a b : ℝ) (hi : ∀ z, φ (a,z) = z)
    (ψ : (E × E) ≃ₜ (E × E)) (hψ : ∀ z, ψ z = φ (b,z))
    {K : Set (E × E)} (hK : IsCompact K)
    (hst : ∀ z ∉ K, ∀ t, φ (t,z) = z)
    (hHK : ∀ z ∉ K, ∀ t, H (t,z) = 0)
    (c : ℝ≥0) (hc : c < 1)
    (hsmall : ∀ z, ‖fderiv ℝ (fun x => φ (b,x)) z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c)
    {δ : ℝ} (hδ : ∀ z, ‖ψ z-z‖ < δ) :
    ∃ (e : (E × E) ≃ₜ (E × E)) (σ : E × E → ℝ),
      (∀ z, e z = mixedMap ψ z) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ ContDiff ℝ ∞ σ ∧ HasCompactSupport σ ∧
      (∀ y, HasFDerivAt σ
        ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
          (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y) ∧
      (∀ X ∉ Prod.fst '' K, ∀ p, σ (X,p) = 0) ∧
      (∀ X p, ‖fderiv ℝ (fun p => σ (X,p)) p‖ < δ) ∧
      (∀ x p X, (ψ (x,p)).1 = X ↔ fderiv ℝ (fun p => σ (X,p)) p = innerSL ℝ (x-X)) ∧
      ∀ x p, innerSL ℝ (ψ (x,p)).2 = innerSL ℝ p +
        fderiv ℝ (fun X => σ (X,p)) (ψ (x,p)).1 := by
  have heq : (fun x => φ (b,x)) = ψ := funext fun z => (hψ z).symm
  have hψsmooth : ContDiff ℝ ∞ (ψ : E × E → E × E) := by
    rw [← heq]
    exact hφ.comp (contDiff_const.prodMk contDiff_id)
  have hsmall' : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c := by
    simpa only [heq] using hsmall
  let e := mixedHomeomorph ψ hψsmooth c hc hsmall'
  have he : ∀ z, e z = mixedMap ψ z := fun z => mixedHomeomorph_apply ψ hψsmooth c hc hsmall' z
  have hj : ContDiff ℝ ∞ e.symm := contDiff_mixedHomeomorph_symm ψ hψsmooth c hc hsmall'
  have hec : ContDiff ℝ ∞ (e : E × E → E × E) := by
    change ContDiff ℝ ∞ (mixedMap ψ)
    exact hψsmooth.fst.prodMk contDiff_snd
  let A := hamiltonianAction φ H a b
  have hA : ContDiff ℝ ∞ A := contDiff_hamiltonianAction hφ hH hHam a b
  have hAK : ∀ z ∉ K, A z = 0 := by
    intro z hz
    have hzero : ∀ t, actionIntegrand φ H (t,z) = 0 := by
      intro t
      simp only [actionIntegrand, flowVelocity_eq_zero_of_stationary hφ z (hst z hz) t,
        Prod.fst_zero, inner_zero_right, hst z hz t, hHK z hz t, sub_zero]
    simp only [A, hamiltonianAction, hzero, intervalIntegral.integral_zero]
  have hψK : ∀ z ∉ K, ψ z = z := fun z hz => (hψ z).trans (hst z hz b)
  let σ := mixedSigma A e.symm
  have hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y := by
    intro y
    apply hasFDerivAt_mixedSigma e he (hψsmooth.differentiable (by simp))
      (hj.differentiable (by simp))
    intro z
    simpa only [← heq] using hasFDerivAt_hamiltonianAction_initial hφ hH hHam a b hi z
  exact ⟨e,σ,he,hec,hj,contDiff_mixedSigma hA hj,
    hasCompactSupport_mixedSigma e he hK hψK hAK,hd,
    mixedSigma_zero_off_projection ψ.injective e he hψK hAK,
    mixed_momentum_derivative_bound e he hd hδ,
    mixed_graph_iff e he hd,mixed_graph_output e he hd⟩

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mixedDisplacement_eq_inverse {ψ : E × E → E × E} {σ : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E))
    (hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y) (y : E × E) :
    mixedDisplacement σ y = (e.symm y).1-y.1 := by
  have hp : verticalDifferential σ y.1 y.2 = innerSL ℝ ((e.symm y).1-y.1) := by
    rw [verticalDifferential, Prod.mk.eta, (hd y).fderiv]
    ext v
    simp only [comp_apply, add_apply, coe_fst', coe_snd', inr_apply, map_zero, zero_add]
  unfold mixedDisplacement
  rw [hp]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

theorem mixed_twist_surjective {ψ : E × E → E × E} {σ : E × E → ℝ}
    (e : (E × E) ≃ₜ (E × E)) (he : ∀ z, e z = mixedMap ψ z)
    (hes : ContDiff ℝ ∞ (e : E × E → E × E)) (hjs : ContDiff ℝ ∞ e.symm)
    (hd : ∀ y, HasFDerivAt σ
      ((innerSL ℝ ((ψ (e.symm y)).2-y.2)).comp (fst ℝ E E) +
        (innerSL ℝ ((e.symm y).1-y.1)).comp (snd ℝ E E)) y) (y : E × E) :
    Function.Surjective (ContinuousLinearMap.id ℝ E +
      (fderiv ℝ (mixedDisplacement σ) y).comp (inl ℝ E E)) := by
  have hj := hjs.differentiable (by simp)
  have hef := hes.differentiable (by simp)
  have hm : mixedDisplacement σ = fun q => (e.symm q).1-q.1 :=
    funext (mixedDisplacement_eq_inverse e hd)
  have hdj : HasFDerivAt (mixedDisplacement σ)
      ((fst ℝ E E).comp (fderiv ℝ e.symm y) - fst ℝ E E) y := by
    rw [hm]
    exact (hj y).hasFDerivAt.fst.sub hasFDerivAt_fst
  have hcomp : (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) =
      ContinuousLinearMap.id ℝ (E × E) := by
    have hh := (hj (e (e.symm y))).hasFDerivAt.comp (e.symm y) (hef (e.symm y)).hasFDerivAt
    have hi : (fun z => e.symm (e z)) = id := funext e.symm_apply_apply
    simpa only [Function.comp_def, hi, e.apply_symm_apply, fderiv_id] using hh.fderiv.symm
  intro w
  let v := fderiv ℝ e (e.symm y) (w,0)
  have hv2 : v.2 = 0 := by
    have hh := (hef (e.symm y)).hasFDerivAt.snd.fderiv
    have hm : (fun z => (e z).2) = Prod.snd := by
      funext z
      rw [he]
      rfl
    have hrow' : (snd ℝ E E).comp (fderiv ℝ e (e.symm y)) = snd ℝ E E := by
      simpa only [hm, fderiv_snd] using hh.symm
    exact congrArg (fun L : E × E →L[ℝ] E => L (w,0)) hrow'
  refine ⟨v.1,?_⟩
  rw [hdj.fderiv]
  have hv : (v.1,(0:E)) = v := Prod.ext rfl hv2.symm
  have hh := congrArg (fun L : E × E →L[ℝ] E × E => (L (w,0)).1) hcomp
  change (fderiv ℝ e.symm y v).1 = w at hh
  simpa only [add_apply,id_apply,comp_apply,sub_apply,inl_apply,coe_fst',hv,
    add_sub_cancel] using hh

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport.StepData
open ContinuousLinearMap
open scoped ContDiff
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]
variable (S : StepData (E := E) (W := W))

theorem regular_at_newCritical_of_twist
    (old_regular : ∀ x ∈ S.U, ∀ w, verticalDifferential S.F x w = 0 →
      Function.Surjective (fderiv ℝ (fun v : E × W => verticalDifferential S.F v.1 v.2) (x,w)))
    (mixed_twist : ∀ X ∈ S.U, ∀ p, Function.Surjective (ContinuousLinearMap.id ℝ E +
      (fderiv ℝ (mixedDisplacement S.σ) (X,p)).comp (inl ℝ E E)))
    (q : S.NewCritical) :
    Function.Surjective (fderiv ℝ (fiberDifferential (totalPhase S.F S.σ S.κ)) q.val) := by
  let r := q.val
  have hU : r.1 ∈ S.U := q.property.1
  have hc : IsShiftedCritical S.F S.σ S.κ r.1 r.2.1 r.2.2.1 r.2.2.2 := q.property.2
  obtain ⟨hw,hz⟩ := S.new_critical_bounds hU hc
  have ho := (S.new_to_old hU hc).1
  have hshift := S.shift_mem r.1 hU r.2.1 r.2.2.1
  change Function.Surjective (fderiv ℝ (fiberDifferential (totalPhase S.F S.σ S.κ)) r)
  rcases S.cover r.1 hU with hζ | hσ
  · have hk : S.κ r.1 r.2.1 r.2.2.1 = 1 := by
      exact (S.cutoff_near_critical hw hz).self_of_nhds.trans hζ.self_of_nhds
    have hs : S.shiftedBase r.1 r.2.1 r.2.2.1 = r.1+r.2.2.1 := by
      simp only [shiftedBase,hk,one_smul]
    change S.shiftedBase r.1 r.2.1 r.2.2.1 ∈ S.U at hshift
    rw [hs] at ho hshift
    have hreg := regular_purePhase (S.smooth_F _ hshift r.2.1)
      (S.smooth_σ.contDiffAt (x := (r.1,r.2.2.2)))
      (old_regular _ hshift _ ho) (mixed_twist _ hU _)
    rw [(fiberDifferential_congr (S.phase_near_supported hw hz hζ)).fderiv_eq]
    exact hreg
  · have H := (shiftedCritical_iff_outside
      (S.diff_F hshift r.2.1) hσ.self_of_nhds (S.diff_κ_w _ _ _)
      (S.diff_κ_z _ _ _) (S.diff_phase hU _ _ _)).mp hc
    have hs : S.shiftedBase r.1 r.2.1 r.2.2.1 = r.1 := by
      simp only [shiftedBase,H.1,smul_zero,add_zero]
    rw [hs] at ho
    have hreg := regular_outsidePhase (S.smooth_F _ hU r.2.1)
      (S.smooth_ζ.contDiffAt (x := r.1)) H.1 (old_regular _ hU _ ho)
    rw [(fiberDifferential_congr (S.phase_near_outside hw hz hσ)).fderiv_eq]
    exact hreg

end NearbyLagrangian.Transport.StepData

end

end OAI
