import Mathlib
import OAI.Analysis.SymmetricDomains.AffineProductCoordinates
import OAI.Analysis.SymmetricDomains.LieBracketIndicatorConst

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

def rotationScalar (t : ℝ) : ℂ := Complex.exp ((t : ℂ)*Complex.I)
@[simp] theorem rotationScalar_zero : rotationScalar 0=1 := by simp [rotationScalar]
@[simp] theorem rotationScalar_add (s t : ℝ) : rotationScalar (s+t)=rotationScalar s*rotationScalar t := by
  simp [rotationScalar,add_mul,Complex.exp_add]
@[simp] theorem rotationScalar_mul_neg (t : ℝ) : rotationScalar t*rotationScalar (-t)=1 := by
  rw [←rotationScalar_add,add_neg_cancel,rotationScalar_zero]
@[simp] theorem rotationScalar_norm (t : ℝ) : ‖rotationScalar t‖=1 := Complex.norm_exp_ofReal_mul_I t

def tangentialRotation (r k : ℕ) (t : ℝ) :
    (Affine r × Affine k) ≃L[ℂ] (Affine r × Affine k) :=
  ContinuousLinearEquiv.equivOfInverse
    (((rotationScalar t) • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (((rotationScalar (-t)) • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (by intro p; ext i <;> simp [smul_smul,←rotationScalar_add])
    (by intro p; ext i <;> simp [smul_smul,←rotationScalar_add])

def flatTangentialRotation (r k : ℕ) (t : ℝ) : Affine (r+k) ≃L[ℂ] Affine (r+k) :=
  ((affineProductCoordinates r k).symm.trans (tangentialRotation r k t)).trans
    (affineProductCoordinates r k)

@[simp] theorem flatTangentialRotation_apply (r k : ℕ) (t : ℝ) (x : Affine (r+k)) :
    flatTangentialRotation r k t x=affineProductCoordinates r k
      (rotationScalar t • ((affineProductCoordinates r k).symm x).1,
        ((affineProductCoordinates r k).symm x).2) := rfl

def flatTangentialInfinitesimal (r k : ℕ) : Affine (r+k) →L[ℂ] Affine (r+k) :=
  (affineProductCoordinates r k).toContinuousLinearMap.comp
    (((Complex.I • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod 0).comp
      (affineProductCoordinates r k).symm.toContinuousLinearMap)

 theorem hasDerivAt_rotationScalar : HasDerivAt rotationScalar Complex.I 0 := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
  convert (h.mul_const Complex.I).cexp using 1 <;> first | rfl | simp

 theorem hasDerivAt_flatTangentialRotation (r k : ℕ) (x : Affine (r+k)) :
    HasDerivAt (fun t => flatTangentialRotation r k t x) (flatTangentialInfinitesimal r k x) 0 := by
  let e := affineProductCoordinates r k
  have hp := (hasDerivAt_rotationScalar.smul_const (e.symm x).1).prodMk
    (hasDerivAt_const (0 : ℝ) (e.symm x).2)
  have hh := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Affine r × Affine k)
    (E := Affine (r+k)) 0 (e.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt hp
  convert hh using 1 <;> rfl

 theorem flatTangentialRotation_mem {r k : ℕ} (D : Set (Affine r × Affine k))
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    (t : ℝ) (x : Affine (r+k)) :
    flatTangentialRotation r k t x∈(affineProductCoordinates r k) '' D ↔
      x∈(affineProductCoordinates r k) '' D := by
  let e := affineProductCoordinates r k
  have hi (y : Affine (r+k)) : y∈e '' D ↔ e.symm y∈D := by
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [e.symm_apply_apply] using hp
    · intro h; exact ⟨e.symm y,h,e.apply_symm_apply y⟩
  rw [hi,hi]
  change e.symm (e (rotationScalar t • (e.symm x).1,(e.symm x).2)) ∈ D ↔ _
  rw [e.symm_apply_apply]
  exact hr _ (rotationScalar_norm t) _

 theorem exists_actual_model_rotation {r k n : ℕ}
    (D : Set (Affine r × Affine k))
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U) :
    ∃ H : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm H.val=((affineProductCoordinates r k) '' D).indicator
        (flatTangentialInfinitesimal r k) := by
  apply exists_complete_linear_generator_in_model hU hc hbd Γ hhol e
    (flatTangentialRotation r k) (flatTangentialRotation_mem D hr)
  · intro x
    simp
  · intro s t x
    simp [mul_smul]
  · simp_rw [flatTangentialRotation_apply]
    apply (affineProductCoordinates r k).continuous.comp
    have hc : Continuous rotationScalar := by
      exact Complex.continuous_exp.comp ((Complex.continuous_ofReal).mul_const Complex.I)
    exact ((hc.comp continuous_fst).smul
      (continuous_fst.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd))).prodMk
      (continuous_snd.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd))
  · exact hasDerivAt_flatTangentialRotation r k

end Biholomorph
end Release061

open Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 omit [CompleteSpace E] in
 theorem hasFDerivAt_centeredLinear (A : E →L[ℂ] E) (p x : E) :
    HasFDerivAt (fun y => A (y-p)) A x := by
  convert A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p) using 1 <;> rfl

 omit [CompleteSpace E] in
 theorem lieBracket_centeredLinear_eq (A : E →L[ℂ] E) (p : E) (V : E → E) :
    VectorField.lieBracket ℂ (fun y => A (y-p)) V =
      fun x => (fderiv ℂ V x) (A (x-p))-A (V x) := by
  funext x
  rw [VectorField.lieBracket,(hasFDerivAt_centeredLinear A p x).fderiv]

 theorem fderiv_lieBracket_centeredLinear (A : E →L[ℂ] E) (p : E)
    {V : E → E} {x : E} (hV : AnalyticAt ℂ V x) :
    fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) x=
      (fderiv ℂ V x).comp A+(fderiv ℂ (fderiv ℂ V) x).flip (A (x-p))-
        A.comp (fderiv ℂ V x) := by
  rw [lieBracket_centeredLinear_eq]
  have hd := (hV.fderiv.differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_centeredLinear A p x)).sub
    (A.hasFDerivAt.comp x hV.differentiableAt.hasFDerivAt)
  exact hd.fderiv

 omit [CompleteSpace E] in
 theorem lieBracket_centeredLinear_zeroJet (A : E →L[ℂ] E) (p : E) (V : E → E) :
    VectorField.lieBracket ℂ (fun y => A (y-p)) V p= -A (V p) := by
  rw [lieBracket_centeredLinear_eq]
  simp

 theorem lieBracket_centeredLinear_firstJet (A : E →L[ℂ] E) (p : E)
    {V : E → E} (hV : AnalyticAt ℂ V p) :
    fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) p=
      (fderiv ℂ V p).comp A-A.comp (fderiv ℂ V p) := by
  rw [fderiv_lieBracket_centeredLinear A p hV]
  simp

 theorem lieBracket_centeredLinear_secondJet (A : E →L[ℂ] E) (p : E)
    {V : E → E} (hV : AnalyticAt ℂ V p) (u v : E) :
    (fderiv ℂ (fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V)) p) u v=
      (fderiv ℂ (fderiv ℂ V) p) u (A v)+
      (fderiv ℂ (fderiv ℂ V) p) v (A u)-A ((fderiv ℂ (fderiv ℂ V) p) u v) := by
  let R : E → E →L[ℂ] E →L[ℂ] E := fun x => (fderiv ℂ (fderiv ℂ V) x).flip
  have hR : DifferentiableAt ℂ R p := by
    have hL : Differentiable ℂ (fun B : E →L[ℂ] E →L[ℂ] E => B.flip) := by
      exact LinearIsometryEquiv.differentiable (𝕜 := ℂ) (E := E →L[ℂ] E →L[ℂ] E)
        (F := E →L[ℂ] E →L[ℂ] E) (ContinuousLinearMap.flipₗᵢ ℂ E E E)
    exact DifferentiableAt.comp (𝕜 := ℂ) (F := E →L[ℂ] E →L[ℂ] E)
      (G := E →L[ℂ] E →L[ℂ] E) p (hL _) hV.fderiv.fderiv.differentiableAt
  have he : fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) =ᶠ[𝓝 p]
      fun x => (fderiv ℂ V x).comp A+R x (A (x-p))-A.comp (fderiv ℂ V x) := by
    filter_upwards [hV.eventually_analyticAt] with x hx
    exact fderiv_lieBracket_centeredLinear A p hx
  rw [he.fderiv_eq]
  have h1 := hV.fderiv.differentiableAt.hasFDerivAt.clm_comp (hasFDerivAt_const A p)
  have h2 := hR.hasFDerivAt.clm_apply (hasFDerivAt_centeredLinear A p p)
  have h3 := (hasFDerivAt_const A p).clm_comp hV.fderiv.differentiableAt.hasFDerivAt
  have hd := (h1.add h2).sub h3
  change (fderiv ℂ (((fun x => (fderiv ℂ V x).comp A)+fun x => R x (A (x-p)))-
    fun x => A.comp (fderiv ℂ V x)) p) u v=_
  rw [hd.fderiv]
  simp only [R, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  simp only [sub_self, map_zero, zero_apply, zero_add, add_zero]
end

open Filter Topology

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

def ZeroSecondJet (f : E → F) (p : E) : Prop :=
  f p=0 ∧ fderiv ℂ f p=0 ∧ fderiv ℂ (fderiv ℂ f) p=0

omit [CompleteSpace E] in
theorem ZeroSecondJet.comp {f : F → G} {g : E → F} {p : E}
    (hf : AnalyticAt ℂ f (g p)) (hg : AnalyticAt ℂ g p)
    (hz : ZeroSecondJet f (g p)) : ZeroSecondJet (f ∘ g) p := by
  obtain ⟨hz0,hz1,hz2⟩ := hz
  refine ⟨hz0,?_,?_⟩
  · rw [fderiv_comp p hf.differentiableAt hg.differentiableAt,hz1,ContinuousLinearMap.zero_comp]
  · have he : fderiv ℂ (f ∘ g) =ᶠ[𝓝 p]
        fun x => (fderiv ℂ f (g x)).comp (fderiv ℂ g x) := by
      filter_upwards [hg.eventually_analyticAt,
        hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt] with x hx hx'
      exact fderiv_comp x hx'.differentiableAt hx.differentiableAt
    rw [he.fderiv_eq]
    have hd := (hf.fderiv.differentiableAt.hasFDerivAt.comp p hg.differentiableAt.hasFDerivAt).clm_comp
      hg.fderiv.differentiableAt.hasFDerivAt
    simp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp [hz1,hz2]

omit [CompleteSpace E] in
theorem ZeroSecondJet.clm_apply {H : E → F →L[ℂ] G} {Z : E → F} {p : E}
    (hH : AnalyticAt ℂ H p) (hZ : AnalyticAt ℂ Z p)
    (hz : ZeroSecondJet Z p) : ZeroSecondJet (fun x => H x (Z x)) p := by
  obtain ⟨hz0,hz1,hz2⟩ := hz
  refine ⟨by simp [hz0],?_,?_⟩
  · rw [fderiv_clm_apply hH.differentiableAt hZ.differentiableAt]
    simp [hz0,hz1]
  · let R : E → F →L[ℂ] E →L[ℂ] G := fun x => (fderiv ℂ H x).flip
    let L : (E →L[ℂ] F →L[ℂ] G) →L[ℂ] (F →L[ℂ] E →L[ℂ] G) :=
      (ContinuousLinearMap.flipₗᵢ ℂ E F G).toContinuousLinearEquiv.toContinuousLinearMap
    have hR : DifferentiableAt ℂ R p := by
      change DifferentiableAt ℂ (L ∘ fderiv ℂ H) p
      have hL : Differentiable ℂ (fun B : E →L[ℂ] F →L[ℂ] G => B.flip) := by
        exact LinearIsometryEquiv.differentiable (𝕜 := ℂ) (E := E →L[ℂ] F →L[ℂ] G)
          (F := F →L[ℂ] E →L[ℂ] G) (ContinuousLinearMap.flipₗᵢ ℂ E F G)
      exact DifferentiableAt.comp (𝕜 := ℂ) (F := E →L[ℂ] F →L[ℂ] G)
        (G := F →L[ℂ] E →L[ℂ] G) p (hL _) hH.fderiv.differentiableAt
    have he : fderiv ℂ (fun x => H x (Z x)) =ᶠ[𝓝 p]
        fun x => (H x).comp (fderiv ℂ Z x)+R x (Z x) := by
      filter_upwards [hH.eventually_analyticAt,hZ.eventually_analyticAt] with x hx hx'
      exact fderiv_clm_apply hx.differentiableAt hx'.differentiableAt
    rw [he.fderiv_eq]
    have ha := hH.differentiableAt.hasFDerivAt.clm_comp hZ.fderiv.differentiableAt.hasFDerivAt
    have hb := hR.hasFDerivAt.clm_apply hZ.differentiableAt.hasFDerivAt
    change fderiv ℂ ((fun x => (H x).comp (fderiv ℂ Z x)) + fun x => R x (Z x)) p=0
    rw [(ha.add hb).fderiv]
    simp [hz0,hz1,hz2]

 omit [CompleteSpace E] [CompleteSpace F] in
 theorem ZeroSecondJet.congr {f g : E → F} {p : E}
    (h : f =ᶠ[𝓝 p] g) (hf : ZeroSecondJet f p) : ZeroSecondJet g p := by
  simpa only [ZeroSecondJet,←h.eq_of_nhds,←h.fderiv_eq,←h.fderiv.fderiv_eq] using hf
end

open Filter Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem fderiv_fderiv_add_of_analytic {V W : E → E} {p : E}
    (hV : AnalyticAt ℂ V p) (hW : AnalyticAt ℂ W p) :
    fderiv ℂ (fderiv ℂ (V+W)) p=fderiv ℂ (fderiv ℂ V) p+fderiv ℂ (fderiv ℂ W) p := by
  have he : fderiv ℂ (V+W) =ᶠ[𝓝 p] fun x => fderiv ℂ V x+fderiv ℂ W x := by
    filter_upwards [hV.eventually_analyticAt,hW.eventually_analyticAt] with x hx hy
    exact fderiv_add hx.differentiableAt hy.differentiableAt
  rw [he.fderiv_eq]
  exact fderiv_add hV.fderiv.differentiableAt hW.fderiv.differentiableAt

 theorem fderiv_fderiv_smul_of_analytic {V : E → E} {p : E}
    (hV : AnalyticAt ℂ V p) (c : ℂ) :
    fderiv ℂ (fderiv ℂ (c • V)) p=c • fderiv ℂ (fderiv ℂ V) p := by
  have he : fderiv ℂ (c • V) =ᶠ[𝓝 p] fun x => c • fderiv ℂ V x := by
    filter_upwards [hV.eventually_analyticAt] with x hx
    exact fderiv_const_smul hx.differentiableAt c
  rw [he.fderiv_eq]
  exact fderiv_const_smul hV.fderiv.differentiableAt c

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)

def fieldFirstJet : V →ₗ[ℂ] E →L[ℂ] E where
  toFun X := fderiv ℂ (F X) p
  map_add' X Y := by
    rw [map_add]
    exact fderiv_add (hF X).differentiableAt (hF Y).differentiableAt
  map_smul' c X := by
    rw [map_smul]
    exact fderiv_const_smul (hF X).differentiableAt c

def fieldSecondJet : V →ₗ[ℂ] E →L[ℂ] E →L[ℂ] E where
  toFun X := fderiv ℂ (fderiv ℂ (F X)) p
  map_add' X Y := by
    rw [map_add]
    exact fderiv_fderiv_add_of_analytic (hF X) (hF Y)
  map_smul' c X := by
    rw [map_smul]
    exact fderiv_fderiv_smul_of_analytic (hF X) c

end

open Polynomial

end

end OAI
