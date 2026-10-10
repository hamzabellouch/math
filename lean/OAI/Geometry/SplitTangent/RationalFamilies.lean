import Mathlib
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.OpenManifold
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.RationalTrivialization
import OAI.Geometry.SplitTangent.BoxFirstTransport

namespace OAI

/-! Rational Families. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
abbrev Space (n : ℕ) := Fin n → ℂ

 
structure Patch (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  dim : ℕ
  domain : Set (Space dim)
  isOpen_domain : IsOpen domain
  preconnected_domain : IsPreconnected domain
  map : Space dim → E
  analytic : AnalyticOnNhd ℂ map domain

def Patch.image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (P : Patch E) : Set E :=
  P.map '' P.domain

 

theorem regular_zero_patchAlternative {d : ℕ} {f : Space d → ℂ} {x : Space d}
    {U : Set (Space d)} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : AnalyticAt ℂ f x) (hx : f x=0) (hd : fderiv ℂ f x ≠ 0) :
    ∃ P : Patch (Space d), P.dim < d ∧ P.image ⊆ U ∩ {y | f y=0} ∧
      ∃ V : Set (Space d), IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, f y=0 → y ∈ P.image := by
  classical
  let L := fderiv ℂ f x
  have hL : L.toLinearMap ≠ 0 := by
    intro hh
    apply hd
    ext v
    exact congrArg (fun q : Space d →ₗ[ℂ] ℂ => q v) hh
  have hr : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hL
  have hk := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented f L
    ((hf.contDiffAt (n := ω)).hasStrictFDerivAt (by simp)) hr hk
  let m := Module.finrank ℂ L.ker
  let e : Space m ≃L[ℂ] L.ker :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).symm
  have hm : m < d := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hL
    have hh' : m + 1 = d := by simpa only [Space,Module.finrank_fin_fun] using hh
    omega
  have hright : AnalyticAt ℂ φ.rightFun x := by
    exact ((Classical.choose hk).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ : AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    (φ.contDiffAt_implicitFunction hf.contDiffAt hright.contDiffAt (by simp)).analyticAt
  have hbase : φ.prodFun φ.pt = (0,0) := by
    ext <;> simp [φ,ImplicitFunctionData.prodFun,hx]
  have hval : φ.implicitFunction 0 0 = x := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ,hx] using hh
  let g : Space m → Space d := fun z => φ.implicitFunction 0 (e z)
  have hg : AnalyticAt ℂ g 0 := by
    have hh : AnalyticAt ℂ φ.implicitFunction.uncurry (0,e 0) := by
      simpa only [hbase,map_zero] using hφ
    exact AnalyticAt.comp (f := fun z : Space m => (0,e z)) (x := 0) hh
      (analyticAt_const.prod (e.analyticAt 0))
  have hg0 : g 0=x := by simpa [g] using hval
  have hfg : ∀ᶠ z in 𝓝 (0 : Space m), f (g z)=0 := by
    have ht : Tendsto (fun z : Space m => (0,e z)) (𝓝 0) (𝓝 (φ.prodFun φ.pt)) := by
      rw [hbase]
      simpa using (continuous_const.prodMk e.continuous).continuousAt.tendsto (x := 0)
    exact ht.eventually φ.leftFun_implicitFunction
  have hgU : ∀ᶠ z in 𝓝 (0 : Space m), g z∈U :=
    hg.continuousAt (hg0 ▸ hU.mem_nhds hxU)
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp
    (hg.eventually_analyticAt.and (hgU.and hfg))
  let W := Metric.ball (0 : Space m) r
  have hWo : IsOpen W := Metric.isOpen_ball
  have hW0 : (0 : Space m)∈W := Metric.mem_ball_self hr
  have hWh : ∀ z∈W, AnalyticAt ℂ g z ∧ g z∈U ∧ f (g z)=0 := hrW
  let P : Patch (Space d) := ⟨m,W,hWo,(convex_ball (0 : Space m) r).isPreconnected,
    g,fun z hz => (hWh z hz).1⟩
  refine ⟨P,hm,?_,?_⟩
  · rintro y ⟨z,hz,rfl⟩
    exact (hWh z hz).2
  · have hψ : ContinuousAt (fun y => e.symm (φ.rightFun y)) x :=
      e.symm.continuousAt.comp hright.continuousAt
    have hψ0 : e.symm (φ.rightFun x)=0 := by simp [φ]
    have hψW : ∀ᶠ y in 𝓝 x, e.symm (φ.rightFun y)∈W :=
      hψ (by simpa only [hψ0] using hWo.mem_nhds hW0)
    obtain ⟨V,hV,hVo,hVx⟩ := eventually_nhds_iff.mp
      (hψW.and φ.implicitFunction_apply_image)
    refine ⟨V,hVo,hVx,fun y hy hfy => ?_⟩
    refine ⟨e.symm (φ.rightFun y),(hV y hy).1,?_⟩
    change φ.implicitFunction 0 (e (e.symm (φ.rightFun y)))=y
    rw [e.apply_symm_apply]
    have hh := (hV y hy).2
    simpa only [show φ.leftFun y=f y from rfl,hfy] using hh

end AnalyticZeroCover

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
section

variable {R K F : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ R] [FiniteDimensional ℂ K] [FiniteDimensional ℂ F]

 

omit [FiniteDimensional ℂ F] in
lemma vertical_eq_zero_of_rank_le (A : R × K →L[ℂ] F) (p : F →L[ℂ] R)
    (hp : p.comp A = ContinuousLinearMap.fst ℂ R K)
    (hr : Module.finrank ℂ A.range ≤ Module.finrank ℂ R) (k : K) :
    A (0,k)=0 := by
  let q : A.range →ₗ[ℂ] R := p.toLinearMap.comp A.range.subtype
  have hq : Function.Surjective q := by
    intro r
    refine ⟨⟨A (r,0),⟨(r,0),rfl⟩⟩,?_⟩
    exact congrArg (fun B : R × K →L[ℂ] R => B (r,0)) hp
  have heq : Module.finrank ℂ A.range = Module.finrank ℂ R :=
    le_antisymm hr (LinearMap.finrank_le_finrank_of_surjective hq)
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hq
  have hh : q ⟨A (0,k),⟨(0,k),rfl⟩⟩ = q 0 := by
    simpa [q,ContinuousLinearMap.comp_apply] using congrArg (fun B : R × K →L[ℂ] R => B (0,k)) hp
  exact congrArg Subtype.val (hi hh)

 
omit [FiniteDimensional ℂ F] in
lemma finrank_range_comp_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ G]
    (a : E →L[ℂ] F) (b : G →L[ℂ] E) :
    Module.finrank ℂ (a.comp b).range ≤ Module.finrank ℂ a.range := by
  exact Submodule.finrank_mono (by
    rintro _ ⟨v,rfl⟩
    exact ⟨b v,rfl⟩)

 

lemma Patch.dimH_image_le (P : Patch F) :
    dimH P.image ≤ (2*P.dim : ℕ) := by
  have hh : dimH P.image ≤ dimH P.domain := by
    exact dimH_image_le_of_locally_lipschitzOn (fun x hx => by
      obtain ⟨C,s,hs,hC⟩ := (P.analytic x hx).contDiffAt (n := 1) |>.exists_lipschitzOnWith
      exact ⟨C,s,mem_nhdsWithin_of_mem_nhds hs,hC⟩)
  apply hh.trans
  apply (dimH_mono (subset_univ P.domain)).trans_eq
  rw [Real.dimH_univ_eq_finrank,finrank_real_of_complex,Module.finrank_fin_fun]

end

variable {E F R K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [FiniteDimensional ℂ R] [FiniteDimensional ℂ K]

 
omit [FiniteDimensional ℂ F] in
lemma constant_vertical {H : R × K → F} {U : Set R} {V : Set K}
    (hU : IsOpen U) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hH : AnalyticOnNhd ℂ H (U ×ˢ V)) (p : F →L[ℂ] R)
    (hp : ∀ z∈U ×ˢ V, p (H z)=z.1)
    (hr : ∀ z∈U ×ˢ V, Module.finrank ℂ (fderiv ℂ H z).range ≤ Module.finrank ℂ R)
    {r : R} (hrU : r∈U) {k l : K} (hk : k∈V) (hl : l∈V) :
    H (r,k)=H (r,l) := by
  have hd (v : K) (hv : v∈V) := (hH (r,v) ⟨hrU,hv⟩).differentiableAt
  have hcomp (v : K) (hv : v∈V) :
      HasFDerivAt (fun k => H (r,k))
        ((fderiv ℂ H (r,v)).comp (ContinuousLinearMap.inr ℂ R K)) v :=
    (hd v hv).hasFDerivAt.comp v
      ((hasFDerivAt_const r v).prodMk (hasFDerivAt_id v))
  have hz (v : K) (hv : v∈V) : fderiv ℂ (fun k => H (r,k)) v=0 := by
    rw [(hcomp v hv).fderiv]
    have he : (fun z => p (H z)) =ᶠ[𝓝 (r,v)] Prod.fst :=
      Filter.Eventually.mono ((hU.prod hV).mem_nhds (show (r,v)∈U ×ˢ V from ⟨hrU,hv⟩))
        (fun z hz => hp z hz)
    have heD : p.comp (fderiv ℂ H (r,v)) = ContinuousLinearMap.fst ℂ R K :=
      ((p.hasFDerivAt.comp (r,v) (hd v hv).hasFDerivAt).congr_of_eventuallyEq he.symm).unique
        hasFDerivAt_fst
    ext w
    exact vertical_eq_zero_of_rank_le _ p heD (hr (r,v) ⟨hrU,hv⟩) w
  exact hV.is_const_of_fderiv_eq_zero hVc
    (fun v hv => (hcomp v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => hz v hv) hk hl

 

theorem local_image_patchAlternative {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x∈U) (hf : AnalyticOnNhd ℂ f U)
    (p : F →L[ℂ] R) (hs : Function.Surjective (p.comp (fderiv ℂ f x)))
    (hr : ∀ y∈U, Module.finrank ℂ (fderiv ℂ f y).range ≤ Module.finrank ℂ R) :
    ∃ P : Patch F, P.dim=Module.finrank ℂ R ∧
      ∃ W : Set E, IsOpen W ∧ x∈W ∧ W⊆U ∧ f '' W ⊆ P.image := by
  classical
  let g : E → R := fun y => p (f y)
  let L := p.comp (fderiv ℂ f x)
  have hg : AnalyticAt ℂ g x := (p.analyticAt _).comp (hf x hx)
  have hgD : HasStrictFDerivAt g L x :=
    p.hasStrictFDerivAt.comp x (((hf x hx).contDiffAt (n := ω)).hasStrictFDerivAt (by simp))
  have hL : L.range=⊤ := LinearMap.range_eq_top.mpr hs
  have hK := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented g L hgD hL hK
  have hright : AnalyticAt ℂ φ.rightFun x :=
    ((Classical.choose hK).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ : AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    (φ.contDiffAt_implicitFunction hg.contDiffAt hright.contDiffAt (by simp)).analyticAt
  have hbase : φ.prodFun φ.pt=(g x,0) := by
    ext <;> simp [φ,ImplicitFunctionData.prodFun]
  have hval : φ.implicitFunction (g x) 0=x := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ] using hh
  have hφ' : AnalyticAt ℂ φ.implicitFunction.uncurry (g x,0) := hbase ▸ hφ
  have hφU : ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), φ.implicitFunction.uncurry z∈U :=
    hφ'.continuousAt (by simpa only [Function.uncurry_apply_pair,hval] using hU.mem_nhds hx)
  have hφp : ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), p (f (φ.implicitFunction.uncurry z))=z.1 := by
    change ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), φ.leftFun (φ.implicitFunction z.1 z.2)=z.1
    rw [← hbase]
    exact φ.leftFun_implicitFunction
  obtain ⟨ε,hε,hεprop⟩ := Metric.mem_nhds_iff.mp
    (hφ'.eventually_analyticAt.and (hφU.and hφp))
  let A := Metric.ball (g x) ε
  let B := Metric.ball (0 : L.ker) ε
  have hAB : A ×ˢ B = Metric.ball (g x,(0 : L.ker)) ε := by
    ext z
    simp only [A,B,mem_prod,Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  let H : R × L.ker → F := f ∘ φ.implicitFunction.uncurry
  have hprop (z : R × L.ker) (hz : z∈A ×ˢ B) :
      AnalyticAt ℂ φ.implicitFunction.uncurry z ∧
        φ.implicitFunction.uncurry z∈U ∧ p (H z)=z.1 := hεprop (hAB ▸ hz)
  have hH : AnalyticOnNhd ℂ H (A ×ˢ B) := fun z hz =>
    (hf _ (hprop z hz).2.1).comp (hprop z hz).1
  have hrH : ∀ z∈A ×ˢ B, Module.finrank ℂ (fderiv ℂ H z).range ≤ Module.finrank ℂ R := by
    intro z hz
    rw [fderiv_comp z (hf _ (hprop z hz).2.1).differentiableAt (hprop z hz).1.differentiableAt]
    exact (finrank_range_comp_le _ _).trans (hr _ (hprop z hz).2.1)
  have hconst {r : R} (hrA : r∈A) {k : L.ker} (hkB : k∈B) : H (r,k)=H (r,0) :=
    constant_vertical Metric.isOpen_ball Metric.isOpen_ball (convex_ball (0 : L.ker) ε).isPreconnected
      hH p (fun z hz => (hprop z hz).2.2) hrH hrA hkB (Metric.mem_ball_self hε)
  let e : Space (Module.finrank ℂ R) ≃L[ℂ] R :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).symm
  let q : Space (Module.finrank ℂ R) → F := fun z => H (e z,0)
  let c := e.symm (g x)
  have hcA : e c ∈ A := by simpa [c,A] using Metric.mem_ball_self hε (x := g x)
  have hq : AnalyticAt ℂ q c :=
    AnalyticAt.comp (f := fun z => (e z,(0 : L.ker))) (x := c)
      (hH (e c,0) ⟨hcA,Metric.mem_ball_self hε⟩) ((e.analyticAt c).prod analyticAt_const)
  obtain ⟨δ,hδ,hδprop⟩ := Metric.mem_nhds_iff.mp
    (hq.eventually_analyticAt.and (e.continuousAt (Metric.isOpen_ball.mem_nhds hcA)))
  let P : Patch F := ⟨Module.finrank ℂ R,Metric.ball c δ,Metric.isOpen_ball,
    (convex_ball c δ).isPreconnected,q,fun z hz => (hδprop hz).1⟩
  have hnear : ∀ᶠ y in 𝓝 x, e.symm (g y) ∈ Metric.ball c δ :=
    (e.symm.continuousAt.comp hg.continuousAt) (Metric.ball_mem_nhds c hδ)
  have hknear : ∀ᶠ y in 𝓝 x, φ.rightFun y∈B :=
    hright.continuousAt (by simpa [φ,B] using Metric.ball_mem_nhds (0 : L.ker) hε)
  obtain ⟨W,hW,hWo,hWx⟩ := eventually_nhds_iff.mp
    (Filter.Eventually.and (hU.mem_nhds hx) (hnear.and (hknear.and φ.implicitFunction_apply_image)))
  refine ⟨P,rfl,W,hWo,hWx,fun y hy => (hW y hy).1,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  refine ⟨e.symm (g y),(hW y hy).2.1,?_⟩
  change H (e (e.symm (g y)),0)=f y
  rw [e.apply_symm_apply]
  have hgA : g y∈A := by
    have hh := (hδprop (hW y hy).2.1).2
    simpa only [e.apply_symm_apply] using hh
  rw [← hconst hgA (hW y hy).2.2.1]
  change f (φ.implicitFunction (g y) (φ.rightFun y))=f y
  exact congrArg f (hW y hy).2.2.2

end AnalyticZeroCover

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology


open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
namespace SplitTangent

 

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

instance (U : Set ℂ) : CoeFun (AnalyticFunction U) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

open scoped MvPowerSeries.WithPiTopology

end FormalCauchy
end SplitTangent

open Set Filter Topology

open Filter Topology

section FiniteBaseImport
open Polynomial
namespace SplitTangent.RationalSurface

local instance : DecidableEq K := Classical.decEq K

variable {ι : Type*} [Fintype ι]

end SplitTangent.RationalSurface

end FiniteBaseImport

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 
lemma eventually_zero_of_all_derivatives {f : E → F} {x : E}
    (hf : AnalyticAt ℂ f x) (h : ∀ n, iteratedFDeriv ℂ n f x = 0) :
    f =ᶠ[𝓝 x] 0 := by
  obtain ⟨p,r,hp⟩ := hf
  filter_upwards [Metric.eball_mem_nhds x hp.r_pos] with y hy
  have hh := hp.hasSum_iteratedFDeriv (y := y-x) (by simpa only [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero] using hy)
  simp only [h, zero_apply, smul_zero, add_sub_cancel] at hh
  exact hh.unique (hasSum_zero)

lemma analyticAt_iterated {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) (n : ℕ) :
    AnalyticAt ℂ (iteratedFDeriv ℂ n f) x :=
  (show AnalyticOnNhd ℂ f {x} from fun _ hy => mem_singleton_iff.mp hy ▸ hf).iteratedFDeriv n x
    (mem_singleton x)

 
def coeffDerivative {d : ℕ} (f : Space d → ℂ) (n : ℕ) (k : Fin n → Fin d) :
    Space d → ℂ := fun x => iteratedFDeriv ℂ n f x (fun i => Pi.single (k i) 1)

lemma coeffDerivative_analytic {d n : ℕ} {f : Space d → ℂ} {x : Space d}
    (hf : AnalyticAt ℂ f x) (k : Fin n → Fin d) :
    AnalyticAt ℂ (coeffDerivative f n k) x := by
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Space d) ℂ
    (fun i => Pi.single (k i) 1)).analyticAt _).comp (analyticAt_iterated hf n)

lemma derivative_zero_of_coefficients {d n : ℕ} {f : Space d → ℂ} {x : Space d}
    (h : ∀ k : Fin n → Fin d, coeffDerivative f n k x = 0) :
    iteratedFDeriv ℂ n f x = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => Pi.basisFun ℂ (Fin d))
  intro k
  simpa only [coeffDerivative,Pi.basisFun_apply,ContinuousMultilinearMap.coe_coe,
    zero_apply] using h k

 

theorem exists_regular_derivative {d : ℕ} {f : Space d → ℂ} {x : Space d}
    (hf : AnalyticAt ℂ f x) (hx : f x=0) (hn : ¬ f =ᶠ[𝓝 x] 0) :
    ∃ (n : ℕ) (k : Fin n → Fin d), coeffDerivative f n k x=0 ∧
      fderiv ℂ (coeffDerivative f n k) x ≠ 0 := by
  classical
  have he : ∃ n, iteratedFDeriv ℂ n f x ≠ 0 := by
    by_contra! h
    exact hn (eventually_zero_of_all_derivatives hf h)
  let n := Nat.find he
  have hn0 : n ≠ 0 := by
    intro h
    have hh := Nat.find_spec he
    rw [show Nat.find he=0 from h] at hh
    apply hh
    ext v
    simp [iteratedFDeriv_zero_apply,hx]
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hm0 : iteratedFDeriv ℂ m f x=0 := by
    by_contra hc
    have := Nat.find_min' he hc
    dsimp [n] at hm
    omega
  have hm1 : iteratedFDeriv ℂ (m+1) f x≠0 := by
    have hh : iteratedFDeriv ℂ n f x ≠ 0 := Nat.find_spec he
    rw [hm] at hh
    exact hh
  have hk : ∃ k : Fin (m+1) → Fin d, coeffDerivative f (m+1) k x ≠ 0 := by
    by_contra! h
    exact hm1 (derivative_zero_of_coefficients h)
  obtain ⟨k,hk⟩ := hk
  refine ⟨m,Fin.tail k,?_,?_⟩
  · simp [coeffDerivative,hm0]
  · intro hz
    apply hk
    have hd := (analyticAt_iterated hf m).differentiableAt.iteratedFDeriv_succ_apply_left'
      (m := fun i => Pi.single (k i) 1)
    change iteratedFDeriv ℂ (m+1) f x (fun i => Pi.single (k i) 1)=0
    rw [hd]
    change fderiv ℂ (coeffDerivative f m (Fin.tail k)) x (Pi.single (k 0) 1)=0
    rw [hz,zero_apply]

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

theorem regular_zero_patch {d : ℕ} {f : Space d → ℂ} {x : Space d}
    {U : Set (Space d)} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : AnalyticAt ℂ f x) (hx : f x=0) (hd : fderiv ℂ f x ≠ 0) :
    ∃ P : Patch (Space d), P.dim < d ∧ P.image ⊆ U ∩ {y | f y=0} ∧
      ∃ V : Set (Space d), IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, f y=0 → y ∈ P.image := by
  classical
  let L := fderiv ℂ f x
  have hL : L.toLinearMap ≠ 0 := by
    intro hh
    apply hd
    ext v
    exact congrArg (fun q : Space d →ₗ[ℂ] ℂ => q v) hh
  have hr : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hL
  have hk := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented f L
    ((hf.contDiffAt (n := ω)).hasStrictFDerivAt (by simp)) hr hk
  let m := Module.finrank ℂ L.ker
  let e : Space m ≃L[ℂ] L.ker :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).symm
  have hm : m < d := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hL
    have hh' : m + 1 = d := by simpa only [Space,Module.finrank_fin_fun] using hh
    omega
  have hright : AnalyticAt ℂ φ.rightFun x := by
    exact ((Classical.choose hk).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ : AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    (φ.contDiffAt_implicitFunction hf.contDiffAt hright.contDiffAt (by simp)).analyticAt
  have hbase : φ.prodFun φ.pt = (0,0) := by
    ext <;> simp [φ,ImplicitFunctionData.prodFun,hx]
  have hval : φ.implicitFunction 0 0 = x := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ,hx] using hh
  let g : Space m → Space d := fun z => φ.implicitFunction 0 (e z)
  have hg : AnalyticAt ℂ g 0 := by
    have hh : AnalyticAt ℂ φ.implicitFunction.uncurry (0,e 0) := by
      simpa only [hbase,map_zero] using hφ
    exact AnalyticAt.comp (f := fun z : Space m => (0,e z)) (x := 0) hh
      (analyticAt_const.prod (e.analyticAt 0))
  have hg0 : g 0=x := by simpa [g] using hval
  have hfg : ∀ᶠ z in 𝓝 (0 : Space m), f (g z)=0 := by
    have ht : Tendsto (fun z : Space m => (0,e z)) (𝓝 0) (𝓝 (φ.prodFun φ.pt)) := by
      rw [hbase]
      simpa using (continuous_const.prodMk e.continuous).continuousAt.tendsto (x := 0)
    exact ht.eventually φ.leftFun_implicitFunction
  have hgU : ∀ᶠ z in 𝓝 (0 : Space m), g z∈U :=
    hg.continuousAt (hg0 ▸ hU.mem_nhds hxU)
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp
    (hg.eventually_analyticAt.and (hgU.and hfg))
  let W := Metric.ball (0 : Space m) r
  have hWo : IsOpen W := Metric.isOpen_ball
  have hW0 : (0 : Space m)∈W := Metric.mem_ball_self hr
  have hWh : ∀ z∈W, AnalyticAt ℂ g z ∧ g z∈U ∧ f (g z)=0 := hrW
  let P : Patch (Space d) := ⟨m,W,hWo,(convex_ball (0 : Space m) r).isPreconnected,
    g,fun z hz => (hWh z hz).1⟩
  refine ⟨P,hm,?_,?_⟩
  · rintro y ⟨z,hz,rfl⟩
    exact (hWh z hz).2
  · have hψ : ContinuousAt (fun y => e.symm (φ.rightFun y)) x :=
      e.symm.continuousAt.comp hright.continuousAt
    have hψ0 : e.symm (φ.rightFun x)=0 := by simp [φ]
    have hψW : ∀ᶠ y in 𝓝 x, e.symm (φ.rightFun y)∈W :=
      hψ (by simpa only [hψ0] using hWo.mem_nhds hW0)
    obtain ⟨V,hV,hVo,hVx⟩ := _root_.eventually_nhds_iff.mp
      (hψW.and φ.implicitFunction_apply_image)
    refine ⟨V,hVo,hVx,fun y hy hfy => ?_⟩
    refine ⟨e.symm (φ.rightFun y),(hV y hy).1,?_⟩
    change φ.implicitFunction 0 (e (e.symm (φ.rightFun y)))=y
    rw [e.apply_symm_apply]
    have hh := (hV y hy).2
    simpa only [show φ.leftFun y=f y from rfl,hfy] using hh

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

 
theorem countable_regular_zero_cover {d : ℕ} {f : Space d → ℂ}
    {U : Set (Space d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P ∈ C, P.dim < d ∧ P.image ⊆ U) ∧
      {x | x∈U ∧ f x=0 ∧ fderiv ℂ f x≠0} ⊆ ⋃ P∈C,P.image := by
  classical
  let A := {x | x∈U ∧ f x=0 ∧ fderiv ℂ f x≠0}
  have hlocal (x : A) := regular_zero_patch hU x.property.1
    (hf x x.property.1) x.property.2.1 x.property.2.2
  choose P hdim himg V hVo hVx hVcover using hlocal
  have hcover : A ⊆ ⋃ x : A,V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hVx ⟨x,hx⟩⟩
  obtain ⟨D,hD,hDA⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover V hVo hcover
  refine ⟨P '' D,hD.image P,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨hdim x,fun y hy => (himg x hy).1⟩
  · intro y hy
    obtain ⟨x,hx,hyV⟩ := mem_iUnion₂.mp (hDA hy)
    exact mem_iUnion₂.mpr ⟨P x,mem_image_of_mem P hx,hVcover x y hyV hy.2.1⟩

 

theorem countable_zero_cover {d : ℕ} {f : Space d → ℂ}
    {U : Set (Space d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ x∈U, f x=0 → ¬ f =ᶠ[𝓝 x] 0) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P ∈ C, P.dim < d ∧ P.image ⊆ U) ∧
      {x | x∈U ∧ f x=0} ⊆ ⋃ P∈C,P.image := by
  classical
  let I := Σ n : ℕ, Fin n → Fin d
  have hlocal (i : I) := countable_regular_zero_cover hU
    (fun x hx => coeffDerivative_analytic (hf x hx) i.2)
  choose C hC hdim hcover using hlocal
  refine ⟨⋃ i,C i,Set.countable_iUnion hC,?_,?_⟩
  · intro P hP
    obtain ⟨i,hi⟩ := mem_iUnion.mp hP
    exact hdim i P hi
  · intro x hx
    obtain ⟨n,k,hk0,hk1⟩ := exists_regular_derivative (hf x hx.1) hx.2 (hn x hx.1 hx.2)
    obtain ⟨P,hP,hxP⟩ := mem_iUnion₂.mp (hcover ⟨n,k⟩ ⟨hx.1,hk0,hk1⟩)
    exact mem_iUnion₂.mpr ⟨P,mem_iUnion.mpr ⟨⟨n,k⟩,hP⟩,hxP⟩

 
theorem countable_zero_cover_of_nonzero {d : ℕ} {f : Space d → ℂ}
    {U : Set (Space d)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) (hne : ∃ x∈U, f x≠0) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P ∈ C, P.dim < d ∧ P.image ⊆ U) ∧
      {x | x∈U ∧ f x=0} ⊆ ⋃ P∈C,P.image := by
  apply countable_zero_cover hU hf
  intro x hx _ he
  obtain ⟨y,hy,hy0⟩ := hne
  exact hy0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hx he hy)

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover

 

structure AnalyticSetOn {d : ℕ} (U A : Set (Space d)) : Prop where
  subset : A ⊆ U
  closed : closure A ∩ U ⊆ A
  local_equations : ∀ x∈A, ∃ V : Set (Space d), IsOpen V ∧ x∈V ∧ V ⊆ U ∧
    ∃ F : Set (Space d → ℂ), (∀ f∈F, AnalyticOnNhd ℂ f V) ∧
      ∀ y∈V, y∈A ↔ ∀ f∈F, f y=0

 
lemma AnalyticSetOn.closure_interior {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) : closure (interior A) ∩ U ⊆ interior A := by
  intro x hx
  have hxA : x∈A := h.closed ⟨closure_mono interior_subset hx.1,hx.2⟩
  obtain ⟨V,hVo,hVx,hVU,F,hF,hEq⟩ := h.local_equations x hxA
  obtain ⟨r,hr,hBV⟩ := Metric.isOpen_iff.mp hVo x hVx
  let B := Metric.ball x r
  have hBx : x∈B := Metric.mem_ball_self hr
  obtain ⟨y,hyB,hyA⟩ := mem_closure_iff.mp hx.1 B Metric.isOpen_ball hBx
  have hBA : B ⊆ A := by
    intro z hz
    apply (hEq z (hBV hz)).mpr
    intro f hf
    have hfe : f =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_interior.mem_nhds hyA, Metric.isOpen_ball.mem_nhds hyB]
        with w hwA hwB
      exact (hEq w (hBV hwB)).mp (interior_subset hwA) f hf
    exact (hF f hf).mono hBV |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x r).isPreconnected hyB hfe hz
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds hBx) hBA)

 
theorem AnalyticSetOn.interior_eq_empty {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) (hconn : IsPreconnected U) (hne : ∃ x∈U, x∉A) :
    interior A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hU : U ⊆ interior A := hconn.subset_of_closure_inter_subset isOpen_interior
    ⟨x,h.subset (interior_subset hx),hx⟩ h.closure_interior
  obtain ⟨y,hy,hyA⟩ := hne
  exact hyA (interior_subset (hU hy))

 

lemma AnalyticSetOn.local_cover {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) (hconn : IsPreconnected U) (hne : ∃ x∈U, x∉A)
    {x : Space d} (hx : x∈A) :
    ∃ B : Set (Space d), IsOpen B ∧ x∈B ∧
      ∃ C : Set (Patch (Space d)), C.Countable ∧
        (∀ P∈C, P.dim < d ∧ P.image ⊆ U) ∧ A ∩ B ⊆ ⋃ P∈C,P.image := by
  classical
  obtain ⟨V,hVo,hVx,hVU,F,hF,hEq⟩ := h.local_equations x hx
  obtain ⟨r,hr,hBV⟩ := Metric.isOpen_iff.mp hVo x hVx
  let B := Metric.ball x r
  have hBx : x∈B := Metric.mem_ball_self hr
  have he : ∃ f∈F, ∃ y∈B, f y≠0 := by
    by_contra! he
    have hBA : B ⊆ A := fun y hy => (hEq y (hBV hy)).mpr (fun f hf => he f hf y hy)
    have hi : x∈interior A := mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hBx) hBA)
    rw [h.interior_eq_empty hconn hne] at hi
    exact hi
  obtain ⟨f,hf,y,hy,hy0⟩ := he
  obtain ⟨C,hC,hP,hcover⟩ := countable_zero_cover_of_nonzero Metric.isOpen_ball
    (convex_ball x r).isPreconnected ((hF f hf).mono hBV) ⟨y,hy,hy0⟩
  refine ⟨B,Metric.isOpen_ball,hBx,C,hC,?_,?_⟩
  · intro P hPC
    exact ⟨(hP P hPC).1,((hP P hPC).2.trans hBV).trans hVU⟩
  · intro z hz
    exact hcover ⟨hz.2,(hEq z (hBV hz.2)).mp hz.1 f hf⟩

 

theorem AnalyticSetOn.countable_lower_cover {d : ℕ} {U A : Set (Space d)}
    (h : AnalyticSetOn U A) (hconn : IsPreconnected U) (hne : ∃ x∈U, x∉A) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P∈C, P.dim < d ∧ P.image ⊆ U) ∧ A ⊆ ⋃ P∈C,P.image := by
  classical
  have hlocal (x : A) := h.local_cover hconn hne x.property
  choose B hBo hBx C hC hdim hcover using hlocal
  have hAB : A ⊆ ⋃ x:A,B x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hBx ⟨x,hx⟩⟩
  obtain ⟨D,hD,hDA⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover B hBo hAB
  refine ⟨⋃ x∈D,C x,hD.biUnion (fun x _ => hC x),?_,?_⟩
  · intro P hP
    obtain ⟨x,hx,hPC⟩ := mem_iUnion₂.mp hP
    exact hdim x P hPC
  · intro z hz
    obtain ⟨x,hx,hzB⟩ := mem_iUnion₂.mp (hDA hz)
    obtain ⟨P,hPC,hzP⟩ := mem_iUnion₂.mp (hcover x ⟨hz,hzB⟩)
    exact mem_iUnion₂.mpr ⟨P, mem_iUnion₂.mpr ⟨x,hx,hPC⟩,hzP⟩

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def Patch.comp (P : Patch E) (Q : Patch (Space P.dim)) (h : Q.image ⊆ P.domain) : Patch E where
  dim := Q.dim
  domain := Q.domain
  isOpen_domain := Q.isOpen_domain
  preconnected_domain := Q.preconnected_domain
  map := P.map ∘ Q.map
  analytic z hz := (P.analytic _ (h ⟨z,hz,rfl⟩)).comp (Q.analytic z hz)

omit [CompleteSpace E] in
lemma Patch.comp_image_subset (P : Patch E) (Q : Patch (Space P.dim)) (h : Q.image⊆P.domain) :
    (P.comp Q h).image ⊆ P.image := by
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨Q.map z,h ⟨z,hz,rfl⟩,rfl⟩

 

omit [CompleteSpace E] in
theorem Patch.countable_accepted_cover {M A : Set E}
    (test : ∀ P : Patch E, P.image ⊆ M → ¬ P.image ⊆ A →
      ∃ B : Set (Space P.dim), AnalyticSetOn P.domain B ∧
        (∃ x∈P.domain, x∉B) ∧ {x | x∈P.domain ∧ P.map x∈A} ⊆ B)
    (P : Patch E) (hPM : P.image ⊆ M) :
    ∃ C : Set (Patch E), C.Countable ∧
      (∀ Q∈C, Q.dim ≤ P.dim ∧ Q.image ⊆ M ∩ A) ∧
      P.image ∩ A ⊆ ⋃ Q∈C, Q.image := by
  classical
  generalize hd : P.dim = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hPA : P.image ⊆ A
    · refine ⟨{P},countable_singleton P,?_,?_⟩
      · intro Q hQ
        obtain rfl := mem_singleton_iff.mp hQ
        exact ⟨hd.le,fun y hy => ⟨hPM hy,hPA hy⟩⟩
      · intro y hy
        exact mem_iUnion₂.mpr ⟨P,mem_singleton P,hy.1⟩
    · obtain ⟨B,hB,hproper,hAB⟩ := test P hPM hPA
      obtain ⟨D,hD,hDdim,hcover⟩ := hB.countable_lower_cover P.preconnected_domain hproper
      have hrec (i : D) : ∃ C : Set (Patch E), C.Countable ∧
          (∀ Q∈C, Q.dim ≤ (P.comp i.val (hDdim i.val i.property).2).dim ∧
            Q.image ⊆ M ∩ A) ∧
          (P.comp i.val (hDdim i.val i.property).2).image ∩ A ⊆ ⋃ Q∈C,Q.image := by
        apply ih i.val.dim (by simpa only [← hd] using (hDdim i.val i.property).1)
          (P.comp i.val (hDdim i.val i.property).2)
          ((P.comp_image_subset i.val (hDdim i.val i.property).2).trans hPM) rfl
      choose C hC hdim hCc using hrec
      let : Countable D := hD.to_subtype
      refine ⟨⋃ i,C i,Set.countable_iUnion hC,?_,?_⟩
      · intro Q hQ
        obtain ⟨i,hi⟩ := mem_iUnion.mp hQ
        exact ⟨(hdim i Q hi).1.trans ((le_of_lt (hDdim i.val i.property).1).trans hd.le),(hdim i Q hi).2⟩
      · rintro y ⟨⟨x,hx,rfl⟩,hxy⟩
        obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp (hcover (hAB ⟨hx,hxy⟩))
        obtain ⟨z,hz,hzx⟩ := hxQ
        have hyP : P.map x∈(P.comp Q (hDdim Q hQ).2).image := by
          refine ⟨z,hz,?_⟩
          change P.map (Q.map z)=P.map x
          rw [hzx]
        obtain ⟨R,hR,hyR⟩ := mem_iUnion₂.mp (hCc ⟨Q,hQ⟩ ⟨hyP,hxy⟩)
        exact mem_iUnion₂.mpr ⟨R,mem_iUnion.mpr ⟨⟨Q,hQ⟩,hR⟩,hyR⟩

 

theorem countable_open_patches {d : ℕ} {U : Set (Space d)} (hU : IsOpen U) :
    ∃ C : Set (Patch (Space d)), C.Countable ∧
      (∀ P∈C, P.dim=d ∧ P.image ⊆ U) ∧ U ⊆ ⋃ P∈C,P.image := by
  classical
  have hball (x : U) : ∃ r : ℝ, 0<r ∧ Metric.ball (x : Space d) r ⊆ U :=
    Metric.isOpen_iff.mp hU x x.property
  choose r hr hsub using hball
  let P : U → Patch (Space d) := fun x =>
    ⟨d,Metric.ball (x : Space d) (r x),Metric.isOpen_ball,
      (convex_ball (x : Space d) (r x)).isPreconnected,id,fun _ _ => analyticAt_id⟩
  obtain ⟨D,hD,hDU⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    (fun x : U => Metric.ball (x : Space d) (r x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  refine ⟨P '' D,hD.image P,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨rfl,?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact hsub x hz
  · intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp (hDU hz)
    exact mem_iUnion₂.mpr ⟨P x,mem_image_of_mem P hx,⟨z,hzx,rfl⟩⟩

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace SplitTangent.RationalParameters
open AnalyticZeroCover

abbrev Coeff (N d : ℕ) := Space ((N+1)*(d+1))

 
def ev {N d : ℕ} (b : Bool) (τ : Coeff N d) (z : ℂ) : Fin (N+1) → ℂ :=
  fun i => ∑ k : Fin (d+1), τ (finProdFinEquiv (i,k)) * z ^ (if b then d-k.val else k.val)

lemma ev_analytic {N d : ℕ} (b : Bool) (a : ℂ × Coeff N d) :
    AnalyticAt ℂ (fun z : ℂ × Coeff N d => ev b z.2 z.1) a := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (((ContinuousLinearMap.proj (finProdFinEquiv (i,k)) : Coeff N d →L[ℂ] ℂ).analyticAt _).comp
    analyticAt_snd).mul (analyticAt_fst.pow _)

lemma ev_continuous {N d : ℕ} (b : Bool) :
    Continuous (fun z : ℂ × Coeff N d => ev b z.2 z.1) :=
  continuous_iff_continuousAt.mpr (fun a => (ev_analytic b a).continuousAt)

lemma ev_transition {N d : ℕ} (τ : Coeff N d) {z : ℂ} (hz : z≠0) :
    ev false τ z = z^d • ev true τ z⁻¹ := by
  ext i
  simp only [ev,Bool.false_eq_true,↓reduceIte,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : k.val≤d := Nat.le_of_lt_succ k.isLt
  rw [inv_pow,← mul_assoc, mul_comm (z^d) (τ _),mul_assoc]
  congr 1
  rw [← div_eq_mul_inv,eq_div_iff (pow_ne_zero _ hz)]
  rw [← pow_add,Nat.add_sub_of_le hk]

 
def regular (N d : ℕ) : Set (Coeff N d) :=
  {τ | ∀ b : Bool, ∀ z∈Metric.closedBall (0 : ℂ) 1, ev b τ z≠0}

lemma isOpen_regular (N d : ℕ) : IsOpen (regular N d) := by
  let K := Metric.closedBall (0 : ℂ) 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have h (b : Bool) : IsOpen {τ : Coeff N d | ∀ z : K, ev b τ z≠0} := by
    have hc : IsClosed {z : K × Coeff N d | ev b z.2 z.1=0} :=
      isClosed_eq ((ev_continuous b).comp (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd))
        continuous_const
    have hp := isClosedMap_snd_of_compactSpace _ hc
    convert hp.isOpen_compl using 1
    ext τ
    simp
  convert isOpen_iInter_of_finite h using 1
  ext τ
  simp [regular,K]

lemma regular_nonzero {N d : ℕ} {τ : Coeff N d} (hτ : τ∈regular N d)
    (b : Bool) (z : ℂ) : ev b τ z≠0 := by
  by_cases hz : ‖z‖≤1
  · exact hτ b z (by simpa using hz)
  · have hz0 : z≠0 := by intro h; simp [h] at hz
    have hzi : z⁻¹∈Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall,dist_zero_right,norm_inv]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).mpr (le_of_lt (lt_of_not_ge hz))
    cases b
    · rw [ev_transition τ hz0]
      exact smul_ne_zero (pow_ne_zero _ hz0) (hτ true z⁻¹ hzi)
    · intro he
      have htrans := ev_transition τ (inv_ne_zero hz0)
      simp only [inv_inv,he,smul_zero] at htrans
      exact hτ false z⁻¹ hzi htrans

 
def accepted {X : ComplexManifold} (e : ProjectiveEmbedding X) (d : ℕ) : Set (Coeff e.N d) :=
  {τ | ∀ b : Bool, ∀ z : ℂ, ∃ x, e.Incidence x (ev b τ z)}


variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) [CompactSpace X.Carrier]
variable (x₀ : X.Carrier) {d : ℕ} (P : Patch (Coeff e.N d))
variable (hP : P.image ⊆ regular e.N d ∩ accepted e d)

 
def evaluation (b : Bool) (w : ℂ × Space P.dim) : X.Carrier :=
  e.coneLift x₀ (ev b (P.map w.2) w.1)

include hP in
lemma evaluation_holomorphicAt (b : Bool) {w : ℂ × Space P.dim} (hw : w.2∈P.domain) :
    ContMDiffAt 𝓘(ℂ,ℂ × Space P.dim) (ModelWithCorners X) ω (evaluation e x₀ P b) w := by
  apply e.holomorphic_of_incidence
    (AnalyticAt.comp (f := fun y : ℂ × Space P.dim => (y.1,P.map y.2)) (ev_analytic b (w.1,P.map w.2))
      (analyticAt_fst.prod ((P.analytic w.2 hw).comp analyticAt_snd)))
    (regular_nonzero (hP ⟨w.2,hw,rfl⟩).1 b w.1)
  have hv : ∀ᶠ y : ℂ × Space P.dim in 𝓝 w, y.2∈P.domain :=
    continuous_snd.continuousAt.eventually (P.isOpen_domain.mem_nhds hw)
  exact hv.mono (fun y hy => e.coneLift_incidence x₀ ((hP ⟨y.2,hy,rfl⟩).2 b y.1))

include hP in
omit [CompactSpace X.Carrier] in
lemma evaluation_overlap (z : ℂ) (hz : z≠0) {τ : Space P.dim} (hτ : τ∈P.domain) :
    evaluation e x₀ P false (z,τ) = evaluation e x₀ P true (z⁻¹,τ) := by
  dsimp only [evaluation]
  rw [ev_transition _ hz,e.coneLift_smul x₀ (pow_ne_zero d hz) ((hP ⟨τ,hτ,rfl⟩).2 true z⁻¹)]

def pairEvaluation (τ : Space P.dim) : X.Carrier × X.Carrier :=
  (evaluation e x₀ P false (0,τ),evaluation e x₀ P false (1,τ))

include hP in
lemma pairEvaluation_holomorphicAt {τ : Space P.dim} (hτ : τ∈P.domain) :
    ContMDiffAt 𝓘(ℂ,Space P.dim) ((ModelWithCorners X).prod (ModelWithCorners X)) ω
      (pairEvaluation e x₀ P) τ := by
  apply ContMDiffAt.prodMk
  · exact (evaluation_holomorphicAt e x₀ P hP false hτ).comp τ
      (contMDiffAt_const.prodMk_space contMDiffAt_id)
  · exact (evaluation_holomorphicAt e x₀ P hP false hτ).comp τ
      (contMDiffAt_const.prodMk_space contMDiffAt_id)

 

def family {W : Set (Space P.dim)} (hW : IsOpen W) (hne : W.Nonempty) (hWP : W⊆P.domain) :
    RationalFamily X (OpenManifold.manifold.{u} W hW hne) where
  finite p := evaluation e x₀ P false (p.1,OpenManifold.val W p.2)
  infinity p := evaluation e x₀ P true (p.1,OpenManifold.val W p.2)
  finite_holomorphic := by
    intro p
    exact (evaluation_holomorphicAt e x₀ P hP false (hWP p.2.down.property)).comp p
      (contMDiffAt_fst.prodMk_space ((OpenManifold.val_holomorphic W hW hne).contMDiffAt.comp p contMDiffAt_snd))
  infinity_holomorphic := by
    intro p
    exact (evaluation_holomorphicAt e x₀ P hP true (hWP p.2.down.property)).comp p
      (contMDiffAt_fst.prodMk_space ((OpenManifold.val_holomorphic W hW hne).contMDiffAt.comp p contMDiffAt_snd))
  overlap z hz τ := evaluation_overlap e x₀ P hP z hz (hWP τ.down.property)

end SplitTangent.RationalParameters

 

open Set Filter Topology
open scoped ContDiff Manifold

namespace SplitTangent.RationalParameters
open AnalyticZeroCover

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) [CompactSpace X.Carrier]

 

lemma analyticSetOn_incidence {m : ℕ} {U : Set (Space m)} (hU : IsOpen U)
    {Q : Space m → Fin (e.N+1) → ℂ} (hQ : AnalyticOnNhd ℂ Q U)
    (hnz : ∀ z∈U, Q z≠0) :
    AnalyticSetOn U {z | z∈U ∧ ∃ x, e.Incidence x (Q z)} where
  subset := fun _ h => h.1
  closed := by
    intro z hz
    refine ⟨hz.2,?_⟩
    change Q z ∈ {v | ∃ x, e.Incidence x v}
    rw [← e.isClosed_cone.closure_eq]
    exact (closure_mono (show Q '' {z | z∈U ∧ ∃ x, e.Incidence x (Q z)} ⊆
        {v | ∃ x, e.Incidence x v} from by rintro _ ⟨y,hy,rfl⟩; exact hy.2)
        (mem_closure_image (hQ z hz.2).continuousAt hz.1))
  local_equations := by
    intro z hz
    obtain ⟨D,hD,hDeq⟩ := e.cone_local_equations_any (hnz z hz.1)
    have hcomp : AnalyticAt ℂ (D ∘ Q) z := hD.comp (hQ z hz.1)
    have heq := (hQ z hz.1).continuousAt.eventually hDeq
    obtain ⟨V,hV,hVo,hVz⟩ := _root_.eventually_nhds_iff.mp
      (Filter.Eventually.and (hU.mem_nhds hz.1) (hcomp.eventually_analyticAt.and heq))
    let f : Fin (e.N+1) → Space m → ℂ := fun i y => D (Q y) i
    refine ⟨V,hVo,hVz,fun y hy => (hV y hy).1,Set.range f,?_,?_⟩
    · rintro g ⟨i,rfl⟩ y hy
      exact ((ContinuousLinearMap.proj i).analyticAt _).comp (hV y hy).2.1
    · intro y hy
      simp only [mem_ofPred_eq,forall_mem_range]
      have hyU : y∈U := (hV y hy).1
      simp only [hyU,true_and]
      rw [(hV y hy).2.2]
      exact ⟨fun h i => congrFun h i,fun h => funext h⟩

end SplitTangent.RationalParameters

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff


 

open Set Filter Topology
open scoped ContDiff

namespace AnalyticZeroCover
variable {E F R K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [FiniteDimensional ℂ R] [FiniteDimensional ℂ K]

theorem local_image_patch {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x∈U) (hf : AnalyticOnNhd ℂ f U)
    (p : F →L[ℂ] R) (hs : Function.Surjective (p.comp (fderiv ℂ f x)))
    (hr : ∀ y∈U, Module.finrank ℂ (fderiv ℂ f y).range ≤ Module.finrank ℂ R) :
    ∃ P : Patch F, P.dim=Module.finrank ℂ R ∧
      ∃ W : Set E, IsOpen W ∧ x∈W ∧ W⊆U ∧ f '' W ⊆ P.image := by
  classical
  let g : E → R := fun y => p (f y)
  let L := p.comp (fderiv ℂ f x)
  have hg : AnalyticAt ℂ g x := (p.analyticAt _).comp (hf x hx)
  have hgD : HasStrictFDerivAt g L x :=
    p.hasStrictFDerivAt.comp x (((hf x hx).contDiffAt (n := ω)).hasStrictFDerivAt (by simp))
  have hL : L.range=⊤ := LinearMap.range_eq_top.mpr hs
  have hK := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented g L hgD hL hK
  have hright : AnalyticAt ℂ φ.rightFun x :=
    ((Classical.choose hK).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ : AnalyticAt ℂ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    (φ.contDiffAt_implicitFunction hg.contDiffAt hright.contDiffAt (by simp)).analyticAt
  have hbase : φ.prodFun φ.pt=(g x,0) := by
    ext <;> simp [φ,ImplicitFunctionData.prodFun]
  have hval : φ.implicitFunction (g x) 0=x := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ] using hh
  have hφ' : AnalyticAt ℂ φ.implicitFunction.uncurry (g x,0) := hbase ▸ hφ
  have hφU : ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), φ.implicitFunction.uncurry z∈U :=
    hφ'.continuousAt (by simpa only [Function.uncurry_apply_pair,hval] using hU.mem_nhds hx)
  have hφp : ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), p (f (φ.implicitFunction.uncurry z))=z.1 := by
    change ∀ᶠ z in 𝓝 (g x,(0 : L.ker)), φ.leftFun (φ.implicitFunction z.1 z.2)=z.1
    rw [← hbase]
    exact φ.leftFun_implicitFunction
  obtain ⟨ε,hε,hεprop⟩ := Metric.mem_nhds_iff.mp
    (hφ'.eventually_analyticAt.and (hφU.and hφp))
  let A := Metric.ball (g x) ε
  let B := Metric.ball (0 : L.ker) ε
  have hAB : A ×ˢ B = Metric.ball (g x,(0 : L.ker)) ε := by
    ext z
    simp only [A,B,mem_prod,Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  let H : R × L.ker → F := f ∘ φ.implicitFunction.uncurry
  have hprop (z : R × L.ker) (hz : z∈A ×ˢ B) :
      AnalyticAt ℂ φ.implicitFunction.uncurry z ∧
        φ.implicitFunction.uncurry z∈U ∧ p (H z)=z.1 := hεprop (hAB ▸ hz)
  have hH : AnalyticOnNhd ℂ H (A ×ˢ B) := fun z hz =>
    (hf _ (hprop z hz).2.1).comp (hprop z hz).1
  have hrH : ∀ z∈A ×ˢ B, Module.finrank ℂ (fderiv ℂ H z).range ≤ Module.finrank ℂ R := by
    intro z hz
    rw [fderiv_comp z (hf _ (hprop z hz).2.1).differentiableAt (hprop z hz).1.differentiableAt]
    exact (finrank_range_comp_le _ _).trans (hr _ (hprop z hz).2.1)
  have hconst {r : R} (hrA : r∈A) {k : L.ker} (hkB : k∈B) : H (r,k)=H (r,0) :=
    constant_vertical Metric.isOpen_ball Metric.isOpen_ball (convex_ball (0 : L.ker) ε).isPreconnected
      hH p (fun z hz => (hprop z hz).2.2) hrH hrA hkB (Metric.mem_ball_self hε)
  let e : Space (Module.finrank ℂ R) ≃L[ℂ] R :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm).symm
  let q : Space (Module.finrank ℂ R) → F := fun z => H (e z,0)
  let c := e.symm (g x)
  have hcA : e c ∈ A := by simpa [c,A] using Metric.mem_ball_self hε (x := g x)
  have hq : AnalyticAt ℂ q c :=
    AnalyticAt.comp (f := fun z => (e z,(0 : L.ker))) (x := c)
      (hH (e c,0) ⟨hcA,Metric.mem_ball_self hε⟩) ((e.analyticAt c).prod analyticAt_const)
  obtain ⟨δ,hδ,hδprop⟩ := Metric.mem_nhds_iff.mp
    (hq.eventually_analyticAt.and (e.continuousAt (Metric.isOpen_ball.mem_nhds hcA)))
  let P : Patch F := ⟨Module.finrank ℂ R,Metric.ball c δ,Metric.isOpen_ball,
    (convex_ball c δ).isPreconnected,q,fun z hz => (hδprop hz).1⟩
  have hnear : ∀ᶠ y in 𝓝 x, e.symm (g y) ∈ Metric.ball c δ :=
    (e.symm.continuousAt.comp hg.continuousAt) (Metric.ball_mem_nhds c hδ)
  have hknear : ∀ᶠ y in 𝓝 x, φ.rightFun y∈B :=
    hright.continuousAt (by simpa [φ,B] using Metric.ball_mem_nhds (0 : L.ker) hε)
  obtain ⟨W,hW,hWo,hWx⟩ := _root_.eventually_nhds_iff.mp
    (Filter.Eventually.and (hU.mem_nhds hx) (hnear.and (hknear.and φ.implicitFunction_apply_image)))
  refine ⟨P,rfl,W,hWo,hWx,fun y hy => (hW y hy).1,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  refine ⟨e.symm (g y),(hW y hy).2.1,?_⟩
  change H (e (e.symm (g y)),0)=f y
  rw [e.apply_symm_apply]
  have hgA : g y∈A := by
    have hh := (hδprop (hW y hy).2.1).2
    simpa only [e.apply_symm_apply] using hh
  rw [← hconst hgA (hW y hy).2.2.1]
  change f (φ.implicitFunction (g y) (φ.rightFun y))=f y
  exact congrArg f (hW y hy).2.2.2

end AnalyticZeroCover


 

open Set Filter Topology
open scoped ContDiff
namespace AnalyticZeroCover

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

 
def pivot {r : ℕ} (f : E → F) (p : F →L[ℂ] Space r) (s : Space r →L[ℂ] E) (x : E) : ℂ :=
  LinearMap.det ((p.comp (fderiv ℂ f x)).comp s).toLinearMap

omit [FiniteDimensional ℂ E] in
lemma pivot_analytic {r : ℕ} {f : E → F} {x : E} (hf : AnalyticAt ℂ f x)
    (p : F →L[ℂ] Space r) (s : Space r →L[ℂ] E) : AnalyticAt ℂ (pivot f p s) x := by
  classical
  have hentry (i j : Fin r) : AnalyticAt ℂ
      (fun y => p (fderiv ℂ f y (s (Pi.single j 1))) i) x :=
    ((ContinuousLinearMap.proj i).analyticAt _).comp ((p.analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ F (s (Pi.single j 1))).analyticAt _).comp hf.fderiv))
  change AnalyticAt ℂ (fun y => LinearMap.det ((p.comp (fderiv ℂ f y)).comp s).toLinearMap) x
  simp only [← LinearMap.det_toMatrix',Matrix.det_apply',LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply]
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact hentry (σ i) i

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
lemma pivot_surjective {r : ℕ} {f : E → F} {x : E}
    (p : F →L[ℂ] Space r) (s : Space r →L[ℂ] E) (h : pivot f p s x ≠ 0) :
    Function.Surjective (p.comp (fderiv ℂ f x)) := by
  let A := ((p.comp (fderiv ℂ f x)).comp s).toLinearMap
  have hker : A.ker=⊥ := by
    by_contra hh
    exact h (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hh)
  have hi : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hs := LinearMap.injective_iff_surjective.mp hi
  intro y
  obtain ⟨z,hz⟩ := hs y
  exact ⟨s z,hz⟩

 

omit [FiniteDimensional ℂ F] in
lemma exists_pivot (L : E →L[ℂ] F) :
    ∃ (p : F →L[ℂ] Space (Module.finrank ℂ L.range))
      (s : Space (Module.finrank ℂ L.range) →L[ℂ] E),
      (p.comp L).comp s = ContinuousLinearMap.id ℂ _ := by
  classical
  obtain ⟨q,hq⟩ := Submodule.ClosedComplemented.of_finiteDimensional L.range
  let e : L.range ≃L[ℂ] Space (Module.finrank ℂ L.range) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  let p := e.toContinuousLinearMap.comp q
  have hp : Function.Surjective (p.comp L) := by
    intro y
    obtain ⟨v,hv⟩ := (e.symm y).property
    refine ⟨v,?_⟩
    change e (q (L v))=y
    change L v = (e.symm y : F) at hv
    rw [hv,hq,e.apply_symm_apply]
  obtain ⟨s,hs⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hp
  exact ⟨p,s,ContinuousLinearMap.ext hs⟩

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff ENNReal
namespace AnalyticZeroCover

 
lemma dimH_image_le_of_local {E F : Type*} [TopologicalSpace E]
    [SecondCountableTopology E] [EMetricSpace F] {f : E → F} {V : Set E} {a : ℝ≥0∞}
    (h : ∀ x∈V, ∃ W : Set E, IsOpen W ∧ x∈W ∧ dimH (f '' W)≤a) :
    dimH (f '' V)≤a := by
  classical
  choose W hWo hxW hdim using (fun x : V => h x x.property)
  obtain ⟨D,hD,hcover⟩ := (HereditarilyLindelofSpace.isLindelof V).elim_countable_subcover
    W hWo (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxW ⟨x,hx⟩⟩)
  apply (dimH_mono (show f '' V ⊆ ⋃ i∈D,f '' W i from ?_)).trans
  · rw [dimH_bUnion hD]
    exact iSup₂_le (fun i _ => hdim i)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨i,hi,mem_image_of_mem f hxi⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

 

theorem rank_dimH_le {d r : ℕ} {f : Space d → F} {U : Set (Space d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀ x∈U, Module.finrank ℂ (fderiv ℂ f x).range ≤ r) :
    dimH (f '' U) ≤ (2*r : ℕ) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hne : U.Nonempty
    · let m := Nat.findGreatest (fun k => ∃ x∈U, Module.finrank ℂ (fderiv ℂ f x).range=k) r
      obtain ⟨x,hx,hxm⟩ : ∃ x∈U, Module.finrank ℂ (fderiv ℂ f x).range=m :=
        Nat.findGreatest_spec (P := fun k => ∃ x∈U, Module.finrank ℂ (fderiv ℂ f x).range=k) (hr hne.choose hne.choose_spec)
          ⟨hne.choose,hne.choose_spec,rfl⟩
      have hm : m≤r := Nat.findGreatest_le r
      have hmax : ∀ y∈U, Module.finrank ℂ (fderiv ℂ f y).range ≤ m := fun y hy =>
        Nat.le_findGreatest (hr y hy) ⟨y,hy,rfl⟩
      obtain ⟨p,s,hps⟩ := exists_pivot (fderiv ℂ f x)
      let θ := pivot f p s
      have hθ : AnalyticOnNhd ℂ θ U := fun y hy => pivot_analytic (hf y hy) p s
      have hθx : θ x≠0 := by
        change LinearMap.det _ ≠ 0
        rw [hps]
        simp
      let V := {y | y∈U ∧ θ y≠0}
      have hV : dimH (f '' V)≤(2*r : ℕ) := by
        apply dimH_image_le_of_local
        intro y hy
        obtain ⟨P,hP,W,hWo,hyW,hWU,hcov⟩ := local_image_patch hU hy.1 hf p
          (pivot_surjective p s hy.2) (fun z hz => by simpa only [Module.finrank_fin_fun,hxm] using hmax z hz)
        refine ⟨W,hWo,hyW,(dimH_mono hcov).trans (P.dimH_image_le.trans ?_)⟩
        exact_mod_cast Nat.mul_le_mul_left 2 (by simpa only [hP,Module.finrank_fin_fun,hxm] using hm)
      obtain ⟨C,hC,hCdim,hcover⟩ := countable_zero_cover_of_nonzero hU hUc hθ ⟨x,hx,hθx⟩
      have hrest (Q : C) : dimH ((f ∘ Q.val.map) '' Q.val.domain) ≤ (2*r : ℕ) := by
        apply ih Q.val.dim (hCdim Q.val Q.property).1 Q.val.isOpen_domain Q.val.preconnected_domain
          (fun z hz => (hf _ ((hCdim Q.val Q.property).2 ⟨z,hz,rfl⟩)).comp (Q.val.analytic z hz))
        intro z hz
        rw [fderiv_comp z (hf _ ((hCdim Q.val Q.property).2 ⟨z,hz,rfl⟩)).differentiableAt
          (Q.val.analytic z hz).differentiableAt]
        exact (finrank_range_comp_le _ _).trans (hr _ ((hCdim Q.val Q.property).2 ⟨z,hz,rfl⟩))
      have hsub : f '' U ⊆ f '' V ∪ ⋃ Q∈C,(f ∘ Q.map) '' Q.domain := by
        rintro _ ⟨y,hy,rfl⟩
        by_cases hθy : θ y=0
        · obtain ⟨Q,hQ,z,hz,hzy⟩ := mem_iUnion₂.mp (hcover ⟨hy,hθy⟩)
          exact Or.inr (mem_iUnion₂.mpr ⟨Q,hQ,z,hz,congrArg f hzy⟩)
        · exact Or.inl ⟨y,⟨hy,hθy⟩,rfl⟩
      apply (dimH_mono hsub).trans
      rw [dimH_union,dimH_bUnion hC]
      exact max_le hV (iSup₂_le (fun Q hQ => hrest ⟨Q,hQ⟩))
    · rw [not_nonempty_iff_eq_empty.mp hne,image_empty,dimH_empty]
      exact bot_le

end AnalyticZeroCover

 

open Set Filter Topology
open scoped ContDiff ENNReal
namespace AnalyticZeroCover
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

lemma finrank_range_lt_of_not_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] F) (hL : ¬Function.Surjective L) :
    Module.finrank ℂ L.range < Module.finrank ℂ F := by
  apply lt_of_le_of_ne L.range.finrank_le
  intro heq
  exact hL (LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq heq))

lemma rank_dimH_le_open {d r : ℕ} {f : Space d → F} {U : Set (Space d)}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀x∈U,Module.finrank ℂ (fderiv ℂ f x).range≤r) :
    dimH (f '' U)≤(2*r : ℕ) := by
  apply dimH_image_le_of_local
  intro x hx
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨Metric.ball x ε,Metric.isOpen_ball,Metric.mem_ball_self hε,
    rank_dimH_le Metric.isOpen_ball (convex_ball x ε).isPreconnected
      (hf.mono hεU) (fun y hy => hr y (hεU hy))⟩

 

theorem exists_surjective_of_countable_cover {A : Type*} [Countable A]
    (d : A → ℕ) (U : ∀a,Set (Space (d a))) (f : ∀a,Space (d a) → F)
    (hU : ∀a,IsOpen (U a)) (hf : ∀a,AnalyticOnNhd ℂ (f a) (U a))
    {V : Set F} (hV : IsOpen V) (hne : V.Nonempty)
    (hcover : V ⊆ ⋃a,f a '' U a) (hdim : 0<Module.finrank ℂ F) :
    ∃a, ∃x, x∈U a ∧ Function.Surjective (fderiv ℂ (f a) x) := by
  classical
  by_contra! hbad
  have hpiece (a : A) : dimH (f a '' U a) ≤ (2*(Module.finrank ℂ F-1) : ℕ) :=
    rank_dimH_le_open (hU a) (hf a) (fun x hx => Nat.le_sub_one_of_lt
      (finrank_range_lt_of_not_surjective _ (hbad a x hx)))
  have hbound : dimH V ≤ (2*(Module.finrank ℂ F-1) : ℕ) := by
    apply (dimH_mono hcover).trans
    rw [dimH_iUnion]
    exact iSup_le hpiece
  obtain ⟨x,hx⟩ := hne
  have hc : Module.finrank ℝ F = 2*Module.finrank ℂ F := by
    rw [← Module.finrank_mul_finrank ℝ ℂ F,Complex.finrank_real_complex]
  rw [Real.dimH_of_mem_nhds (hV.mem_nhds hx),hc] at hbound
  have hnat : 2*Module.finrank ℂ F ≤ 2*(Module.finrank ℂ F-1) := by exact_mod_cast hbound
  omega

end AnalyticZeroCover

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold
namespace SplitTangent
open AnalyticZeroCover

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℂ,F) ω M]

 
theorem exists_chart_submersion_of_cover {A : Type*} [Countable A]
    (d : A → ℕ) (U : ∀a,Set (Space (d a))) (f : ∀a,Space (d a) → M)
    (hU : ∀a,IsOpen (U a))
    (hf : ∀a, ∀x∈U a,ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,F) ω (f a) x)
    {V : Set M} (hV : IsOpen V) (hne : V.Nonempty)
    (hcover : V ⊆ ⋃a,f a '' U a) (hdim : 0<Module.finrank ℂ F) :
    ∃y : M, ∃a, ∃x∈U a, f a x∈(chartAt F y).source ∧
      Function.Surjective (fderiv ℂ ((chartAt F y) ∘ f a) x) := by
  classical
  obtain ⟨y,hy⟩ := hne
  let c := chartAt F y
  let W (a : A) := U a ∩ (f a) ⁻¹' c.source
  have hW (a : A) : IsOpen (W a) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.inter_mem (hU a |>.mem_nhds hx.1)
      ((hf a x hx.1).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx.2))
  have hc : c∈maximalAtlas 𝓘(ℂ,F) ω M := IsManifold.chart_mem_maximalAtlas y
  have hanalytic (a : A) : AnalyticOnNhd ℂ (c ∘ f a) (W a) := by
    intro x hx
    exact ((contMDiffAt_of_mem_maximalAtlas hc hx.2).comp x (hf a x hx.1)).contDiffAt.analyticAt
  let Z := c.target ∩ c.symm ⁻¹' V
  have hZ : IsOpen Z := c.isOpen_inter_preimage_symm hV
  have hZn : Z.Nonempty := ⟨c y,c.map_source (mem_chart_source F y),by
    change c.symm (c y)∈V
    rw [c.left_inv (mem_chart_source F y)]
    exact hy⟩
  have hZcov : Z ⊆ ⋃a,(c ∘ f a) '' W a := by
    intro z hz
    obtain ⟨a,x,hx,hfx⟩ := mem_iUnion.mp (hcover hz.2)
    refine mem_iUnion.mpr ⟨a,x,⟨hx,?_⟩,?_⟩
    · change f a x∈c.source
      rw [hfx]
      exact c.map_target hz.1
    · change c (f a x)=z
      rw [hfx,c.right_inv hz.1]
  obtain ⟨a,x,hx,hs⟩ := exists_surjective_of_countable_cover d W
    (fun a => c ∘ f a) hW hanalytic hZ hZn hZcov hdim
  exact ⟨y,a,x,hx.1,hx.2,hs⟩

 
omit [FiniteDimensional ℂ F] in
lemma surjective_mfderiv_of_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → M} {x : E} (hf : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x)
    (y : M) (hy : f x∈(chartAt F y).source)
    (hs : Function.Surjective (fderiv ℂ ((chartAt F y) ∘ f) x)) :
    Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x) := by
  have hc := mdifferentiable_chart (I := 𝓘(ℂ,F)) y
  have hchain := mfderiv_comp x (hc.mdifferentiableAt hy) (hf.mdifferentiableAt (by decide))
  rw [mfderiv_eq_fderiv] at hchain
  intro w
  obtain ⟨v,hv⟩ := hs (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) (chartAt F y) (f x) w)
  refine ⟨v,hc.mfderiv_injective hy ?_⟩
  change ((mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) (chartAt F y) (f x)).comp
    (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x)) v = _
  rw [← hchain]
  exact hv

 

lemma eventually_surjective_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → F} {x : E} (hf : AnalyticAt ℂ f x)
    (hs : Function.Surjective (fderiv ℂ f x)) :
    ∀ᶠy in 𝓝 x, Function.Surjective (fderiv ℂ f y) := by
  let e : F ≃L[ℂ] Space (Module.finrank ℂ F) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  obtain ⟨s,hs⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (f := e.toContinuousLinearMap.comp (fderiv ℂ f x)) (e.surjective.comp hs)
  have heq : (e.toContinuousLinearMap.comp (fderiv ℂ f x)).comp s = ContinuousLinearMap.id ℂ _ :=
    ContinuousLinearMap.ext hs
  have hp : pivot f e.toContinuousLinearMap s x≠0 := by
    change LinearMap.det _ ≠ 0
    rw [heq]
    simp
  apply ((pivot_analytic hf e.toContinuousLinearMap s).continuousAt.eventually_ne hp).mono
  intro y hy z
  obtain ⟨v,hv⟩ := pivot_surjective e.toContinuousLinearMap s hy (e z)
  exact ⟨v,e.injective hv⟩

end SplitTangent

namespace SplitTangent.RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)
 

theorem integrable_both_of_submersive [CompactSpace X.Carrier]
    [ConnectedSpace X.Carrier] [Nonempty T.Carrier]
    (e : ProjectiveEmbedding X) (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    Integrable X S.first ∧ Integrable X S.second := by
  classical
  apply G.integrable_both_of_submersive_transport S hs
  · intro τ
    let F := Classical.choice (S.exists_projective_tangent_box e (G.curve τ))
    exact Classical.choice (F.exists_normalized_factor_transport b)
  · intro τ
    let F := Classical.choice (S.swap.exists_projective_tangent_box e (G.curve τ))
    exact Classical.choice (F.exists_normalized_factor_transport b)
end SplitTangent.RationalFamily

end

end OAI
