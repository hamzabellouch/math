import Mathlib
import OAI.Analysis.FourierExtension.SmoothCharts
import OAI.Analysis.FourierExtension.ConvexExtension

namespace OAI

/-! Local convex graph coordinates for curved surfaces. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter

namespace DiagonalExtension.SmoothLevel
abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Plane := EuclideanSpace ℝ (Fin 2)

lemma tangent_finrank (L : Ambient →L[ℝ] ℝ) (hL : L ≠ 0) :
    Module.finrank ℝ L.ker = 2 := by
  have hL' : L.toLinearMap ≠ 0 := by
    intro he; apply hL; ext x; exact DFunLike.congr_fun he x
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hL'
  have hdim : Module.finrank ℝ Ambient = 3 := by simp [Ambient]
  rw [hdim] at hh
  omega

def tangentPlaneEquiv (L : Ambient →L[ℝ] ℝ) (hL : L ≠ 0) : L.ker ≃ₗᵢ[ℝ] Plane :=
  ((stdOrthonormalBasis ℝ L.ker).reindex (finCongr (tangent_finrank L hL))).repr

end DiagonalExtension.SmoothLevel

namespace DiagonalExtension.LocalGraph
open SmoothLevel Set Filter
open scoped Topology
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := WithLp 2 (Plane × ℝ)

def graph (φ : Plane → ℝ) (u : Plane) : Space := WithLp.toLp 2 (u,φ u)

lemma hessian_comp_linear {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : W → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : V →L[ℝ] W) (x v : V) :
    (fderiv ℝ (fderiv ℝ (f ∘ L)) x v) v =
      (fderiv ℝ (fderiv ℝ f) (L x) (L v)) (L v) := by
  have h := congrArg (fun B => B ![v,v])
    (L.iteratedFDeriv_comp_right hf x (i := 2) (by exact WithTop.coe_le_coe.mpr le_top))
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem exists_local_graph {S : Set E3} (hS : IsSurface S) {a : E3} (ha : a ∈ S) :
    ∃ (A : Space ≃L[ℝ] E3) (φ : Plane → ℝ) (c R : ℝ) (V : Set E3),
      0 < c ∧ 0 < R ∧ ContDiff ℝ ∞ φ ∧
      (∀ x v, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v) ∧
      IsOpen V ∧ a ∈ V ∧
      S ∩ V ⊆ (fun u => a + A (graph φ u)) '' Metric.closedBall 0 R := by
  obtain ⟨U,F,G,n,h,c,r,hU,haU,hF,hG,hreg,hF0,hG0,hn,hc,hr,hh0,hd0,
    hh,hlower,hiff,hbd⟩ := hS.exists_convex_chart ha
  let K := (fderiv ℝ F a).ker
  let e : K ≃ₗᵢ[ℝ] Plane := tangentPlaneEquiv (fderiv ℝ F a) hreg
  let L : (K × ℝ) ≃L[ℝ] E3 := kernelNormalEquiv (fderiv ℝ F a) n hn
  obtain ⟨c',hc',ψ,hψ,hψh,hψout,hψcomp,hψlower⟩ :=
    ConvexNeighborhood.local_convex_extension Metric.isOpen_ball
      (Metric.mem_ball_self hr) hh (fun v hv =>
        lt_of_lt_of_le (mul_pos hc (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)))
          (hlower 0 (Metric.mem_ball_self hr) v)) (by norm_num : (0:ℝ)<1)
  let φ : Plane → ℝ := ψ ∘ e.symm
  have hφ : ContDiff ℝ ∞ φ := hψ.comp e.symm.toContinuousLinearEquiv.contDiff
  have hφlower (x v : Plane) : c' * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v := by
    rw [show φ = ψ ∘ e.symm.toContinuousLinearEquiv.toContinuousLinearMap from rfl,
      hessian_comp_linear hψ]
    simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.norm_map] using hψlower (e.symm x) (e.symm v)
  let A : Space ≃L[ℝ] E3 :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).trans
      (e.symm.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))).trans L
  obtain ⟨s,hs,hse⟩ := Metric.eventually_nhds_iff.mp hψh
  let R : ℝ := min r s / 2
  have hR : 0 < R := half_pos (lt_min hr hs)
  have hRr : R < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
  have hRs : R < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
  let V : Set E3 := {y | ‖L.symm (y-a)‖ < R}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have haV : a ∈ V := by simpa [V] using hR
  refine ⟨A,φ,c',R,V,hc',hR,hφ,hφlower,hV,haV,?_⟩
  rintro y ⟨hyS,hyV⟩
  let z : K × ℝ := L.symm (y-a)
  have hzR : ‖z‖ < R := hyV
  have hzr : z ∈ Metric.ball 0 r := by simpa only [Metric.mem_ball,dist_zero_right] using hzR.trans hRr
  have hyEq : a + (z.1 : E3) + z.2 • n = y := by
    have heq := L.apply_symm_apply (y-a)
    change (z.1 : E3) + z.2 • n = y-a at heq
    rw [add_assoc,heq]
    abel
  have hheight : z.2 = h z.1 := ((hiff z hzr).2.mp (by rwa [hyEq])).1
  have hz1 : ‖z.1‖ < R := (norm_fst_le z).trans_lt hzR
  have hpatch : ψ z.1 = h z.1 := hse (by simpa only [dist_zero_right] using hz1.trans hRs)
  refine ⟨e z.1,?_,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map]
      using hz1.le
  · have heval : A (graph φ (e z.1)) = L z := by
      simp only [A,graph,ContinuousLinearEquiv.trans_apply,
        WithLp.prodContinuousLinearEquiv_apply,ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply,φ,Function.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.symm_apply_apply]
      rw [hpatch, ← hheight]
    change a + A (graph φ (e z.1)) = y
    rw [heval]
    change a + ((z.1 : E3) + z.2 • n) = y
    rwa [← add_assoc]

end DiagonalExtension.LocalGraph

end

end OAI
