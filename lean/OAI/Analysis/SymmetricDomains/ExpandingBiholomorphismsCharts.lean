import Mathlib
import OAI.Analysis.SymmetricDomains.ChartJacobianNeZero

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
namespace Release061
open Set Filter Metric
open scoped Topology

theorem chart_jacobian_of_biholomorph {n m : ℕ}
    {W S : Set (Affine n)} {D T : Set (Affine m)}
    (hWS : W ⊆ S) (hD : IsOpen D) (hT : IsOpen T)
    (e : Biholomorph W D) (b : Biholomorph S T)
    {f : Affine n → Affine m}
    (hf : ∀ q : W, f q.val = (b.toHomeomorph ⟨q.val,hWS q.property⟩).val) :
    HolomorphicOnSubset W (fun q => f q) ∧
      ∀ z ∈ D, (fderiv ℂ
        (f ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0 := by
  have hfh : HolomorphicOnSubset W (fun q => f q) := by
    intro q
    obtain ⟨A,hAo,hqA,φ,hφ,hext⟩ := b.holomorphic_toFun ⟨q.val,hWS q.property⟩
    refine ⟨A,hAo,hqA,φ,hφ,?_⟩
    intro r hr
    change φ r.val = f r.val
    rw [hf r]
    exact hext ⟨r.val,hWS r.property⟩ hr
  refine ⟨hfh,?_⟩
  intro z hz
  let G := ambientExtend (fun x : T => (b.toHomeomorph.symm x).val)
  have hGa : AnalyticOnNhd ℂ G T := b.holomorphic_invFun.analyticOnNhd_extend hT
  have hleft : ∀ q ∈ W, f q ∈ T → G (f q) = q := by
    intro q hq _
    rw [hf ⟨q,hq⟩]
    dsimp only [G]
    rw [ambientExtend_apply _ (b.toHomeomorph ⟨q,hWS hq⟩),b.toHomeomorph.symm_apply_apply]
  let q : W := e.toHomeomorph.symm ⟨z,hz⟩
  have hqT : f q.val ∈ T := by rw [hf q]; exact (b.toHomeomorph ⟨q.val,hWS q.property⟩).property
  have hn := chart_jacobian_ne_zero_of_left_inverse hD hT e hfh hGa hleft q hqT
  simpa only [q,e.toHomeomorph.apply_symm_apply] using hn

theorem expanding_biholomorphisms_charts {n m : ℕ} {S : Set (Affine n)}
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAS : ∀ j, A j ⊆ S)
    (hAo : ∀ j, IsOpen ((Subtype.val : S → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m)
    (hf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hcover : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, K ⊆ A j) :
    ∀ p : S, ∃ W : Set (Affine n), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine m), IsOpen D ∧ IsPreconnected D ∧
      ∃ e : Biholomorph W D, ∀ᶠ j in atTop,
        HolomorphicOnSubset W (fun x => f j x) ∧
        ∀ z ∈ D, (fderiv ℂ
          (f j ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0 := by
  intro p
  obtain ⟨j,hj⟩ := (hcover {p.val} isCompact_singleton
    (singleton_subset_iff.mpr p.property)).exists
  have hpj : p.val ∈ A j := hj (mem_singleton p.val)
  let q : A j := ⟨p.val,hpj⟩
  let z := ((b j).toHomeomorph q).val
  obtain ⟨R,hR,hRB⟩ := Metric.mem_nhds_iff.mp
    ((hBo j).mem_nhds ((b j).toHomeomorph q).property)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrB : closedBall z r ⊆ B j :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hRB
  let W : Set (Affine n) := {x | x ∈ A j ∧ f j x ∈ ball z r}
  have hWA : W ⊆ A j := fun _ hx => hx.1
  have hfc : Continuous (fun x : A j => f j x.val) := by
    have heq : (fun x : A j => f j x.val) =
        (fun x : A j => ((b j).toHomeomorph x).val) := funext (hf j)
    rw [heq]
    exact continuous_subtype_val.comp (b j).toHomeomorph.continuous
  have hWo : IsOpen ((Subtype.val : A j → Affine n) ⁻¹' W) := by
    have heq : ((Subtype.val : A j → Affine n) ⁻¹' W) =
        {x : A j | f j x.val ∈ ball z r} := by
      ext x
      simp only [mem_preimage,W,mem_ofPred_eq,x.property,true_and]
    rw [heq]
    exact isOpen_ball.preimage hfc
  have hpW : p.val ∈ W := by
    refine ⟨hpj,?_⟩
    rw [hf j q]
    exact mem_ball_self hr
  have hrestrict : ∀ x : A j, x.val ∈ W ↔ ((b j).toHomeomorph x).val ∈ ball z r := by
    intro x
    simp only [W,mem_ofPred_eq,x.property,true_and,hf j x]
  let e := (b j).restrict hWA (ball_subset_closedBall.trans hrB) hrestrict
  let E := ambientExtend (fun x : B j => ((b j).toHomeomorph.symm x).val)
  have hEc : ContinuousOn E (B j) := continuousOn_ambientExtend
    (continuous_subtype_val.comp (b j).toHomeomorph.symm.continuous)
  have hEm : MapsTo E (B j) (A j) := by
    intro x hx
    rw [show E x = ((b j).toHomeomorph.symm ⟨x,hx⟩).val from ambientExtend_apply _ ⟨x,hx⟩]
    exact ((b j).toHomeomorph.symm ⟨x,hx⟩).property
  have hK : IsCompact (E '' closedBall z r) :=
    (isCompact_closedBall z r).image_of_continuousOn (hEc.mono hrB)
  have hKS : E '' closedBall z r ⊆ S := by
    rintro x ⟨y,hy,rfl⟩
    exact hAS j (hEm (hrB hy))
  have hWK : W ⊆ E '' closedBall z r := by
    intro x hx
    refine ⟨((b j).toHomeomorph ⟨x,hx.1⟩).val,?_,?_⟩
    · rw [← hf j ⟨x,hx.1⟩]
      exact ball_subset_closedBall hx.2
    · dsimp only [E]
      rw [ambientExtend_apply _ ((b j).toHomeomorph ⟨x,hx.1⟩),
        (b j).toHomeomorph.symm_apply_apply]
  refine ⟨W,hWA.trans (hAS j),relative_open_trans (hAS j) hWA (hAo j) hWo,hpW,
    ball z r,isOpen_ball,(convex_ball z r).isPreconnected,e,?_⟩
  filter_upwards [hcover _ hK hKS] with i hi
  exact chart_jacobian_of_biholomorph (hWK.trans hi) isOpen_ball (hBo i) e (b i)
    (fun x => hf i ⟨x.val,hi (hWK x.property)⟩)

end Release061

end

end OAI
