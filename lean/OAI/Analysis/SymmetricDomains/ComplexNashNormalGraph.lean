import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicAnalyticLocalInverse
import OAI.Analysis.SymmetricDomains.GenericNormalGraphProjection

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
namespace Release061
open Set Filter Topology Metric
open scoped Classical

theorem complex_nash_normal_graph {d r k : ℕ}
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine r × Affine k)
    (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (q x)).1))
    (hqn : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (q x)).2))
    {a : Fin d → ℝ} (ha : a ∈ B) (hq0 : q a = 0)
    (hdim : d = (r+r)+k) (hqi : Function.Injective (fderiv ℝ q a))
    (hqt : ∀ v i, (((fderiv ℝ q a) v).2 i).im = 0) :
    ∃ (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin ((r+r)+k) → ℝ))
      (R : ℝ) (φ : (Fin ((r+r)+k) → ℝ) → (Fin k → ℝ)),
      (e : (Fin d → ℝ) → _) = (fun x => (complexGraphRealEquiv r k (q x)).1) ∧
      a ∈ e.source ∧ e.symm 0 = a ∧ 0 < R ∧ ball 0 R ⊆ e.target ∧
      MapsTo e.symm (ball 0 R) B ∧
      AnalyticOnNhd ℝ e.symm (ball 0 R) ∧ SemialgebraicOn (ball 0 R) e.symm ∧
      AnalyticOnNhd ℝ φ (ball 0 R) ∧ SemialgebraicOn (ball 0 R) φ ∧
      φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      (∀ s ∈ ball 0 R, complexGraphRealEquiv r k (q (e.symm s)) = (s,φ s)) ∧
      (∀ᶠ x in 𝓝 a, e x ∈ ball 0 R ∧
        complexGraphRealEquiv r k (q x) = (e x,φ (e x))) := by
  let P := (ContinuousLinearMap.fst ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp
    (complexGraphRealEquiv r k).toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp
    (complexGraphRealEquiv r k).toContinuousLinearMap
  let f := P ∘ q
  let g := Q ∘ q
  have hf : AnalyticOnNhd ℝ f B := fun x hx => (P.analyticAt (q x)).comp (hqa x hx)
  have hg : AnalyticOnNhd ℝ g B := fun x hx => (Q.analyticAt (q x)).comp (hqa x hx)
  have hf0 : f a = 0 := by change P (q a) = 0; rw [hq0,map_zero]
  have hg0 : g a = 0 := by change Q (q a) = 0; rw [hq0,map_zero]
  let A := P.comp (fderiv ℝ q a)
  have hi : Function.Injective A := generic_normal_graph_projection_injective
    (fderiv ℝ q a) hqi hqt
  let L := (A.toLinearMap.linearEquivOfInjective hi (by simp [hdim])).toContinuousLinearEquiv
  have heL : (L : (Fin d → ℝ) →L[ℝ] (Fin ((r+r)+k) → ℝ)) = A := by ext v i; rfl
  have hfd : HasFDerivAt f A a := P.hasFDerivAt.comp a (hqa a ha).differentiableAt.hasFDerivAt
  obtain ⟨e,he,hes,R,hR,hRt,hRB,hea,hesa⟩ :=
    semialgebraic_analytic_local_inverse hB hqs ha (hf a ha) L (heL.symm ▸ hfd)
  simp only [hq0,map_zero,Prod.fst_zero] at hRt hRB hea hesa
  have hein : e.symm 0 = a := by
    have hh := e.left_inv hes
    change e.symm ((e : (Fin d → ℝ) → _) a) = a at hh
    rw [he,show (fun x => (complexGraphRealEquiv r k (q x)).1) = f from rfl,hf0] at hh
    exact hh
  let φ := g ∘ e.symm
  have hφa : AnalyticOnNhd ℝ φ (ball 0 R) :=
    fun s hs => (hg _ (hRB hs)).comp (hea s hs)
  have hφs : SemialgebraicOn (ball 0 R) φ := hqn.comp hesa hRB
  have hQ : Q.comp (fderiv ℝ q a) = 0 := by
    ext v i
    exact hqt v i
  have hgd : HasFDerivAt g (0 : (Fin d → ℝ) →L[ℝ] (Fin k → ℝ)) a := by
    have hh := Q.hasFDerivAt.comp a (hqa a ha).differentiableAt.hasFDerivAt
    rwa [hQ] at hh
  have hder : fderiv ℝ φ 0 = 0 := by
    have hh := (hein.symm ▸ hgd).comp 0 (hea 0 (mem_ball_self hR)).differentiableAt.hasFDerivAt
    exact hh.fderiv
  have hgraph : ∀ s ∈ ball 0 R, complexGraphRealEquiv r k (q (e.symm s)) = (s,φ s) := by
    intro s hs
    apply Prod.ext
    · have hh := e.right_inv (hRt hs)
      simpa only [he] using hh
    · rfl
  refine ⟨e,R,φ,he,hes,hein,hR,hRt,hRB,hea,hesa,hφa,hφs,?_,hder,hgraph,?_⟩
  · change g (e.symm 0) = 0
    rw [hein,hg0]
  · have hnear : ∀ᶠ x in 𝓝 a, e x ∈ ball 0 R := by
      have hec : ContinuousAt (e : (Fin d → ℝ) → _) a := e.continuousAt hes
      have he0 : e a = 0 := by rw [he]; exact hf0
      apply hec.preimage_mem_nhds
      rw [he0]
      exact ball_mem_nhds _ hR
    filter_upwards [hnear,e.open_source.mem_nhds hes] with x hx hxs
    refine ⟨hx,?_⟩
    have hh := hgraph (e x) hx
    simpa only [e.left_inv hxs] using hh
end Release061

end

end OAI
