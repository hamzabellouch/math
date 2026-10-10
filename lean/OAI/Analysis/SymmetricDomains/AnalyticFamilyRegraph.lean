import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticReparameterization

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
namespace Release061.Flatten
open Set Filter
open scoped Topology

theorem analytic_family_regraph {k : ℕ}
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), G (x,0) = realEmbedding k x)
    {Ω : Set (Fin k → ℂ)}
    (hΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω) :
    ∃ f : (Fin (k+1) → ℝ) → Fin k → ℝ, AnalyticAt ℝ f 0 ∧
      (∀ᶠ x in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 x) = 0) ∧
      ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 →
        (fun i => (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)) ∈ Ω := by
  have hreal : AnalyticAt ℝ (fun q => realPart k (G q)) 0 :=
    (realPart k).analyticAt _ |>.comp hG
  have hreal0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), realPart k (G (x,0)) = x := by
    filter_upwards [hG0] with x hx
    rw [hx]
    rfl
  obtain ⟨e,he,hem,he0,hia,hsnd,hbase⟩ := analytic_reparameterization hreal hreal0
  have hei0 : e.symm 0 = 0 := by
    calc e.symm 0 = e.symm (e 0) := congrArg e.symm he0.symm
         _ = 0 := e.left_inv hem
  let P : (Fin (k+1) → ℝ) →L[ℝ] ((Fin k → ℝ) × ℝ) :=
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)).prod
      (ContinuousLinearMap.proj 0)
  have hP (q : (Fin k → ℝ) × ℝ) : P (Fin.cons q.2 q.1) = q := by
    apply Prod.ext
    · ext i
      change (Fin.cons q.2 q.1 : Fin (k+1) → ℝ) i.succ = q.1 i
      exact Fin.cons_succ _ _ i
    · change (Fin.cons q.2 q.1 : Fin (k+1) → ℝ) 0 = q.2
      exact Fin.cons_zero _ _
  let f : (Fin (k+1) → ℝ) → Fin k → ℝ :=
    fun z => imaginaryPart k (G (e.symm (P z)))
  have ha : AnalyticAt ℝ (fun q => imaginaryPart k (G (e.symm q))) 0 := by
    have hG' : AnalyticAt ℝ G (e.symm 0) := by rwa [hei0]
    exact (imaginaryPart k).analyticAt _ |>.comp (hG'.comp hia)
  refine ⟨f,?_,?_,?_⟩
  · have ha' : AnalyticAt ℝ (fun q => imaginaryPart k (G (e.symm q))) (P 0) := by
      simpa only [map_zero] using ha
    exact ha'.comp (P.analyticAt 0)
  · filter_upwards [hbase,hG0] with x hx hx0
    change imaginaryPart k (G (e.symm (P (Fin.cons 0 x)))) = 0
    rw [hP (x,0),hx,hx0]
    ext i
    simp [imaginaryPart,realEmbedding]
  · have ht : Tendsto e.symm (𝓝 0) (𝓝 (0 : (Fin k → ℝ) × ℝ)) := by
      simpa only [hei0] using hia.continuousAt.tendsto
    have htar : (0 : (Fin k → ℝ) × ℝ) ∈ e.target := he0 ▸ e.map_source hem
    filter_upwards [e.open_target.mem_nhds htar,hsnd,ht hΩ] with q hq hqs hqi
    intro hu
    have hr : realPart k (G (e.symm q)) = q.1 := by
      have hh := congrArg Prod.fst (e.right_inv hq)
      simpa only [he] using hh
    have hEq : (fun i => (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)) = G (e.symm q) := by
      ext i
      have hi := congrFun hr i
      change (G (e.symm q) i).re = q.1 i at hi
      dsimp [f]
      rw [hP]
      change (q.1 i : ℂ)+Complex.I*((G (e.symm q) i).im : ℂ) = _
      rw [← hi,mul_comm,Complex.re_add_im]
    rw [hEq]
    exact hqi (by rwa [hqs])

end Release061.Flatten

end

end OAI
