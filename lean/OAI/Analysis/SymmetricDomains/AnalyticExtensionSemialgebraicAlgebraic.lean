import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticZeroRealPolydisc
import OAI.Analysis.SymmetricDomains.AnalyticNashRank
import OAI.Analysis.SymmetricDomains.AlgebraicGraphPolynomial

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
open Set Filter Metric Topology

theorem analytic_germ_zero_of_real_slice {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hz : (fun x : Fin n → ℝ => f (fun i => (x i : ℂ))) =ᶠ[𝓝 0] 0) :
    f =ᶠ[𝓝 0] 0 := by
  obtain ⟨r,hr,hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨s,hs,hzs⟩ := Metric.mem_nhds_iff.mp hz
  have hm : 0 < min r s := lt_min hr hs
  have hzero := analytic_zero_of_real_polydisc hm
    (hfr.mono (Metric.ball_subset_ball (min_le_left r s))) (fun x hx => by
      apply hzs
      simpa only [mem_ball,dist_zero_right] using hx.trans_le (min_le_right r s))
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hm] with x hx
  exact hzero hx

theorem analytic_extension_of_semialgebraic_isAlgebraic {n : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (f : (Fin n → ℝ) → ℝ) (F : (Fin n → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F 0)
    (hext : (fun x : Fin n → ℝ => F (fun i => (x i : ℂ))) =ᶠ[𝓝 0] fun x => (f x : ℂ))
    (hgraph : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
      (meromorphicGermOf F hF) := by
  obtain ⟨P,hP,hzero⟩ := semialgebraic_graph_polynomial B f hgraph
  let Q : MvPolynomial (Option (Fin n)) ℂ := P.map Complex.ofRealHom
  have hQ : Q ≠ 0 := by
    exact (map_ne_zero_iff (MvPolynomial.map Complex.ofRealHom)
      (MvPolynomial.map_injective _ Complex.ofReal_injective)).mpr hP
  let g : Option (Fin n) → (Fin n → ℂ) → ℂ := fun a z => a.elim (F z) z
  have hg : ∀ a, AnalyticAt ℂ (g a) 0 := by
    intro a
    cases a with
    | none => exact hF
    | some i => exact (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _
  have hqA : AnalyticAt ℂ (fun z => MvPolynomial.eval (fun a => g a z) Q) 0 :=
    ((AnalyticOnNhd.eval_mvPolynomial Q) _ (mem_univ _)).comp
      (analyticAt_pi_iff.mpr hg)
  have hqzero : (fun z => MvPolynomial.eval (fun a => g a z) Q) =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 := by
    apply analytic_germ_zero_of_real_slice hqA
    filter_upwards [hB,hext] with x hx hex
    change MvPolynomial.eval (fun a => a.elim (F (fun i => (x i : ℂ))) (fun i => (x i : ℂ))) Q = 0
    rw [hex]
    have heq : (fun a : Option (Fin n) => a.elim (f x : ℂ) (fun i => (x i : ℂ))) =
        Complex.ofRealHom ∘ (fun a : Option (Fin n) => a.elim (f x) x) := by
      funext a
      cases a <;> rfl
    rw [heq,MvPolynomial.eval_map,← MvPolynomial.eval₂_comp,hzero x hx]
    rfl
  have hgerm := (meromorphicGerm_aeval_eq_zero_iff g hg Q).mpr hqzero
  have hval : (fun a => meromorphicGermOf (g a) (hg a)) =
      fun a : Option (Fin n) => a.elim (meromorphicGermOf F hF) meromorphicCoordinate := by
    funext a
    cases a <;> rfl
  rw [hval] at hgerm
  exact algebraic_of_graph_polynomial meromorphicCoordinate algebraicIndependent_meromorphicCoordinate
    (meromorphicGermOf F hF) Q hQ hgerm

end Release061

end

end OAI
