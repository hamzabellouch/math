import OAI.NumberTheory.JointDickman.Analysis.SquarefreeContourSeries
import OAI.NumberTheory.JointDickman.Analysis.PrimeZetaPoleLog
import OAI.NumberTheory.JointDickman.Analysis.ZetaRectangleLog
import OAI.NumberTheory.JointDickman.Analysis.AnalyticLogUniqueness

namespace OAI

/-! # Agreement of the continuation with the original squarefree series -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem squarefreeContourSeries_eq_LSeries_on_right {z δ T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T)) (hf1 : f 1 = 0)
    (he : ∀ s ∈ zetaOpenRectangle δ T, Complex.exp (f s) = zetaPoleFactor s) :
    ∀ s ∈ zetaOpenRectangle 0 T,
      squarefreeContourSeries z f s = LSeries (fun n => (squarefreeWeight z n:ℂ)) s := by
  have h1 := zetaOpenRectangle_one hδ hT
  have hlocal := normalized_log_eq_principal_near (hf 1 h1).continuousAt hf1
    (Filter.eventuallyEq_of_mem ((zetaOpenRectangle_isOpen δ T).mem_nhds h1) he)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  let d := min ε 1 / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d < ε := by dsimp [d]; have := min_le_left ε 1; linarith
  have hd1 : d < 1 := by dsimp [d]; have := min_le_right ε 1; linarith
  have hw : ((1+d:ℝ):ℂ) ∈ zetaOpenRectangle 0 T := by
    change (1+d ∈ Ioo (1-0) 2) ∧ (0:ℝ) ∈ Ioo (-T) T
    constructor <;> constructor <;> linarith
  have hsub : zetaOpenRectangle 0 T ⊆ zetaOpenRectangle δ T := by
    intro s hs
    exact ⟨⟨by have := hs.1.1; linarith,hs.1.2⟩,hs.2⟩
  have hbase : f ((1+d:ℝ):ℂ) = primeZetaPoleLog ((1+d:ℝ):ℂ) := by
    rw [primeZetaPoleLog_real (by linarith : 1 < 1+d)]
    apply hball
    rw [dist_eq_norm]
    have heq : (((1+d:ℝ):ℂ)-1) = (d:ℂ) := by push_cast; ring
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    exact hdε
  let : ContractibleSpace (zetaOpenRectangle 0 T) :=
    (zetaOpenRectangle_convex 0 T).contractibleSpace ⟨_,hw⟩
  have hsim : IsSimplyConnected (zetaOpenRectangle 0 T) := by
    change SimplyConnectedSpace _
    infer_instance
  have hg : AnalyticOnNhd ℂ primeZetaPoleLog (zetaOpenRectangle 0 T) := by
    intro s hs
    exact primeZetaPoleLog_analyticAt (by simpa only [sub_zero] using hs.1.1)
  have hsame := analytic_log_unique (zetaOpenRectangle_isOpen 0 T)
    hsim.isPathConnected.isConnected.isPreconnected (hf.mono hsub) hg
    (fun s hs => (he s (hsub hs)).trans (primeZetaPoleLog_exp
      (by simpa only [sub_zero] using hs.1.1)).symm) hw hbase
  intro s hs
  rw [squarefreeContourSeries,hsame hs,primeZetaPoleLog,add_sub_cancel_right]
  exact (squarefreeDirichletSeries_factorization hz hz1
    (by simpa only [sub_zero] using hs.1.1)).symm

end JointDickman

end OAI
