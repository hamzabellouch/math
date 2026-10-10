import Mathlib
import OAI.Probability.SKGap.Matrix.LogDetExpected

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_logdet_mean {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
        (∫ g, LogDet.regularizedLogDet γ (logPath ((j/(n:ℝ))*∑ i,a i) a
          (goeMatrix (j/(n:ℝ)) g) 1)
          ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)) ≤
          j*((∑ i,a i)/(n:ℝ))^2+γ*B^2+C/(n:ℝ) := by
  have hs : sqrt j*1 < 1 := by nlinarith [sq_sqrt hj.le,sqrt_nonneg j]
  obtain ⟨f,R,hR,lo,hi,C,N,hReq,hloeq,hhieq,hlo,hf,_hfr,hC,hN,hbias⟩ :=
    actual_projected_path_equivalents hj (by norm_num : (0:ℝ)<1) hs
  have hB := (path_constants_nonneg f hR hj.le (by norm_num : (0:ℝ)≤1)).1
  refine ⟨pathBound f R j 1,hB,?_⟩
  intro γ hγ
  have hr := pathRate_pos hj (by norm_num : (0:ℝ)<1) hs
  refine ⟨logdetMeanError j R (pathBound f R j 1) C (pathRate j 1) γ,
    logdetMeanError_nonneg hj.le hR hB hC.le hr hγ,?_⟩
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (path_size_eventually hs)
  refine ⟨max N N₁,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n hn a ha ha1
  have hnN := (le_max_left N N₁).trans hn
  have hn0 := hN.trans_le hnN
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hb (z) (hz : z ∈ Icc (0:ℝ) 1) := hbias n hnN a ha ha1 z hz
  have hp := logPathGood_exponential hj (by norm_num : (0:ℝ)<1) ha ha1 hs
    (by simpa only [Fintype.card_fin] using hN₁ n ((le_max_right N N₁).trans hn))
  rw [← hReq,← hloeq,← hhieq] at hp
  simpa only [Fintype.card_fin] using
    logPath_regularized_expected f hR hlo hf hj.le hC.le hγ hr ha ha1
      (fun z hz i => by simpa only [Fintype.card_fin] using (hb z hz i).1)
      (fun z hz i => by simpa only [Fintype.card_fin] using (hb z hz i).2) hp
end SKGap
end
end

end OAI
