import OAI.Geometry.NodalSets.Elliptic.RealCompactH1Approximation
import OAI.Geometry.NodalSets.Elliptic.RealTranslatedJetEmbedding
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetPairings

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Metric
open scoped ContDiff
noncomputable section

theorem real_global_jet_l2_embedding (W : Yau.Jets.Coord → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (n : ℕ)
    (E : List (Fin 4) → ℝ)
    (hb : ∀ es, es.length ≤ n+4 → (∫ x, (partialJet W es x)^2) ≤ E es)
    (ds : List (Fin 4)) (hd : ds.length ≤ n) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤
      256 * ∑ r ∈ Finset.range (n+5), ∑ w : Fin r → Fin 4, E (List.ofFn w) := by
  have hi (es : List (Fin 4)) : Integrable (fun x ↦ (partialJet W es x)^2) :=
    (Yau.real_compact_continuous_memLp _ (partialJet_smooth W hW es).continuous
      (partialJet_compactSupport W hc es)).integrable_sq
  have hf : Integrable (realFiniteJetSquare W (n+4)) :=
    integrable_finsetSum _ (fun r _ ↦ integrable_finsetSum _ (fun w _ ↦ hi (List.ofFn w)))
  have h := real_uniform_jet_l2_embedding W hW n x 0 ds hd x (by simp)
  have hm := integral_mono_measure (Measure.restrict_le_self :
      volume.restrict (closedBall x (0+1)) ≤ volume)
    (Filter.Eventually.of_forall (realFiniteJetSquare_nonneg W (n+4))) hf
  have hs : (∫ z, realFiniteJetSquare W (n+4) z) ≤
      ∑ r ∈ Finset.range (n+5), ∑ w : Fin r → Fin 4, E (List.ofFn w) := by
    unfold realFiniteJetSquare
    rw [integral_finsetSum _ (fun r _ ↦ integrable_finsetSum _ (fun w _ ↦ hi (List.ofFn w)))]
    apply Finset.sum_le_sum
    intro r hr
    rw [integral_finsetSum _ (fun w _ ↦ hi (List.ofFn w))]
    apply Finset.sum_le_sum
    intro w _
    apply hb
    simp only [List.length_ofFn]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  exact h.trans (mul_le_mul_of_nonneg_left (hm.trans hs) (by norm_num))

end
end Yau.Geometry

end OAI
