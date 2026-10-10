import OAI.Geometry.NodalSets.Elliptic.RealGlobalJetEmbedding

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_global_jet_common_bound (n : ℕ) :
    ∃ C > 0, ∀ W : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ W → HasCompactSupport W →
      ∀ E : ℝ, 0 ≤ E →
      (∀ es, es.length ≤ n+4 → (∫ x, (partialJet W es x)^2) ≤ E) →
      ∀ ds, ds.length ≤ n → ∀ x, (partialJet W ds x)^2 ≤ C*E := by
  let A : ℝ := ∑ r ∈ Finset.range (n+5), ∑ _w : Fin r → Fin 4, (1:ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ by norm_num))
  refine ⟨256*(A+1),mul_pos (by norm_num) (by linarith only [hA]),fun W hW hc E hE hb ds hd x ↦ ?_⟩
  have h := real_global_jet_l2_embedding W hW hc n (fun _ ↦ E) hb ds hd x
  have hs : (∑ r ∈ Finset.range (n+5), ∑ _w : Fin r → Fin 4, E)=A*E := by
    simp only [A,Finset.sum_mul,one_mul]
  rw [hs] at h
  nlinarith

end
end Yau.Geometry

end OAI
