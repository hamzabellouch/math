import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.Dual

namespace OAI

namespace MetricKMedianRecovery.PhaseOriginalLedger
universe u v w
variable {A : Type u} {B : Type v} {X : Type w} [Fintype A] [Fintype B]
    [PseudoMetricSpace X]
lemma Dual.reindex (e : B ≃ A) (loc : A→X) (F : Finset X) (v lam : ℝ) (alpha : A→ℝ)
    (h : Dual loc F v lam alpha) : Dual (loc ∘ e) F v lam (alpha ∘ e) := by
  classical
  refine ⟨fun j=>h.1 (e j),?_,?_⟩
  · intro i hi
    have he := Equiv.sum_comp e (fun j=>max (alpha j-2*dist i (loc j)) 0)
    simpa only [Function.comp_apply,he] using h.2.1 i hi
  · intro C hC i hi b hb hp hl hs
    have hd : (∑ j∈C.image e,dist i (loc j))=∑ j∈C,dist i ((loc ∘ e) j) := by
      rw [Finset.sum_image]
      · rfl
      · exact fun _ _ _ _ hh=>e.injective hh
    have ha : (∑ j∈C.image e,alpha j)=∑ j∈C,(alpha ∘ e) j := by
      rw [Finset.sum_image]
      · rfl
      · exact fun _ _ _ _ hh=>e.injective hh
    simpa only [hd,ha] using h.2.2 (C.image e) (hC.image e) i hi b hb (hd ▸ hp) (hd ▸ hl) hs
end MetricKMedianRecovery.PhaseOriginalLedger

end OAI
