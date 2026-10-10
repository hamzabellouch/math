import OAI.Analysis.LipschitzEquivalence.SmoothCalculus

namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped Topology BigOperators
open Filter Set
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_triangular_duals {u : ℕ → E} {φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ}
    (hφ : ∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)))
    {d : ℝ} (hd : 0 < d)
    (hfar : ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖) (N : ℕ) :
    ∃ (f : Fin N → E →L[ℝ] ℝ) (v : Fin N → ℕ),
      (∀ j, ‖f j‖ = 1 ∧ d/2 < φ (f j)) ∧
      (∀ i j, j ≤ i → d/4 < f j (u (v i))) ∧
      (∀ i j, i < j → f j (u (v i)) = 0) := by
  classical
  induction N with
  | zero => exact ⟨Fin.elim0,Fin.elim0,by simp,by simp,by simp⟩
  | succ N ih =>
    obtain ⟨f,v,hf,hhigh,hlow⟩ := ih
    obtain ⟨g,hgnorm,hgzero,hgφ⟩ := bidual_separate_finite φ hd hfar (fun i => u (v i))
    let F : Fin (N+1) → E →L[ℝ] ℝ := Fin.snoc f g
    have hF (j : Fin (N+1)) : ‖F j‖ = 1 ∧ d/2 < φ (F j) := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [F] using And.intro hgnorm hgφ
      · simpa [F] using hf i
    have hev (j : Fin (N+1)) : ∀ᶠ k in atTop, d/4 < F j (u k) :=
      (tendsto_order.1 (hφ (F j))).1 _ (by linarith [(hF j).2])
    have hall : ∀ᶠ k in atTop, ∀ j : Fin (N+1), d/4 < F j (u k) :=
      Filter.eventually_all.mpr hev
    obtain ⟨k,hk⟩ := hall.exists
    refine ⟨F,Fin.snoc v k,hF,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j _
        simpa using hk j
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h
          simp at h
        · intro h
          simpa [F] using hhigh i j (by simpa using h)
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j h
        exact False.elim (not_lt_of_ge (Fin.le_last j) h)
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _
          simpa [F] using hgzero i
        · intro h
          simpa [F] using hlow i j (by simpa using h)

end LipschitzCounterexample.WeakSequences
end

end OAI
