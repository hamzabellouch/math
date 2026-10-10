import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialParameterSubsequence

namespace OAI

/-! Extend an indexed family without changing its values on increasing powers. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def radialIndexedExtension {E : Type*} (s : ℕ → ℕ)
    (v w : ℕ → E) (n : ℕ) : E := by
  classical
  exact if h : ∃ i, s i=n then v (Classical.choose h) else w n

theorem radialIndexedExtension_apply {E : Type*} (s : ℕ → ℕ) (hs : StrictMono s)
    (v w : ℕ → E) (i : ℕ) : radialIndexedExtension s v w (s i)=v i := by
  classical
  rw [radialIndexedExtension,dite_eq_left (show ∃ k, s k=s i from ⟨i,rfl⟩)]
  congr 1
  exact hs.injective (Classical.choose_spec (show ∃ k, s k=s i from ⟨i,rfl⟩))

theorem radialIndexedExtension_constant_tendsto {E : Type*} [TopologicalSpace E]
    (s : ℕ → ℕ) (hs : StrictMono s) (v : ℕ → E) (w : E)
    (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (radialIndexedExtension s v (fun _ => w)) atTop (𝓝 w) := by
  classical
  intro U hU
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hv.eventually hU)
  apply eventually_atTop.mpr
  refine ⟨s K,fun n hn => ?_⟩
  by_cases he : ∃ i, s i=n
  · rw [radialIndexedExtension,dite_eq_left he]
    exact hK _ (hs.le_iff_le.mp (by rw [Classical.choose_spec he]; exact hn))
  · simpa only [radialIndexedExtension,dite_eq_right he] using mem_of_mem_nhds hU

end DefocusingNLS

end OAI
