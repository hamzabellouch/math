import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCornerChart

namespace OAI

/-! A small neighborhood of an interior point of an embedded compact path
avoids any prescribed compact exterior parameter intervals. -/
noncomputable section
open Set Filter unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] {p q : M}

lemma embeddedPath_extend_injOn (γ : Path p q) (hi : Function.Injective γ) :
    InjOn γ.extend (Icc (0:ℝ) 1) := by
  intro u hu v hv he
  rw [Path.extend_apply γ hu,Path.extend_apply γ hv] at he
  exact congrArg (fun z : I => (z:ℝ)) (hi he)

variable [T2Space M]

theorem embedded_path_corner_neighborhood (γ : Path p q) (hi : Function.Injective γ)
    {a t b : ℝ} (ha : 0 ≤ a) (hat : a < t) (htb : t < b) (hb : b ≤ 1)
    {O : Set M} (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ V : Set M, IsOpen V ∧ γ.extend t ∈ V ∧ V ⊆ O ∧
      ∀ u ∈ Icc (0:ℝ) a ∪ Icc b 1, γ.extend u ∉ V := by
  let K := γ.extend '' (Icc (0:ℝ) a ∪ Icc b 1)
  have hK : IsCompact K := (isCompact_Icc.union isCompact_Icc).image γ.continuous_extend
  have htK : γ.extend t ∉ K := by
    rintro ⟨u,hu,he⟩
    have ht01 : t ∈ Icc (0:ℝ) 1 := ⟨ha.trans hat.le,htb.le.trans hb⟩
    have hu01 : u ∈ Icc (0:ℝ) 1 := by
      rcases hu with hu | hu
      · exact ⟨hu.1,hu.2.trans (hat.le.trans ht01.2)⟩
      · exact ⟨(ht01.1.trans htb.le).trans hu.1,hu.2⟩
    have heu := embeddedPath_extend_injOn γ hi hu01 ht01 he
    subst u
    rcases hu with hu | hu
    · exact (not_le_of_gt hat) hu.2
    · exact (not_le_of_gt htb) hu.1
  refine ⟨O \ K,hO.sdiff hK.isClosed,⟨htO,htK⟩,sdiff_subset,?_⟩
  intro u hu hv
  exact hv.2 ⟨u,hu,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
