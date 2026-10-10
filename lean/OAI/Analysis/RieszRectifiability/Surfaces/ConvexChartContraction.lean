import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Topology

theorem exists_contraction_in_convex_chart {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace V]
    (C : Set E) (hC : Convex ℝ C) (H : C → V) (hH : IsEmbedding H)
    (A : Set V) (hA : A ⊆ Set.range H) (p : V) (hp : p ∈ A) :
    ∃ F : unitInterval × A → V, Continuous F ∧
      (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, hp⟩) = p) ∧ (∀ w, F w ∈ Set.range H) := by
  classical
  have hpre : ∀ x : A, ∃ u : C, H u = x.val := fun x => hA x.property
  choose j hj using hpre
  have hjcont : Continuous j := hH.continuous_iff.mpr (by
    have hid : H ∘ j = (Subtype.val : A → V) := funext hj
    rw [hid]
    exact continuous_subtype_val)
  let u0 : C := j ⟨p, hp⟩
  let T : unitInterval × A → C := fun w =>
    ⟨(1 - (w.1 : ℝ)) • (j w.2 : E) + (w.1 : ℝ) • (u0 : E),
      hC (j w.2).property u0.property (sub_nonneg.mpr w.1.property.2)
        w.1.property.1 (by ring)⟩
  have hs : Continuous (fun w : unitInterval × A => (w.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hjv : Continuous (fun w : unitInterval × A => (j w.2 : E)) :=
    continuous_subtype_val.comp (hjcont.comp continuous_snd)
  have hT : Continuous T :=
    (((continuous_const.sub hs).smul hjv).add (hs.smul continuous_const)).subtype_mk _
  let F := H ∘ T
  refine ⟨F, hH.continuous.comp hT, ?_, ?_, ?_, ?_⟩
  · intro x
    have ht : T (0, x) = j x := by apply Subtype.ext; simp [T]
    change H (T (0, x)) = x.val
    rw [ht]
    exact hj x
  · intro x
    have ht : T (1, x) = u0 := by apply Subtype.ext; simp [T]
    change H (T (1, x)) = p
    rw [ht]
    exact hj ⟨p, hp⟩
  · intro s
    have ht : T (s, ⟨p, hp⟩) = u0 := by
      apply Subtype.ext
      change (1 - (s : ℝ)) • (u0 : E) + (s : ℝ) • (u0 : E) = (u0 : E)
      rw [← add_smul]
      simp
    change H (T (s, ⟨p, hp⟩)) = p
    rw [ht]
    exact hj ⟨p, hp⟩
  · intro w
    exact ⟨T w, rfl⟩

end

end RieszRectifiability

end OAI
