import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.ConvexChartContraction

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Topology
open scoped NNReal

theorem exists_bounded_contraction_in_bilipschitz_convex_chart {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace V]
    (C : Set E) (hC : Convex ℝ C) (H : C → V) (K L : ℝ≥0)
    (hLip : LipschitzWith K H) (hsep : AntilipschitzWith L H)
    (A : Set V) (hA : A ⊆ Set.range H) (p : V) (hp : p ∈ A)
    (r : ℝ) (hball : A ⊆ closedBall p r) :
    ∃ F : unitInterval × A → V, Continuous F ∧
      (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, hp⟩) = p) ∧
      (∀ w, F w ∈ Set.range H ∩ closedBall p ((K : ℝ) * (L : ℝ) * r)) := by
  classical
  have hH : IsEmbedding H := hsep.isEmbedding hLip.continuous
  have hpre : ∀ x : A, ∃ u : C, H u = x.val := fun x => hA x.property
  choose j hj using hpre
  have hjcont : Continuous j := hH.continuous_iff.mpr (by
    have hid : H ∘ j = (Subtype.val : A → V) := funext hj
    rw [hid]
    exact continuous_subtype_val)
  let u0 : C := j ⟨p, hp⟩
  have hH0 : H u0 = p := hj ⟨p, hp⟩
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
  refine ⟨F, hLip.continuous.comp hT, ?_, ?_, ?_, ?_⟩
  · intro x
    have ht : T (0, x) = j x := by apply Subtype.ext; simp [T]
    change H (T (0, x)) = x.val
    rw [ht]
    exact hj x
  · intro x
    have ht : T (1, x) = u0 := by apply Subtype.ext; simp [T]
    change H (T (1, x)) = p
    rw [ht]
    exact hH0
  · intro s
    have ht : T (s, ⟨p, hp⟩) = u0 := by
      apply Subtype.ext
      change (1 - (s : ℝ)) • (u0 : E) + (s : ℝ) • (u0 : E) = (u0 : E)
      rw [← add_smul]
      simp
    change H (T (s, ⟨p, hp⟩)) = p
    rw [ht]
    exact hH0
  · intro w
    refine ⟨⟨T w, rfl⟩, ?_⟩
    have hseg : dist (T w) u0 ≤ dist (j w.2) u0 := by
      calc
        dist (T w) u0 = (1 - (w.1 : ℝ)) * dist (j w.2) u0 := by
          simp only [Subtype.dist_eq, dist_eq_norm]
          change ‖((1 - (w.1 : ℝ)) • (j w.2 : E) + (w.1 : ℝ) • (u0 : E)) - (u0 : E)‖ =
            (1 - (w.1 : ℝ)) * ‖(j w.2 : E) - (u0 : E)‖
          rw [show ((1 - (w.1 : ℝ)) • (j w.2 : E) + (w.1 : ℝ) • (u0 : E)) - (u0 : E) =
            (1 - (w.1 : ℝ)) • ((j w.2 : E) - (u0 : E)) by module]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr w.1.property.2)]
        _ ≤ dist (j w.2) u0 := mul_le_of_le_one_left dist_nonneg (by linarith [w.1.property.1])
    have hjdist : dist (j w.2) u0 ≤ (L : ℝ) * r := by
      have h := hsep.le_mul_dist (j w.2) u0
      rw [hj w.2, hH0] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hball w.2.property) L.coe_nonneg)
    change dist (H (T w)) p ≤ (K : ℝ) * (L : ℝ) * r
    rw [← hH0]
    calc
      dist (H (T w)) (H u0) ≤ (K : ℝ) * dist (T w) u0 := hLip.dist_le_mul _ _
      _ ≤ (K : ℝ) * ((L : ℝ) * r) :=
        mul_le_mul_of_nonneg_left (hseg.trans hjdist) K.coe_nonneg
      _ = (K : ℝ) * (L : ℝ) * r := by ring

end

end RieszRectifiability

end OAI
