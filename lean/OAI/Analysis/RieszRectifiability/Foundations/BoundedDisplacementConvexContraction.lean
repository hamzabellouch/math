import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.ConvexChartContraction

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Topology
open scoped NNReal

theorem exists_bounded_displacement_convex_chart_contraction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Convex ℝ C) (H : C → E) (hH : IsEmbedding H)
    (δ : ℝ) (hdisp : ∀ u, dist (H u) (u : E) ≤ δ)
    (A : Set E) (hA : A ⊆ Set.range H) (p : E) (hp : p ∈ A)
    (r : ℝ) (hball : A ⊆ closedBall p r) :
    ∃ F : unitInterval × A → E, Continuous F ∧
      (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, hp⟩) = p) ∧
      (∀ w, F w ∈ Set.range H ∩ closedBall p (r + 4 * δ)) := by
  classical
  have hpre : ∀ x : A, ∃ u : C, H u = x.val := fun x => hA x.property
  choose j hj using hpre
  have hjcont : Continuous j := hH.continuous_iff.mpr (by
    have hid : H ∘ j = (Subtype.val : A → E) := funext hj
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
    have hjdist : dist (j w.2) u0 ≤ r + 2 * δ := by
      have h1 := dist_triangle (j w.2 : E) (H (j w.2)) (u0 : E)
      have h2 := dist_triangle (H (j w.2)) (H u0) (u0 : E)
      have hleft := hdisp (j w.2)
      have hright := hdisp u0
      rw [dist_comm (H (j w.2)) (j w.2 : E)] at hleft
      have hmid : dist (H (j w.2)) (H u0) ≤ r := by
        rw [hj w.2, hH0]
        exact hball w.2.property
      change dist (j w.2 : E) (u0 : E) ≤ r + 2 * δ
      linarith
    have h1 := dist_triangle (H (T w)) (T w : E) p
    have h2 := dist_triangle (T w : E) (u0 : E) p
    have hleft := hdisp (T w)
    have hright : dist (u0 : E) p ≤ δ := by
      rw [← hH0, dist_comm]
      exact hdisp u0
    change dist (H (T w)) p ≤ r + 4 * δ
    change dist (T w : E) (u0 : E) ≤ dist (j w.2 : E) (u0 : E) at hseg
    change dist (j w.2 : E) (u0 : E) ≤ r + 2 * δ at hjdist
    linarith

end

end RieszRectifiability

end OAI
