import OAI.MeasureTheory.Falconer.Radial.RadialScaleIntersection

namespace OAI

/-! # Removing the diagonal from an actual radial pair set -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_remove_diagonal (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G) {r : ℝ} (hr : 0 ≤ r)
    (C : ℝ≥0∞)
    (hcap : ∀ x w : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (∀ x : Space d, (x,x) ∉ H) ∧ (μ.prod μ) Hᶜ ≤ (μ.prod μ) Gᶜ+C := by
  let D : Set (Space d × Space d) := {p | p.1 = p.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  have hbound : (μ.prod μ) (G ∩ D) ≤ C := by
    rw [Measure.prod_apply (hG.inter hD)]
    calc
      _ ≤ ∫⁻ _x, C ∂μ := lintegral_mono (fun x => by
        apply (measure_mono ?_).trans (hcap x 0)
        rintro z ⟨hz,hz'⟩
        have hxz : x = z := hz'
        refine ⟨hz,?_⟩
        rw [← hxz,sub_self,normalize_zero_eq_zero,sub_self,norm_zero]
        exact hr)
      _ = C := by simp
  refine ⟨G \ D,hG.diff hD,sdiff_subset,?_,?_⟩
  · intro x hx
    exact hx.2 rfl
  · have hs : (G \ D)ᶜ ⊆ Gᶜ ∪ (G ∩ D) := by
      intro p hp
      by_cases hg : p ∈ G
      · exact Or.inr ⟨hg,by simpa only [mem_compl_iff,mem_sdiff,hg,true_and,not_not] using hp⟩
      · exact Or.inl hg
    exact (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbound))

end Falconer

end OAI
