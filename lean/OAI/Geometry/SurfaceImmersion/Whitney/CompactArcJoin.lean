import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcJoin

namespace OAI

/-! Joining compact parameterized arcs preserves their precise image and
injectivity when their only shared point is the common endpoint. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*}

theorem joinedCurve_compact_image (γ δ : ℝ → N) (e : ℝ ≃ₜ ℝ)
    (he : StrictMono e) {l a d : ℝ} (hla : l ≤ a) (had : e a < d)
    (hpoint : γ a = δ (e a)) :
    joinedCurve a γ (δ ∘ e) '' Icc l (e.symm d) =
      γ '' Icc l a ∪ δ '' Icc (e a) d := by
  have haw : a < e.symm d := by
    apply he.lt_iff_lt.mp
    simpa only [e.apply_symm_apply] using had
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    by_cases hta : t ≤ a
    · exact Or.inl ⟨t,⟨ht.1,hta⟩,by simp only [joinedCurve,ite_eq_left hta]⟩
    · refine Or.inr ⟨e t,⟨he.monotone (le_of_not_ge hta),?_⟩,?_⟩
      · simpa only [e.apply_symm_apply] using he.monotone ht.2
      · simp only [joinedCurve,ite_eq_right hta,Function.comp_apply]
  · rintro y (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · exact ⟨t,⟨ht.1,ht.2.trans haw.le⟩,by simp only [joinedCurve,ite_eq_left ht.2]⟩
    · have hlow : a ≤ e.symm t := by
        apply he.le_iff_le.mp
        simpa only [e.apply_symm_apply] using ht.1
      have hhigh : e.symm t ≤ e.symm d := (he.le_iff_le).mp (by simpa using ht.2)
      refine ⟨e.symm t,⟨hla.trans hlow,hhigh⟩,?_⟩
      by_cases hta : e.symm t ≤ a
      · have hta' : e.symm t = a := le_antisymm hta hlow
        have ht' : t = e a := by simpa only [e.apply_symm_apply] using congrArg e hta'
        rw [hta',ht']
        simpa only [joinedCurve,le_refl,ite_true] using hpoint
      · simp only [joinedCurve,ite_eq_right hta,Function.comp_apply,e.apply_symm_apply]

theorem joinedCurve_compact_injective (γ δ : ℝ → N) (e : ℝ ≃ₜ ℝ)
    (he : StrictMono e) {l a d : ℝ}
    (hγ : (Icc l a).InjOn γ) (hδ : (Icc (e a) d).InjOn δ)
    (hcross : ∀ s ∈ Icc l a, ∀ t ∈ Ioc (e a) d, γ s ≠ δ t) :
    (Icc l (e.symm d)).InjOn (joinedCurve a γ (δ ∘ e)) := by
  apply joinedCurve_injective_on
  · intro x hx y hy hxy
    exact hγ ⟨hx.1.1,hx.2⟩ ⟨hy.1.1,hy.2⟩ hxy
  · intro x hx y hy hxy
    apply e.injective
    apply hδ _ _ hxy
    · exact ⟨(he hx.2).le,by simpa only [e.apply_symm_apply] using he.monotone hx.1.2⟩
    · exact ⟨(he hy.2).le,by simpa only [e.apply_symm_apply] using he.monotone hy.1.2⟩
  · intro x hx hxa y hy hay
    exact hcross x ⟨hx.1,hxa⟩ (e y)
      ⟨he hay,by simpa only [e.apply_symm_apply] using he.monotone hy.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
