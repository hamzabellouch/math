import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance

namespace OAI

/-! # Removing zero-weight states preserves finite weighted variance -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- An injective encoding may omit only states of weight zero. -/
theorem sum_support_embedding (e : X → Y) (he : Function.Injective e)
    (w : Y → ℝ) (hw : ∀ y ∉ Set.range e,w y=0) (H : Y → ℝ) :
    (∑ x,w (e x)*H (e x))=∑ y,w y*H y := by
  apply Fintype.sum_of_injective e he _ _
  · intro y hy
    rw [hw y hy,zero_mul]
  · intro x
    rfl

theorem mean_support_embedding (e : X → Y) (he : Function.Injective e)
    (w : Y → ℝ) (hw : ∀ y ∉ Set.range e,w y=0) (H : Y → ℝ) :
    mean (fun x => w (e x)) (fun x => H (e x))=mean w H := by
  have hm : (∑ x,w (e x))=∑ y,w y :=
    Fintype.sum_of_injective e he _ _ hw (fun _ => rfl)
  unfold mean
  rw [sum_support_embedding e he w hw H,hm]

theorem variance_support_embedding (e : X → Y) (he : Function.Injective e)
    (w : Y → ℝ) (hw : ∀ y ∉ Set.range e,w y=0) (H : Y → ℝ) :
    variance (fun x => w (e x)) (fun x => H (e x))=variance w H := by
  unfold variance
  rw [mean_support_embedding e he w hw H]
  exact sum_support_embedding e he w hw (fun y => (H y-mean w H)^2)

omit [Fintype Y] in
/-- In particular, restriction to the strictly positive support does not
change any weighted variance, including the empty-support case. -/
theorem variance_positive_support (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) :
    variance (fun x : {x // 0 < w x} => w x.val)
      (fun x => H x.val)=variance w H := by
  apply variance_support_embedding Subtype.val Subtype.val_injective w
  intro x hx
  have hn : ¬0 < w x := by
    intro hp
    exact hx ⟨⟨x,hp⟩,rfl⟩
  exact le_antisymm (le_of_not_gt hn) (hw x)

end ContingencyTables.FiniteExposureVariance

end OAI
