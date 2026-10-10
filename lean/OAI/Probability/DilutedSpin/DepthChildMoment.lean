import OAI.Probability.DilutedSpin.SpatialScheduledContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance depthChildMomentDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {L : ℕ} [NeZero L]

lemma average_nonneg (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) : 0≤average D F := by
  apply FiniteLaw.expect_nonneg
  intro q
  split_ifs
  · exact hF q
  · exact le_rfl

lemma average_mono (D : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ)
    (h : ∀ q, D q → F q≤G q) : average D F≤average D G := by
  apply FiniteLaw.expect_mono
  intro q
  split_ifs with hd
  · exact h q hd
  · exact le_rfl

lemma average_const_mul (D : (α → Fin L) → Prop) (c : ℝ) (F : (α → Fin L) → ℝ) :
    average D (fun q => c*F q)= c*average D F := by
  unfold average
  rw [← FiniteLaw.expect_mul_left]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

lemma average_sqrt_le (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) : average D (fun q => Real.sqrt (F q))≤Real.sqrt (average D F) := by
  have h := FiniteLaw.expect_sqrt_le (depthLaw α L) (fun q => if D q then F q else 0)
    (fun q => by split_ifs; exact hF q; exact le_rfl)
  have he : (fun q => Real.sqrt (if D q then F q else 0)) =
      (fun q => if D q then Real.sqrt (F q) else 0) := by
    funext q
    split_ifs <;> simp
  rw [he] at h
  exact h

lemma fiber_sqrt_bound (e : β → α) (he : Function.Injective e)
    (τ : β → Equiv.Perm (Fin L)) (D : (α → Fin L) → Prop) (E : (β → Fin L) → Prop)
    (hDE : ∀ q, D q → E (coordinateProjection e τ q)) (F : (β → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) :
    average D (fun q => Real.sqrt (F (coordinateProjection e τ q)))≤
      Real.sqrt (average E F) :=
  (fiber_bound e he τ D E hDE (fun q => Real.sqrt (F q)) (fun _ => Real.sqrt_nonneg _)).trans
    (average_sqrt_le E F hF)

/-- The exact nested square roots occurring in the physical root multileaf
estimate pass through the normalized depth fibers. Every child uses its own
retained coordinates; unused coordinates have mass one. -/
theorem fiber_child_moment_bound {ι : Type} [Fintype ι]
    {β : ι → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    (c : ℝ) (hc : 0≤c) (e : (j : ι) → β j → α) (he : ∀ j, Function.Injective (e j))
    (τ : (j : ι) → β j → Equiv.Perm (Fin L))
    (D : (α → Fin L) → Prop) (E : (j : ι) → (β j → Fin L) → Prop)
    (hDE : ∀ j q, D q → E j (coordinateProjection (e j) (τ j) q))
    (F : (j : ι) → (β j → Fin L) → ℝ) (hF : ∀ j q, 0≤F j q) :
    average D (fun q => Real.sqrt (c*∑ j, Real.sqrt (F j (coordinateProjection (e j) (τ j) q)))) ≤
      Real.sqrt (c*∑ j, Real.sqrt (average (E j) (F j))) := by
  apply (average_sqrt_le D _ (fun q => mul_nonneg hc
    (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)))).trans
  apply Real.sqrt_le_sqrt
  rw [average_const_mul,average_sum]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Finset.sum_le_sum
  intro j _
  exact fiber_sqrt_bound (e j) (he j) (τ j) D (E j) (hDE j) (F j) (hF j)

end DilutedSpinGlass.DepthAverage
end

end

end OAI
